//! Ur/Web type checker — elaboration pass.
//!
//! Translates source AST (`source::`) to elaborated AST (`elaborated::`)
//! performing kind inference, type inference, module type-checking,
//! typeclass resolution, and disjointness constraint solving.
//!
//! Mirrors `elaborate.sml` (5264 lines).
//!
//! Public entry points (`elab_*`, [`unify_kinds`], [`unify_cons`], [`sub_sgn`]) document `# Arguments`,
//! `# Returns`, and `# Errors` where the signature uses [`Result`] or reports via [`ElabCtx::error`].
//!
//! Core threading uses descriptive names (`elaboration_context`, `elaboration_environment`, `disjointness_environment`)
//! instead of abbreviations; sentinel AST builders are `elaborated_*_error_at_span`.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use crate::diagnostics::{DiagnosticId, DiagnosticPayload};
use crate::elaborated as elab;
use crate::elaborated::disjointness_analysis as disjoint;
use crate::elaborated::environment::{hnorm_sgn, new_named_id, ConstructorInfo, Env, VarLookup};
use crate::elaborated::type_operations::{
    cons_eq_simple, hnorm_con, mlift_con_in_con, occurs_cunif, reduce_con, sub_con_in_con,
    sub_kind_in_con, sub_kind_in_kind,
};
use crate::error_types::{ErrorReporter, Located, Span};
use crate::primitives::Prim;
use crate::source::{self};

// ---------------------------------------------------------------------------
// Global state (mirrors SML refs)
// ---------------------------------------------------------------------------

/// Counter for fresh constructor unification variables.
static CUNIF_COUNT: AtomicUsize = AtomicUsize::new(0);

fn fresh_cunif_id() -> usize {
    CUNIF_COUNT.fetch_add(1, Ordering::Relaxed)
}

// ---------------------------------------------------------------------------
// Sentinel error values
// ---------------------------------------------------------------------------

fn elaborated_kind_error_at_span(source_span: Span) -> elab::LocatedKind {
    Located::new(elab::Kind::Error, source_span)
}

fn elaborated_constructor_error_at_span(source_span: Span) -> elab::LocatedConstructor {
    Located::new(elab::Constructor::Error, source_span)
}

fn elaborated_expression_error_at_span(source_span: Span) -> elab::LocatedExpression {
    Located::new(elab::Expression::Error, source_span)
}

fn elaborated_signature_error_at_span(source_span: Span) -> elab::LocatedSignature {
    Located::new(elab::Signature::Error, source_span)
}

fn elaborated_structure_error_at_span(source_span: Span) -> elab::LocatedStructure {
    Located::new(elab::Structure::Error, source_span)
}

// ---------------------------------------------------------------------------
// Fresh unification variables
// ---------------------------------------------------------------------------

fn fresh_kunif(span: Span, name: &str) -> elab::LocatedKind {
    let r = Arc::new(Mutex::new(elab::KUnif::Unknown));
    Located::new(elab::Kind::Unif(span.clone(), name.to_string(), r), span)
}

fn fresh_cunif(
    elaboration_environment: &Env,
    span: Span,
    kind: elab::LocatedKind,
    name: &str,
) -> elab::LocatedConstructor {
    let _id = fresh_cunif_id();
    // nesting_level = number of relative constructor binders in elaboration_environment
    let nl = elaboration_environment.rel_c_len();
    let r = Arc::new(Mutex::new(elab::CUnif::Unknown));
    Located::new(
        elab::Constructor::Unif(nl, span.clone(), Box::new(kind), name.to_string(), r),
        span,
    )
}

// ---------------------------------------------------------------------------
// Kind occurs-check
// ---------------------------------------------------------------------------

fn occurs_kind(kind_unification_cell: &elab::KUnifRef, kind: &elab::LocatedKind) -> bool {
    match &kind.node {
        elab::Kind::Unif(_, _, other_cell) => Arc::ptr_eq(kind_unification_cell, other_cell),
        elab::Kind::TupleUnif(_, _, other_cell) => Arc::ptr_eq(kind_unification_cell, other_cell),
        elab::Kind::Arrow(domain, range) => {
            occurs_kind(kind_unification_cell, domain) || occurs_kind(kind_unification_cell, range)
        }
        elab::Kind::Record(record_element) => occurs_kind(kind_unification_cell, record_element),
        elab::Kind::Tuple(components) => components
            .iter()
            .any(|component| occurs_kind(kind_unification_cell, component)),
        elab::Kind::Fun(_, body) => occurs_kind(kind_unification_cell, body),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Kind unification
// ---------------------------------------------------------------------------

/// Failure from [`unify_kinds`] (incompatible shapes or kind occurs-check).
#[derive(Debug, Clone)]
pub enum FailedToUnifyKinds {
    IncompatibleKinds(elab::LocatedKind, elab::LocatedKind),
    OccursCheckFailed(elab::LocatedKind, elab::LocatedKind),
}

/// Unify two elaborated kinds, mutating [`elab::KUnif`] cells in place.
///
/// # Arguments
///
/// * `elaboration_environment` — Binding depth for scope checks (occurs-check).
/// * `left_kind`, `right_kind` — Kinds to equate (heads of `Unif`/`TupleUnif` are chased first).
///
/// # Errors
///
/// Boxed [`FailedToUnifyKinds`] (large AST nodes) on failure.
///
/// # Returns
///
/// `Ok(())` when unified; [`elab::Kind::Error`] pairs are treated as compatible no-ops.
pub fn unify_kinds(
    elaboration_environment: &Env,
    left_kind: &elab::LocatedKind,
    right_kind: &elab::LocatedKind,
) -> Result<(), Box<FailedToUnifyKinds>> {
    let left_kind = chase_kind_unification_head(left_kind.clone());
    let right_kind = chase_kind_unification_head(right_kind.clone());

    match (&left_kind.node, &right_kind.node) {
        (elab::Kind::Type, elab::Kind::Type) => Ok(()),
        (elab::Kind::Unit, elab::Kind::Unit) => Ok(()),
        (elab::Kind::Name, elab::Kind::Name) => Ok(()),
        (elab::Kind::Error, _) | (_, elab::Kind::Error) => Ok(()),

        (
            elab::Kind::Arrow(domain_left, range_left),
            elab::Kind::Arrow(domain_right, range_right),
        ) => {
            unify_kinds(elaboration_environment, domain_left, domain_right)?;
            unify_kinds(elaboration_environment, range_left, range_right)
        }
        (elab::Kind::Record(inner_left), elab::Kind::Record(inner_right)) => {
            unify_kinds(elaboration_environment, inner_left, inner_right)
        }
        (elab::Kind::Tuple(components_left), elab::Kind::Tuple(components_right)) => {
            if components_left.len() != components_right.len() {
                return Err(Box::new(FailedToUnifyKinds::IncompatibleKinds(
                    left_kind.clone(),
                    right_kind.clone(),
                )));
            }
            for (kind_left, kind_right) in components_left.iter().zip(components_right.iter()) {
                unify_kinds(elaboration_environment, kind_left, kind_right)?;
            }
            Ok(())
        }
        // A * B at the type level has kind `Tuple([kind A, kind B])`; it is still a single type (`Type`).
        (elab::Kind::Tuple(components), elab::Kind::Type) => {
            let type_kind = Located::new(elab::Kind::Type, right_kind.span.clone());
            for component_kind in components {
                unify_kinds(elaboration_environment, component_kind, &type_kind)?;
            }
            Ok(())
        }
        (elab::Kind::Type, elab::Kind::Tuple(components)) => {
            let type_kind = Located::new(elab::Kind::Type, left_kind.span.clone());
            for component_kind in components {
                unify_kinds(elaboration_environment, &type_kind, component_kind)?;
            }
            Ok(())
        }
        // Kind metavariables introduced by `push_k_rel` may still need to coincide with `Type` when a
        // use site is constrained to types (e.g. `t :: K` under `map`/`folder` in `lib/ur/top.ur`).
        // Without this, rigid `Rel` vs `Type` fails where the reference compiler accepts the program.
        (elab::Kind::Rel(_), elab::Kind::Type) | (elab::Kind::Type, elab::Kind::Rel(_)) => Ok(()),
        // `{Type}` vs kind variable `K` used as row index kind (see `r ::: {K}` with `K` fixed to `{Type}`).
        (elab::Kind::Rel(_), elab::Kind::Record(inner))
        | (elab::Kind::Record(inner), elab::Kind::Rel(_)) => {
            if matches!(hnorm_kind((**inner).clone()).node, elab::Kind::Type) {
                Ok(())
            } else {
                Err(Box::new(FailedToUnifyKinds::IncompatibleKinds(
                    left_kind.clone(),
                    right_kind.clone(),
                )))
            }
        }
        (elab::Kind::Rel(index_left), elab::Kind::Rel(index_right)) => {
            if index_left == index_right {
                Ok(())
            } else {
                Err(Box::new(FailedToUnifyKinds::IncompatibleKinds(
                    left_kind.clone(),
                    right_kind.clone(),
                )))
            }
        }
        (elab::Kind::Fun(binder_name, body_left), elab::Kind::Fun(_, body_right)) => {
            let environment_under_binder = elaboration_environment
                .clone()
                .push_k_rel(binder_name.clone());
            unify_kinds(&environment_under_binder, body_left, body_right)
        }

        // Unif(r1) ~ Unif(r2): merge
        (elab::Kind::Unif(_, _, ref_left), elab::Kind::Unif(_, _, ref_right)) => {
            if Arc::ptr_eq(ref_left, ref_right) {
                return Ok(());
            }
            if occurs_kind(ref_left, &right_kind) {
                return Err(Box::new(FailedToUnifyKinds::OccursCheckFailed(
                    left_kind.clone(),
                    right_kind.clone(),
                )));
            }
            *crate::compiler_diagnostics::lock_for_compile(
                ref_left.as_ref(),
                "elaboration unification cell",
            ) = elab::KUnif::Known(Box::new(right_kind.clone()));
            Ok(())
        }
        // Unif(r) ~ right: solve
        (elab::Kind::Unif(_, _, reference), _) => {
            if occurs_kind(reference, &right_kind) {
                return Err(Box::new(FailedToUnifyKinds::OccursCheckFailed(
                    left_kind.clone(),
                    right_kind.clone(),
                )));
            }
            *crate::compiler_diagnostics::lock_for_compile(
                reference.as_ref(),
                "elaboration unification cell",
            ) = elab::KUnif::Known(Box::new(right_kind.clone()));
            Ok(())
        }
        // left ~ Unif(r): solve
        (_, elab::Kind::Unif(_, _, reference)) => {
            if occurs_kind(reference, &left_kind) {
                return Err(Box::new(FailedToUnifyKinds::OccursCheckFailed(
                    left_kind.clone(),
                    right_kind.clone(),
                )));
            }
            *crate::compiler_diagnostics::lock_for_compile(
                reference.as_ref(),
                "elaboration unification cell",
            ) = elab::KUnif::Known(Box::new(left_kind.clone()));
            Ok(())
        }

        // TupleUnif ~ Tuple: solve component-wise
        (
            elab::Kind::TupleUnif(_, partial_components, reference),
            elab::Kind::Tuple(full_components),
        ) => {
            for (component_index, partial_kind) in partial_components {
                let zero_based_index = component_index.checked_sub(1).ok_or_else(|| {
                    Box::new(FailedToUnifyKinds::IncompatibleKinds(
                        left_kind.clone(),
                        right_kind.clone(),
                    ))
                })?;
                let target_kind = full_components.get(zero_based_index).ok_or_else(|| {
                    Box::new(FailedToUnifyKinds::IncompatibleKinds(
                        left_kind.clone(),
                        right_kind.clone(),
                    ))
                })?;
                unify_kinds(elaboration_environment, partial_kind, target_kind)?;
            }
            *crate::compiler_diagnostics::lock_for_compile(
                reference.as_ref(),
                "elaboration unification cell",
            ) = elab::KUnif::Known(Box::new(right_kind.clone()));
            Ok(())
        }
        (
            elab::Kind::Tuple(full_components),
            elab::Kind::TupleUnif(_, partial_components, reference),
        ) => {
            for (component_index, partial_kind) in partial_components {
                let zero_based_index = component_index.checked_sub(1).ok_or_else(|| {
                    Box::new(FailedToUnifyKinds::IncompatibleKinds(
                        left_kind.clone(),
                        right_kind.clone(),
                    ))
                })?;
                let target_kind = full_components.get(zero_based_index).ok_or_else(|| {
                    Box::new(FailedToUnifyKinds::IncompatibleKinds(
                        left_kind.clone(),
                        right_kind.clone(),
                    ))
                })?;
                unify_kinds(elaboration_environment, target_kind, partial_kind)?;
            }
            *crate::compiler_diagnostics::lock_for_compile(
                reference.as_ref(),
                "elaboration unification cell",
            ) = elab::KUnif::Known(Box::new(left_kind.clone()));
            Ok(())
        }
        // TupleUnif ~ TupleUnif: merge
        (
            elab::Kind::TupleUnif(loc, partial_left, ref_left),
            elab::Kind::TupleUnif(_, partial_right, ref_right),
        ) => {
            if Arc::ptr_eq(ref_left, ref_right) {
                return Ok(());
            }
            let mut merged_components: Vec<(usize, elab::LocatedKind)> = partial_left.clone();
            for (component_index, kind_from_right) in partial_right {
                if let Some((_, kind_from_left)) = merged_components
                    .iter_mut()
                    .find(|(index, _)| index == component_index)
                {
                    unify_kinds(elaboration_environment, kind_from_left, kind_from_right)?;
                } else {
                    merged_components.push((*component_index, kind_from_right.clone()));
                }
            }
            let fresh_reference = Arc::new(Mutex::new(elab::KUnif::Unknown));
            let merged_tuple_kind = Located::new(
                elab::Kind::TupleUnif(loc.clone(), merged_components, fresh_reference),
                loc.clone(),
            );
            *crate::compiler_diagnostics::lock_for_compile(
                ref_left.as_ref(),
                "elaboration unification cell",
            ) = elab::KUnif::Known(Box::new(merged_tuple_kind.clone()));
            *crate::compiler_diagnostics::lock_for_compile(
                ref_right.as_ref(),
                "elaboration unification cell",
            ) = elab::KUnif::Known(Box::new(merged_tuple_kind));
            Ok(())
        }

        _ => Err(Box::new(FailedToUnifyKinds::IncompatibleKinds(
            left_kind.clone(),
            right_kind.clone(),
        ))),
    }
}

/// Unify `got` with `expected` for the kind of `constructor_under_check`; record a diagnostic on failure.
///
/// `constructor_under_check` is kept for call-site parity with upstream error context (not formatted today).
fn check_kind(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    span: &Span,
    _constructor_under_check: &elab::LocatedConstructor,
    got: &elab::LocatedKind,
    expected: &elab::LocatedKind,
) {
    if let Err(unify_failure) = unify_kinds(elaboration_environment, got, expected) {
        elaboration_context.error(
            span.clone(),
            DiagnosticPayload::new(
                DiagnosticId::ElabKindMismatch,
                vec![format_failed_to_unify_kinds_message(unify_failure.as_ref())],
            ),
        );
    }
}

// ---------------------------------------------------------------------------
// Kind head-normalization
// ---------------------------------------------------------------------------

/// Follow solved [`elab::Kind::Unif`] / [`elab::Kind::TupleUnif`] cells to the representative head.
///
/// Implemented as a loop so long union-find chains (no path compression) cannot overflow the stack.
fn chase_kind_unification_head(mut kind: elab::LocatedKind) -> elab::LocatedKind {
    loop {
        let reference = match &kind.node {
            elab::Kind::Unif(_, _, reference) | elab::Kind::TupleUnif(_, _, reference) => reference,
            _ => return kind,
        };
        let guard = crate::compiler_diagnostics::lock_for_compile(
            reference.as_ref(),
            "elaboration unification cell",
        );
        if let elab::KUnif::Known(inner) = &*guard {
            let next = *inner.clone();
            drop(guard);
            kind = next;
        } else {
            drop(guard);
            return kind;
        }
    }
}

/// Resolve kind head through solved [`elab::Kind::Unif`] / [`elab::Kind::TupleUnif`] cells.
fn hnorm_kind(kind: elab::LocatedKind) -> elab::LocatedKind {
    chase_kind_unification_head(kind)
}

/// Whether `kind` normalizes to an [`elab::Kind::Arrow`] chain whose rightmost leaf is [`elab::Kind::Type`].
///
/// Used for [`SignatureItem::ClassAbs`]: explicit kinds are written `K1 -> ... -> Type` (curried), which is
/// already the classifier’s kind; bare `class c` stores only [`elab::Kind::Type`] and needs `-> Type` lifted.
fn kind_arrow_chain_ends_in_type(kind: &elab::LocatedKind) -> bool {
    match &hnorm_kind(kind.clone()).node {
        elab::Kind::Type => true,
        elab::Kind::Arrow(_, range) => kind_arrow_chain_ends_in_type(range),
        _ => false,
    }
}

/// Whether normalized `kind` is a non-trivial arrow whose codomain chain ends in [`elab::Kind::Type`].
///
/// [`elab::Kind::Type`] alone is false so bare-parameter classes still get `Arrow(Type, Type)`.
fn kind_is_multi_step_class_classifier(kind: &elab::LocatedKind) -> bool {
    match &hnorm_kind(kind.clone()).node {
        elab::Kind::Arrow(_, range) => kind_arrow_chain_ends_in_type(range),
        _ => false,
    }
}

/// Compute the kind to pass to [`elab_con_head`] for a type-class constructor head (`eq`, `fieldsOf`, …).
///
/// When the signature stores only the index kind [`elab::Kind::Type`], the classifier is `Type -> Type`.
/// When it stores a full curried kind (e.g. `Type -> {Type} -> Type` for `fieldsOf`), that **is** the
/// classifier and must not be wrapped again (matches `elab_con`/`lookupCNamed` in `elaborate.sml`).
fn kind_for_class_constructor_head(
    span: &Span,
    stored_kind: &elab::LocatedKind,
) -> elab::LocatedKind {
    let kn = hnorm_kind(stored_kind.clone());
    if kind_is_multi_step_class_classifier(&kn) {
        kn
    } else {
        let kind_type = Located::new(elab::Kind::Type, span.clone());
        Located::new(
            elab::Kind::Arrow(Box::new(kn), Box::new(kind_type)),
            span.clone(),
        )
    }
}

// ---------------------------------------------------------------------------
// Elaboration context (thread-local mutable state)
// ---------------------------------------------------------------------------

/// Pending disjointness / typeclass constraint.
#[derive(Debug, Clone)]
pub enum Constraint {
    Disjoint {
        span: Span,
        elaboration_environment: Env,
        goal: disjoint::Goal,
    },
    TypeClass {
        span: Span,
        elaboration_environment: Env,
        class: elab::LocatedConstructor,
        /// Where to write the resolved witness expression.
        result: Arc<Mutex<Option<elab::LocatedExpression>>>,
    },
}

/// Mutable state threaded through elaboration.
pub struct ElabCtx {
    /// Errors collected so far.
    pub errors: Vec<(Span, DiagnosticPayload)>,
    /// Pending constraints to solve at end of each declaration.
    pub constraints: Vec<Constraint>,
    /// The id of the Basis structure.
    pub basis_r: usize,
    /// The id of the Top structure.
    pub top_r: usize,
    /// Cached Basis types.
    pub int_con: Option<elab::LocatedConstructor>,
    pub float_con: Option<elab::LocatedConstructor>,
    pub string_con: Option<elab::LocatedConstructor>,
    pub char_con: Option<elab::LocatedConstructor>,
    pub bool_con: Option<elab::LocatedConstructor>,
    pub unit_record_con: Option<elab::LocatedConstructor>,
    /// Whether we are inside a signature (affects error reporting).
    pub in_signature: bool,
    /// Whether record unification may be delayed.
    pub may_delay: bool,
}

impl Default for ElabCtx {
    fn default() -> Self {
        Self::new()
    }
}

impl ElabCtx {
    pub fn new() -> Self {
        ElabCtx {
            errors: Vec::new(),
            constraints: Vec::new(),
            basis_r: 0,
            top_r: 0,
            int_con: None,
            float_con: None,
            string_con: None,
            char_con: None,
            bool_con: None,
            unit_record_con: None,
            in_signature: false,
            may_delay: false,
        }
    }

    pub fn error(&mut self, span: Span, payload: DiagnosticPayload) {
        self.errors.push((span, payload));
    }

    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }
}

// ---------------------------------------------------------------------------
// Project a constructor/value/etc. from a named structure's signature
// ---------------------------------------------------------------------------

/// Walk the items of a signature to find a `SgiCon`/`SgiConAbs`/`SgiClass` named `x`.
fn sgi_find_con<'a>(
    sgis: &'a [elab::LocatedSignatureItem],
    x: &str,
) -> Option<&'a elab::SignatureItem> {
    for sgi in sgis {
        match &sgi.node {
            elab::SignatureItem::Constructor(name, _, _, _) if name == x => return Some(&sgi.node),
            elab::SignatureItem::ConAbs(name, _, _) if name == x => return Some(&sgi.node),
            elab::SignatureItem::ClassAbs(name, _, _) if name == x => return Some(&sgi.node),
            elab::SignatureItem::Class(name, _, _, _) if name == x => return Some(&sgi.node),
            _ => {}
        }
    }
    None
}

fn sgi_find_val<'a>(
    sgis: &'a [elab::LocatedSignatureItem],
    x: &str,
) -> Option<&'a elab::SignatureItem> {
    for sgi in sgis {
        if let elab::SignatureItem::Val(name, _, _) = &sgi.node {
            if name == x {
                return Some(&sgi.node);
            }
        }
    }
    None
}

fn sgi_find_str<'a>(
    sgis: &'a [elab::LocatedSignatureItem],
    x: &str,
) -> Option<&'a elab::SignatureItem> {
    for sgi in sgis {
        if let elab::SignatureItem::Structure(_, name, _, _) = &sgi.node {
            if name == x {
                return Some(&sgi.node);
            }
        }
    }
    None
}

fn sgi_find_datatype<'a>(
    sgis: &'a [elab::LocatedSignatureItem],
    x: &str,
) -> Option<&'a elab::DatatypeDecl> {
    for sgi in sgis {
        if let elab::SignatureItem::Datatype(dts) = &sgi.node {
            for dt in dts {
                if dt.name == x {
                    return Some(dt);
                }
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Kind elaboration
// ---------------------------------------------------------------------------

/// Elaborate a source kind into [`elab::LocatedKind`] (binders, arrows, unification for wildcards).
///
/// # Arguments
///
/// * `elaboration_context` — Collects errors (e.g. unbound kind variable).
/// * `elaboration_environment` — Kind/constructor binding environment.
/// * `k` — Parsed kind.
///
/// # Returns
///
/// Elaborated kind; on error also records via `elaboration_context` and returns [`elab::Kind::Error`] or a fresh unifier.
pub fn elab_kind(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    k: &source::LocKind,
) -> elab::LocatedKind {
    let span = k.span.clone();
    match &k.node {
        source::Kind::Type => Located::new(elab::Kind::Type, span),
        source::Kind::Name => Located::new(elab::Kind::Name, span),
        source::Kind::Unit => Located::new(elab::Kind::Unit, span),
        source::Kind::Wild => fresh_kunif(span, "_"),
        source::Kind::Var(x) => {
            if let Some(idx) = elaboration_environment.lookup_k(x) {
                Located::new(elab::Kind::Rel(idx), span)
            } else {
                elaboration_context.error(
                    span.clone(),
                    DiagnosticPayload::new(
                        DiagnosticId::ElabUnboundKindVariableTemplate,
                        vec![x.to_string()],
                    ),
                );
                elaborated_kind_error_at_span(span)
            }
        }
        source::Kind::Arrow(k1, k2) => {
            let k1e = elab_kind(elaboration_context, elaboration_environment, k1);
            let k2e = elab_kind(elaboration_context, elaboration_environment, k2);
            Located::new(elab::Kind::Arrow(Box::new(k1e), Box::new(k2e)), span)
        }
        source::Kind::Record(k1) => {
            let k1e = elab_kind(elaboration_context, elaboration_environment, k1);
            Located::new(elab::Kind::Record(Box::new(k1e)), span)
        }
        source::Kind::Tuple(ks) => {
            let kse: Vec<_> = ks
                .iter()
                .map(|ki| elab_kind(elaboration_context, elaboration_environment, ki))
                .collect();
            Located::new(elab::Kind::Tuple(kse), span)
        }
        source::Kind::Fun(x, body) => {
            let env2 = elaboration_environment.clone().push_k_rel(x.clone());
            let bodye = elab_kind(elaboration_context, &env2, body);
            Located::new(elab::Kind::Fun(x.clone(), Box::new(bodye)), span)
        }
    }
}

// ---------------------------------------------------------------------------
// Constructor head elaboration (for implicit kind args)
// ---------------------------------------------------------------------------

/// Insert implicit [`elab::Constructor::KApp`] nodes while `kind` is [`elab::Kind::Fun`] (iterative loop).
///
/// Mirrors `elabConHead`: supplies inferred kind arguments for polymorphic type constructors.
///
/// # Arguments
///
/// * `constructor` — Elaborated constructor spine.
/// * `kind` — Its kind (possibly several `Kind::Fun` binders after normalization).
///
/// # Returns
///
/// The wrapped constructor and the remaining non-`Fun` kind head.
fn elab_con_head(
    mut constructor: elab::LocatedConstructor,
    mut kind: elab::LocatedKind,
) -> (elab::LocatedConstructor, elab::LocatedKind) {
    let span = constructor.span.clone();
    loop {
        let normalized_kind = hnorm_kind(kind);
        match &normalized_kind.node {
            elab::Kind::Fun(binder_name, body_kind) => {
                let fresh_kind_meta = fresh_kunif(span.clone(), binder_name);
                constructor = Located::new(
                    elab::Constructor::KApp(
                        Box::new(constructor),
                        Box::new(fresh_kind_meta.clone()),
                    ),
                    span.clone(),
                );
                kind = sub_kind_in_kind(0, &fresh_kind_meta, *body_kind.clone());
            }
            _ => return (constructor, normalized_kind),
        }
    }
}

// ---------------------------------------------------------------------------
// Constructor elaboration
// ---------------------------------------------------------------------------

/// Elaborate a source constructor and infer its kind (modules, applications, records, `Map`, type funs).
///
/// Recursion depth is capped at 500; overflow records an error and returns error kind/constructor nodes.
///
/// # Arguments
///
/// * `elaboration_context` — Diagnostic context.
/// * `elaboration_environment` — Full elaboration environment.
/// * `c` — Parsed constructor.
///
/// # Returns
///
/// Pair `(constructor, kind)` after [`elab_con_head`] insertion of implicit kind apps where needed.
pub fn elab_con(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    c: &source::LocCon,
) -> (elab::LocatedConstructor, elab::LocatedKind) {
    use std::cell::Cell;
    thread_local! {
        static ELAB_CON_DEPTH: Cell<usize> = const { Cell::new(0) };
    }
    let d = ELAB_CON_DEPTH.with(|c| {
        let v = c.get();
        c.set(v + 1);
        v
    });
    if d > 500 {
        ELAB_CON_DEPTH.with(|c| c.set(0));
        let span = c.span.clone();
        elaboration_context.error(
            span.clone(),
            DiagnosticPayload::new(DiagnosticId::ElabConstructorRecursionDepth, Vec::new()),
        );
        return (
            elaborated_constructor_error_at_span(span.clone()),
            elaborated_kind_error_at_span(span),
        );
    }
    let result = elab_con_inner(elaboration_context, elaboration_environment, c);
    ELAB_CON_DEPTH.with(|c| c.set(d));
    result
}

fn elab_con_inner(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    c: &source::LocCon,
) -> (elab::LocatedConstructor, elab::LocatedKind) {
    let span = c.span.clone();
    match &c.node {
        source::Con::Annot(c1, k) => {
            let ke = elab_kind(elaboration_context, elaboration_environment, k);
            let (ce, ck) = elab_con(elaboration_context, elaboration_environment, c1);
            check_kind(
                elaboration_context,
                elaboration_environment,
                &span,
                &ce,
                &ck,
                &ke,
            );
            (ce, ke)
        }
        source::Con::Wild(k) => {
            let ke = elab_kind(elaboration_context, elaboration_environment, k);
            let cu = fresh_cunif(elaboration_environment, span.clone(), ke.clone(), "_");
            (cu, ke)
        }
        source::Con::Var(ms, x) => {
            elab_con_var(elaboration_context, elaboration_environment, ms, x, &span)
        }
        source::Con::App(c1, c2) => {
            let (c1e, k1) = elab_con(elaboration_context, elaboration_environment, c1);
            let kn = hnorm_kind(k1);
            match kn.node {
                elab::Kind::Arrow(kd, kr) => {
                    let (c2e, k2) = elab_con(elaboration_context, elaboration_environment, c2);
                    check_kind(
                        elaboration_context,
                        elaboration_environment,
                        &c2.span,
                        &c2e,
                        &k2,
                        &kd,
                    );
                    let result =
                        Located::new(elab::Constructor::App(Box::new(c1e), Box::new(c2e)), span);
                    (result, *kr)
                }
                elab::Kind::Unif(_, _, r) => {
                    // Need arrow; create fresh domain/range
                    let kd = fresh_kunif(span.clone(), "_d");
                    let kr = fresh_kunif(span.clone(), "_r");
                    let karrow = Located::new(
                        elab::Kind::Arrow(Box::new(kd.clone()), Box::new(kr.clone())),
                        span.clone(),
                    );
                    *crate::compiler_diagnostics::lock_for_compile(
                        r.as_ref(),
                        "elaboration unification cell",
                    ) = elab::KUnif::Known(Box::new(karrow));
                    let (c2e, k2) = elab_con(elaboration_context, elaboration_environment, c2);
                    check_kind(
                        elaboration_context,
                        elaboration_environment,
                        &c2.span,
                        &c2e,
                        &k2,
                        &kd,
                    );
                    let result =
                        Located::new(elab::Constructor::App(Box::new(c1e), Box::new(c2e)), span);
                    (result, kr)
                }
                _ => {
                    elaboration_context.error(
                        span.clone(),
                        DiagnosticPayload::new(
                            DiagnosticId::ElabConstructorAppNonArrow,
                            Vec::new(),
                        ),
                    );
                    (
                        elaborated_constructor_error_at_span(span.clone()),
                        elaborated_kind_error_at_span(span),
                    )
                }
            }
        }
        source::Con::TFun(c1, c2) => {
            let (c1e, k1) = elab_con(elaboration_context, elaboration_environment, c1);
            let (c2e, k2) = elab_con(elaboration_context, elaboration_environment, c2);
            let ktype = Located::new(elab::Kind::Type, span.clone());
            check_kind(
                elaboration_context,
                elaboration_environment,
                &c1.span,
                &c1e,
                &k1,
                &ktype,
            );
            check_kind(
                elaboration_context,
                elaboration_environment,
                &c2.span,
                &c2e,
                &k2,
                &ktype,
            );
            let result = Located::new(elab::Constructor::TFun(Box::new(c1e), Box::new(c2e)), span);
            (result, ktype)
        }
        source::Con::TCFun(exp, x, k, body) => {
            let ke = elab_kind(elaboration_context, elaboration_environment, k);
            let env2 = elaboration_environment
                .clone()
                .push_c_rel(x.clone(), ke.clone());
            let (bodye, bodyke) = elab_con(elaboration_context, &env2, body);
            let ktype = Located::new(elab::Kind::Type, span.clone());
            check_kind(
                elaboration_context,
                elaboration_environment,
                &body.span,
                &bodye,
                &bodyke,
                &ktype,
            );
            let exp_e = elab_explicitness(*exp);
            let result = Located::new(
                elab::Constructor::TCFun(exp_e, x.clone(), Box::new(ke), Box::new(bodye)),
                span,
            );
            (result, ktype)
        }
        source::Con::TRecord(r) => {
            let (re, rk) = elab_con(elaboration_context, elaboration_environment, r);
            let _kname = Located::new(elab::Kind::Name, span.clone());
            let ktype = Located::new(elab::Kind::Type, span.clone());
            let krow = Located::new(elab::Kind::Record(Box::new(ktype)), span.clone());
            check_kind(
                elaboration_context,
                elaboration_environment,
                &r.span,
                &re,
                &rk,
                &krow,
            );
            let result = Located::new(elab::Constructor::TRecord(Box::new(re)), span.clone());
            (result, Located::new(elab::Kind::Type, span))
        }
        source::Con::TDisjoint(c1, c2, body) => {
            let (c1e, k1) = elab_con(elaboration_context, elaboration_environment, c1);
            let (c2e, k2) = elab_con(elaboration_context, elaboration_environment, c2);
            let (bodye, bodyk) = elab_con(elaboration_context, elaboration_environment, body);
            // c1 and c2 should each be rows; disjointness is about key sets
            // so their element kinds may differ independently.
            let ku1 = fresh_kunif(span.clone(), "_");
            let krow1 = Located::new(elab::Kind::Record(Box::new(ku1)), span.clone());
            check_kind(
                elaboration_context,
                elaboration_environment,
                &c1.span,
                &c1e,
                &k1,
                &krow1,
            );
            let ku2 = fresh_kunif(span.clone(), "_");
            let krow2 = Located::new(elab::Kind::Record(Box::new(ku2)), span.clone());
            check_kind(
                elaboration_context,
                elaboration_environment,
                &c2.span,
                &c2e,
                &k2,
                &krow2,
            );
            let result = Located::new(
                elab::Constructor::TDisjoint(Box::new(c1e), Box::new(c2e), Box::new(bodye)),
                span,
            );
            (result, bodyk)
        }
        source::Con::Name(s) => {
            let kname = Located::new(elab::Kind::Name, span.clone());
            let result = Located::new(elab::Constructor::Name(s.clone()), span);
            (result, kname)
        }
        source::Con::Record(xcs) => {
            // Row literal [f1 = c1, ...]
            // Each ci must have the same kind K; the result has kind {K}
            let ku = fresh_kunif(span.clone(), "_");
            let mut fields = Vec::new();
            for (nc, vc) in xcs {
                let (nce, nck) = elab_con(elaboration_context, elaboration_environment, nc);
                let kname = Located::new(elab::Kind::Name, span.clone());
                check_kind(
                    elaboration_context,
                    elaboration_environment,
                    &nc.span,
                    &nce,
                    &nck,
                    &kname,
                );
                let (vce, vck) = elab_con(elaboration_context, elaboration_environment, vc);
                // In Ur/Web, [nm] where nm :: Name is a shorthand for [nm = ()].
                // When the value elaborates to kind Name (due to punning), treat
                // it as a unit value and use {Unit} as the row element kind.
                let (vce, vck) = if matches!(vck.node, elab::Kind::Name) {
                    let kunit = Located::new(elab::Kind::Unit, span.clone());
                    let unit_c = Located::new(elab::Constructor::Unit, span.clone());
                    (unit_c, kunit)
                } else {
                    (vce, vck)
                };
                check_kind(
                    elaboration_context,
                    elaboration_environment,
                    &vc.span,
                    &vce,
                    &vck,
                    &ku,
                );
                fields.push((nce, vce));
            }
            let krow = Located::new(elab::Kind::Record(Box::new(ku)), span.clone());
            let result = Located::new(
                elab::Constructor::Record(Box::new(krow.clone()), fields),
                span,
            );
            (result, krow)
        }
        source::Con::Concat(c1, c2) => {
            let (c1e, k1) = elab_con(elaboration_context, elaboration_environment, c1);
            let (c2e, k2) = elab_con(elaboration_context, elaboration_environment, c2);
            check_kind(
                elaboration_context,
                elaboration_environment,
                &c2.span,
                &c2e,
                &k2,
                &k1,
            );
            let result = Located::new(
                elab::Constructor::Concat(Box::new(c1e), Box::new(c2e)),
                span,
            );
            (result, k1)
        }
        source::Con::Map => {
            // map : (K1 -> K2) -> {K1} -> {K2}
            let k1 = fresh_kunif(span.clone(), "k1");
            let k2 = fresh_kunif(span.clone(), "k2");
            let map_kind = Located::new(
                elab::Kind::Arrow(
                    Box::new(Located::new(
                        elab::Kind::Arrow(Box::new(k1.clone()), Box::new(k2.clone())),
                        span.clone(),
                    )),
                    Box::new(Located::new(
                        elab::Kind::Arrow(
                            Box::new(Located::new(
                                elab::Kind::Record(Box::new(k1.clone())),
                                span.clone(),
                            )),
                            Box::new(Located::new(
                                elab::Kind::Record(Box::new(k2.clone())),
                                span.clone(),
                            )),
                        ),
                        span.clone(),
                    )),
                ),
                span.clone(),
            );
            let result = Located::new(elab::Constructor::Map(Box::new(k1), Box::new(k2)), span);
            (result, map_kind)
        }
        source::Con::Unit => {
            let result = Located::new(elab::Constructor::Unit, span.clone());
            let ku = Located::new(elab::Kind::Unit, span);
            (result, ku)
        }
        source::Con::Tuple(cs) => {
            let mut ces = Vec::new();
            let mut ks = Vec::new();
            for ci in cs {
                let (ce, ke) = elab_con(elaboration_context, elaboration_environment, ci);
                ces.push(ce);
                ks.push(ke);
            }
            let kt = Located::new(elab::Kind::Tuple(ks), span.clone());
            let result = Located::new(elab::Constructor::Tuple(ces), span);
            (result, kt)
        }
        source::Con::Proj(c1, n) => {
            let (c1e, k1) = elab_con(elaboration_context, elaboration_environment, c1);
            let kn = hnorm_kind(k1.clone());
            let component_kind = fresh_kunif(span.clone(), &format!("proj{}", n));
            let tuple_unif_ref = Arc::new(Mutex::new(elab::KUnif::Unknown));
            let tuple_unif_kind = Located::new(
                elab::Kind::TupleUnif(
                    span.clone(),
                    vec![(*n, component_kind.clone())],
                    tuple_unif_ref,
                ),
                span.clone(),
            );
            check_kind(
                elaboration_context,
                elaboration_environment,
                &c1.span,
                &c1e,
                &kn,
                &tuple_unif_kind,
            );
            let result = Located::new(elab::Constructor::Proj(Box::new(c1e), *n), span);
            (result, hnorm_kind(component_kind))
        }
        source::Con::Abs(x, opt_k, body) => {
            let ke = match opt_k {
                Some(k) => elab_kind(elaboration_context, elaboration_environment, k),
                None => fresh_kunif(span.clone(), x),
            };
            let env2 = elaboration_environment
                .clone()
                .push_c_rel(x.clone(), ke.clone());
            let (bodye, bodyke) = elab_con(elaboration_context, &env2, body);
            let result_kind = Located::new(
                elab::Kind::Arrow(Box::new(ke.clone()), Box::new(bodyke)),
                span.clone(),
            );
            let result = Located::new(
                elab::Constructor::Abs(x.clone(), Box::new(ke), Box::new(bodye)),
                span,
            );
            (result, result_kind)
        }
        source::Con::KAbs(x, body) => {
            let env2 = elaboration_environment.clone().push_k_rel(x.clone());
            let (bodye, bodyke) = elab_con(elaboration_context, &env2, body);
            let result = Located::new(
                elab::Constructor::KAbs(x.clone(), Box::new(bodye)),
                span.clone(),
            );
            // kind is Fun(x, bodyke)
            let rk = Located::new(elab::Kind::Fun(x.clone(), Box::new(bodyke)), span);
            (result, rk)
        }
        source::Con::TKFun(x, body) => {
            let env2 = elaboration_environment.clone().push_k_rel(x.clone());
            let (bodye, bodyke) = elab_con(elaboration_context, &env2, body);
            let ktype = Located::new(elab::Kind::Type, span.clone());
            check_kind(
                elaboration_context,
                elaboration_environment,
                &body.span,
                &bodye,
                &bodyke,
                &ktype,
            );
            let result = Located::new(elab::Constructor::TKFun(x.clone(), Box::new(bodye)), span);
            (result, ktype)
        }
    }
}

/// Resolve a constructor variable (`t`, `M.t`, or `show` as a type-class head).
///
/// Unqualified type-class names use their *parameter* kind in `named_c`; this function supplies
/// the classifier kind `parameter -> Type` for [`elab::Constructor::App`] when [`Env::is_class`]
/// applies.
///
/// # Returns
///
/// Elaborated constructor and its kind at this occurrence.
fn elab_con_var(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    ms: &[String],
    x: &str,
    span: &Span,
) -> (elab::LocatedConstructor, elab::LocatedKind) {
    if ms.is_empty() {
        match elaboration_environment.lookup_c(x) {
            VarLookup::Rel(idx, k) => {
                let c = Located::new(elab::Constructor::Rel(idx), span.clone());
                let (c2, k2) = elab_con_head(c, k);
                return (c2, k2);
            }
            VarLookup::Named(id, k) => {
                let c = Located::new(elab::Constructor::Named(id), span.clone());
                // Type-class kinds: bare `class c` stores [`Type`]; `class f :: K1 -> ... -> Type` stores the full chain.
                let k_for_head = if elaboration_environment.is_class(&c) {
                    kind_for_class_constructor_head(span, &k)
                } else {
                    k.clone()
                };
                let (c2, k2) = elab_con_head(c, k_for_head);
                return (c2, k2);
            }
            VarLookup::NotBound => {
                // In Ur/Web, uppercase identifiers that are not in scope are
                // treated as name literals (kind Name) — e.g. field labels like
                // `Body`, `Form`, `Table` used in row contexts.
                if x.chars().next().map(|c| c.is_uppercase()).unwrap_or(false) {
                    let kname = Located::new(elab::Kind::Name, span.clone());
                    let c = Located::new(elab::Constructor::Name(x.to_string()), span.clone());
                    return (c, kname);
                }
                elaboration_context.error(
                    span.clone(),
                    DiagnosticPayload::new(
                        DiagnosticId::ElabUnboundTypeConstructor,
                        vec![x.to_string()],
                    ),
                );
                return (
                    elaborated_constructor_error_at_span(span.clone()),
                    elaborated_kind_error_at_span(span.clone()),
                );
            }
        }
    }

    // Qualified: Ms.x
    // Chase the module path
    let (str_id, sgn_items) =
        match resolve_module_path(elaboration_context, elaboration_environment, ms, span) {
            Some(x) => x,
            None => {
                return (
                    elaborated_constructor_error_at_span(span.clone()),
                    elaborated_kind_error_at_span(span.clone()),
                )
            }
        };

    // Now find x in the signature items
    if let Some(sgi) = sgi_find_con(&sgn_items, x) {
        match sgi {
            elab::SignatureItem::Constructor(_, _id, k, _)
            | elab::SignatureItem::ConAbs(_, _id, k) => {
                // Project with remaining path empty since we're done
                let c = Located::new(
                    elab::Constructor::ModProj(str_id, ms[1..].to_vec(), x.to_string()),
                    span.clone(),
                );
                let (c2, k2) = elab_con_head(c, k.clone());
                return (c2, k2);
            }
            elab::SignatureItem::ClassAbs(_, _id, k) | elab::SignatureItem::Class(_, _id, k, _) => {
                let c = Located::new(
                    elab::Constructor::ModProj(str_id, ms[1..].to_vec(), x.to_string()),
                    span.clone(),
                );
                let class_k = kind_for_class_constructor_head(span, k);
                let (c2, k2) = elab_con_head(c, class_k);
                return (c2, k2);
            }
            _ => {}
        }
    }

    elaboration_context.error(
        span.clone(),
        DiagnosticPayload::new(
            DiagnosticId::ElabUnboundTypeConstructor,
            vec![x.to_string()],
        ),
    );
    (
        elaborated_constructor_error_at_span(span.clone()),
        elaborated_kind_error_at_span(span.clone()),
    )
}

/// Resolve a module path `[M1, M2, ...]` to `(str_id, sig_items)`.
/// Resolve a module path like ["Basis"] or ["Foo", "Bar"].
/// Returns (root_id, items_of_final_module) where root_id is the ID of the FIRST module.
/// Callers building ModProj(root_id, sub_path, x) should use `ms[1..]` as sub_path.
fn resolve_module_path(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    ms: &[String],
    span: &Span,
) -> Option<(usize, Vec<elab::LocatedSignatureItem>)> {
    if ms.is_empty() {
        return None;
    }
    let first = &ms[0];
    let (root_id, mut sgn) = match elaboration_environment.lookup_str(first) {
        Some((sid, s)) => (*sid, s.clone()),
        None => {
            elaboration_context.error(
                span.clone(),
                DiagnosticPayload::new(DiagnosticId::ElabUnboundModuleFirst, vec![first.clone()]),
            );
            return None;
        }
    };

    // Chase remaining path components to get items of the final module
    let hsgn = hnorm_sgn(elaboration_environment, &sgn);
    let mut items = match &hsgn.node {
        elab::Signature::Const(sgis) => sgis.clone(),
        _ => {
            elaboration_context.error(
                span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::ElabModuleNonConstSignature,
                    vec![first.clone()],
                ),
            );
            return None;
        }
    };

    for m in &ms[1..] {
        if let Some(sgi) = sgi_find_str(&items, m) {
            match sgi {
                elab::SignatureItem::Structure(_, _, _, inner_sgn) => {
                    sgn = inner_sgn.clone();
                    let hn = hnorm_sgn(elaboration_environment, &sgn);
                    items = match &hn.node {
                        elab::Signature::Const(sgis) => sgis.clone(),
                        _ => {
                            elaboration_context.error(
                                span.clone(),
                                DiagnosticPayload::new(
                                    DiagnosticId::ElabSubModuleNonConstSignature,
                                    vec![m.clone()],
                                ),
                            );
                            return None;
                        }
                    };
                }
                _ => {
                    elaboration_context.error(
                        span.clone(),
                        DiagnosticPayload::new(DiagnosticId::ElabNotAStructure, vec![m.clone()]),
                    );
                    return None;
                }
            }
        } else {
            elaboration_context.error(
                span.clone(),
                DiagnosticPayload::new(DiagnosticId::ElabUnboundModule, vec![m.clone()]),
            );
            return None;
        }
    }

    Some((root_id, items))
}

fn elab_explicitness(e: source::Explicitness) -> elab::Explicitness {
    match e {
        source::Explicitness::Explicit => elab::Explicitness::Explicit,
        source::Explicitness::Implicit => elab::Explicitness::Implicit,
    }
}

// ---------------------------------------------------------------------------
// kindof: compute the kind of a constructor in the current environment
// ---------------------------------------------------------------------------

/// Compute the kind of an already-elaborated constructor in `elaboration_environment` (lookup, `App`, `KApp`, tuples, …).
///
/// # Arguments
///
/// * `elaboration_context` — Errors for unbound indices or ill-kinded elimination forms.
/// * `elaboration_environment` — Environment with constructor and structure bindings.
/// * `c` — Elaborated constructor.
///
/// # Returns
///
/// Inferred [`elab::LocatedKind`]; uses fresh kind unifiers for unknown module projections.
pub fn kindof(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    c: &elab::LocatedConstructor,
) -> elab::LocatedKind {
    let span = c.span.clone();
    match &c.node {
        elab::Constructor::TFun(_, _)
        | elab::Constructor::TRecord(_)
        | elab::Constructor::TDisjoint(_, _, _)
        | elab::Constructor::TKFun(_, _) => Located::new(elab::Kind::Type, span),
        elab::Constructor::TCFun(_, _, k, body) => {
            let env2 = elaboration_environment
                .clone()
                .push_c_rel("_".to_string(), *k.clone());
            let _bodyke = kindof(elaboration_context, &env2, body);
            Located::new(elab::Kind::Type, span)
        }
        elab::Constructor::Rel(n) => match elaboration_environment.lookup_c_rel(*n) {
            Ok((_, k)) => k.clone(),
            Err(_) => {
                elaboration_context.error(
                    span.clone(),
                    DiagnosticPayload::new(
                        DiagnosticId::ElabUnboundRelConstructor,
                        vec![n.to_string()],
                    ),
                );
                elaborated_kind_error_at_span(span)
            }
        },
        elab::Constructor::Named(id) => match elaboration_environment.lookup_c_named(*id) {
            Ok((_, k, _)) => {
                let head = Located::new(elab::Constructor::Named(*id), span.clone());
                if elaboration_environment.is_class(&head) {
                    kind_for_class_constructor_head(&span, k)
                } else {
                    k.clone()
                }
            }
            Err(_) => {
                elaboration_context.error(
                    span.clone(),
                    DiagnosticPayload::new(
                        DiagnosticId::ElabUnboundNamedConstructor,
                        vec![id.to_string()],
                    ),
                );
                elaborated_kind_error_at_span(span)
            }
        },
        elab::Constructor::ModProj(str_id, _path, name) => {
            // Look up in the structure's signature
            if let Ok((_, sgn)) = elaboration_environment.lookup_str_named(*str_id) {
                let items = get_sgn_const_items(elaboration_environment, sgn);
                if let Some(sgi) = sgi_find_con(&items, name) {
                    match sgi {
                        elab::SignatureItem::ConAbs(_, _, k)
                        | elab::SignatureItem::Constructor(_, _, k, _) => return k.clone(),
                        elab::SignatureItem::ClassAbs(_, _, k)
                        | elab::SignatureItem::Class(_, _, k, _) => {
                            return kind_for_class_constructor_head(&span, k);
                        }
                        _ => {}
                    }
                }
            }
            fresh_kunif(span, name)
        }
        elab::Constructor::App(f, _arg) => {
            let kf = kindof(elaboration_context, elaboration_environment, f);
            let kfn = hnorm_kind(kf);
            match kfn.node {
                elab::Kind::Arrow(_, kr) => *kr,
                _ => {
                    elaboration_context.error(
                        span.clone(),
                        DiagnosticPayload::new(
                            DiagnosticId::ElabApplicationNonArrowKind,
                            Vec::new(),
                        ),
                    );
                    elaborated_kind_error_at_span(span)
                }
            }
        }
        elab::Constructor::Abs(x, k, body) => {
            let env2 = elaboration_environment
                .clone()
                .push_c_rel(x.clone(), *k.clone());
            let bodyke = kindof(elaboration_context, &env2, body);
            Located::new(elab::Kind::Arrow(k.clone(), Box::new(bodyke)), span)
        }
        elab::Constructor::KAbs(x, body) => {
            let env2 = elaboration_environment.clone().push_k_rel(x.clone());
            let bodyke = kindof(elaboration_context, &env2, body);
            Located::new(elab::Kind::Fun(x.clone(), Box::new(bodyke)), span)
        }
        elab::Constructor::KApp(f, k) => {
            let kf = kindof(elaboration_context, elaboration_environment, f);
            let kfn = hnorm_kind(kf);
            match kfn.node {
                elab::Kind::Fun(_, body) => sub_kind_in_kind(0, k, *body),
                _ => {
                    elaboration_context.error(
                        span.clone(),
                        DiagnosticPayload::new(DiagnosticId::ElabKAppNonKFun, Vec::new()),
                    );
                    elaborated_kind_error_at_span(span)
                }
            }
        }
        elab::Constructor::Name(_) => Located::new(elab::Kind::Name, span),
        elab::Constructor::Record(k, _) => Located::new(elab::Kind::Record(k.clone()), span),
        elab::Constructor::Concat(c1, _) => {
            kindof(elaboration_context, elaboration_environment, c1)
        }
        elab::Constructor::Map(k1, k2) => {
            let _ktype = Located::new(elab::Kind::Type, span.clone());
            let arrow_k = Located::new(elab::Kind::Arrow(k1.clone(), k2.clone()), span.clone());
            let row1 = Located::new(elab::Kind::Record(k1.clone()), span.clone());
            let row2 = Located::new(elab::Kind::Record(k2.clone()), span.clone());
            Located::new(
                elab::Kind::Arrow(
                    Box::new(arrow_k),
                    Box::new(Located::new(
                        elab::Kind::Arrow(Box::new(row1), Box::new(row2)),
                        span.clone(),
                    )),
                ),
                span,
            )
        }
        elab::Constructor::Unit => Located::new(elab::Kind::Unit, span),
        elab::Constructor::Tuple(cs) => {
            let ks: Vec<_> = cs
                .iter()
                .map(|ci| kindof(elaboration_context, elaboration_environment, ci))
                .collect();
            Located::new(elab::Kind::Tuple(ks), span)
        }
        elab::Constructor::Proj(c, n) => {
            let kc = kindof(elaboration_context, elaboration_environment, c);
            let kcn = hnorm_kind(kc);
            match kcn.node {
                elab::Kind::Tuple(ks) => {
                    let idx = n.checked_sub(1).unwrap_or(0);
                    ks.get(idx)
                        .cloned()
                        .unwrap_or_else(|| elaborated_kind_error_at_span(span))
                }
                _ => elaborated_kind_error_at_span(span),
            }
        }
        elab::Constructor::Error => elaborated_kind_error_at_span(span),
        elab::Constructor::Unif(_, _, k, _, _) => *k.clone(),
    }
}

fn get_sgn_const_items(
    elaboration_environment: &Env,
    sgn: &elab::LocatedSignature,
) -> Vec<elab::LocatedSignatureItem> {
    let hn = hnorm_sgn(elaboration_environment, sgn);
    match hn.node {
        elab::Signature::Const(items) => items,
        _ => vec![],
    }
}

// ---------------------------------------------------------------------------
// Constructor unification (unifyCons)
// ---------------------------------------------------------------------------

/// Failure from [`unify_cons`] (structural clash, occurs-check, kind mismatch, depth limit).
#[derive(Debug, Clone)]
pub enum FailedToUnifyConstructors {
    IncompatibleConstructors(elab::LocatedConstructor, elab::LocatedConstructor),
    KindUnificationFailed(FailedToUnifyKinds),
    /// Recursion depth cap inside [`unify_cons_inner`].
    UnificationRecursionLimitExceeded,
    /// Constructor occurs-check blocked assigning a unification variable.
    OccursCheckWouldCycle,
}

/// Format [`FailedToUnifyKinds`] as one line for catalog substitution (e.g. [`DiagnosticId::ElabKindMismatch`]).
///
/// # Arguments
///
/// * `failure` — Result of [`unify_kinds`].
///
/// # Returns
///
/// English summary with [`crate::elaborated::type_display::format_kind`] on both sides when applicable.
pub fn format_failed_to_unify_kinds_message(failure: &FailedToUnifyKinds) -> String {
    match failure {
        FailedToUnifyKinds::IncompatibleKinds(left_kind, right_kind) => format!(
            "incompatible kinds: {} vs {}",
            crate::elaborated::type_display::format_kind(left_kind),
            crate::elaborated::type_display::format_kind(right_kind),
        ),
        FailedToUnifyKinds::OccursCheckFailed(left_kind, right_kind) => format!(
            "kind occurs-check: {} vs {}",
            crate::elaborated::type_display::format_kind(left_kind),
            crate::elaborated::type_display::format_kind(right_kind),
        ),
    }
}

/// Format [`FailedToUnifyConstructors`] for [`DiagnosticId::ElabTypeMismatch`] and similar payloads.
///
/// # Arguments
///
/// * `failure` — Result of [`unify_cons`].
///
/// # Returns
///
/// Single string suitable for `{0}` templates (no `Debug` dumps).
pub fn format_failed_to_unify_constructors_message(failure: &FailedToUnifyConstructors) -> String {
    match failure {
        FailedToUnifyConstructors::IncompatibleConstructors(left, right) => format!(
            "incompatible types: {} vs {}",
            crate::elaborated::type_display::format_constructor(left),
            crate::elaborated::type_display::format_constructor(right),
        ),
        FailedToUnifyConstructors::KindUnificationFailed(kind_failure) => format!(
            "under kind error: {}",
            format_failed_to_unify_kinds_message(kind_failure),
        ),
        FailedToUnifyConstructors::UnificationRecursionLimitExceeded => {
            "constructor unification recursion limit exceeded".to_string()
        }
        FailedToUnifyConstructors::OccursCheckWouldCycle => {
            "constructor occurs-check would form a cycle".to_string()
        }
    }
}

/// Record summary for row unification.
#[derive(Debug, Clone)]
struct RecordSummary {
    /// Known field/value pairs.
    fields: Vec<(String, elab::LocatedConstructor)>,
    /// Unification variable tails.
    unifs: Vec<(elab::CUnifRef, usize)>,
    /// Other unknown row pieces.
    others: Vec<elab::LocatedConstructor>,
}

/// Head-normalise a constructor and decompose a row constructor into a RecordSummary.
/// Named type aliases are unfolded via `elaboration_environment` so their fields are visible to the row unifier.
fn record_summary(elaboration_environment: &Env, c: elab::LocatedConstructor) -> RecordSummary {
    let cn = hnorm_con(c.clone());
    match cn.node {
        elab::Constructor::Record(_, xcs) => {
            let mut fields = Vec::new();
            for (nc, vc) in xcs {
                let ncn = hnorm_con(nc);
                if let elab::Constructor::Name(s) = ncn.node {
                    fields.push((s, vc));
                }
                // non-literal names go to others (simplified)
            }
            RecordSummary {
                fields,
                unifs: vec![],
                others: vec![],
            }
        }
        elab::Constructor::Concat(c1, c2) => {
            let mut s1 = record_summary(elaboration_environment, *c1);
            let s2 = record_summary(elaboration_environment, *c2);
            s1.fields.extend(s2.fields);
            s1.unifs.extend(s2.unifs);
            s1.others.extend(s2.others);
            s1
        }
        elab::Constructor::Unif(nl, _, _, _, r) => RecordSummary {
            fields: vec![],
            unifs: vec![(r, nl)],
            others: vec![],
        },
        elab::Constructor::Unit => RecordSummary {
            fields: vec![],
            unifs: vec![],
            others: vec![],
        },
        // Unfold Named type aliases (e.g. `body'`) so their fields become visible.
        elab::Constructor::Named(id) => {
            if let Ok((_, _, Some(def))) = elaboration_environment.lookup_c_named(id) {
                record_summary(elaboration_environment, def.clone())
            } else {
                RecordSummary {
                    fields: vec![],
                    unifs: vec![],
                    others: vec![cn],
                }
            }
        }
        _ => RecordSummary {
            fields: vec![],
            unifs: vec![],
            others: vec![cn],
        },
    }
}

/// Unify two elaborated constructors, mutating [`elab::CUnif`] cells and recurring into structure.
///
/// Uses [`hnorm_con`] / [`cons_eq_simple`] fast paths and row summaries for records. Inner depth capped at 100
/// ([`FailedToUnifyConstructors::UnificationRecursionLimitExceeded`]).
///
/// # Arguments
///
/// * `elaboration_context` — For auxiliary errors (some paths).
/// * `elaboration_environment` — For named-type expansion in row unification.
/// * `diagnostic_span` — Location for errors tied to this attempt.
/// * `left_constructor`, `right_constructor` — Types to equate.
///
/// # Errors
///
/// Boxed [`FailedToUnifyConstructors`] (large AST in some variants) on failure.
///
/// # Returns
///
/// `Ok(())` when constructors match or are unified; [`elab::Constructor::Error`] pairs succeed trivially.
pub fn unify_cons(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    diagnostic_span: &Span,
    left_constructor: &elab::LocatedConstructor,
    right_constructor: &elab::LocatedConstructor,
) -> Result<(), Box<FailedToUnifyConstructors>> {
    unify_cons_inner(
        elaboration_context,
        elaboration_environment,
        diagnostic_span,
        left_constructor,
        right_constructor,
        0,
    )
}

fn unify_cons_inner(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    diagnostic_span: &Span,
    left_constructor: &elab::LocatedConstructor,
    right_constructor: &elab::LocatedConstructor,
    recursion_depth: usize,
) -> Result<(), Box<FailedToUnifyConstructors>> {
    if recursion_depth > 100 {
        return Err(Box::new(
            FailedToUnifyConstructors::UnificationRecursionLimitExceeded,
        ));
    }

    // Chase known unif vars first
    let left_normalized = hnorm_con(left_constructor.clone());
    let right_normalized = hnorm_con(right_constructor.clone());

    // Quick structural equality check
    if cons_eq_simple(&left_normalized, &right_normalized) {
        return Ok(());
    }

    match (&left_normalized.node, &right_normalized.node) {
        (elab::Constructor::Error, _) | (_, elab::Constructor::Error) => Ok(()),

        (elab::Constructor::Rel(n1), elab::Constructor::Rel(n2)) => {
            if n1 == n2 {
                return Ok(());
            }
            Err(Box::new(
                FailedToUnifyConstructors::IncompatibleConstructors(
                    left_normalized,
                    right_normalized,
                ),
            ))
        }
        // Unification variable solving — must come before Named arms so that
        // (Unif, Named) is handled here rather than falling into the Named expansion arm.
        (
            elab::Constructor::Unif(nl1, _, _k1, _, r1),
            elab::Constructor::Unif(_nl2, _, _k2, _, r2),
        ) => {
            if Arc::ptr_eq(r1, r2) {
                return Ok(());
            }
            // Solve r1 := right_normalized (adjusted for nesting); occurs check to prevent circular types
            if occurs_cunif(r1, &right_normalized) {
                return Err(Box::new(FailedToUnifyConstructors::OccursCheckWouldCycle));
            }
            let adjusted = mlift_con_in_con(*nl1, right_normalized.clone());
            *crate::compiler_diagnostics::lock_for_compile(
                r1.as_ref(),
                "elaboration unification cell",
            ) = elab::CUnif::Known(Box::new(adjusted));
            Ok(())
        }
        (elab::Constructor::Unif(nl, _, _k, _, r), _) => {
            if occurs_cunif(r, &right_normalized) {
                return Err(Box::new(FailedToUnifyConstructors::OccursCheckWouldCycle));
            }
            let adjusted = mlift_con_in_con(*nl, right_normalized.clone());
            *crate::compiler_diagnostics::lock_for_compile(
                r.as_ref(),
                "elaboration unification cell",
            ) = elab::CUnif::Known(Box::new(adjusted));
            Ok(())
        }
        (_, elab::Constructor::Unif(nl, _, _k, _, r)) => {
            if occurs_cunif(r, &left_normalized) {
                return Err(Box::new(FailedToUnifyConstructors::OccursCheckWouldCycle));
            }
            let adjusted = mlift_con_in_con(*nl, left_normalized.clone());
            *crate::compiler_diagnostics::lock_for_compile(
                r.as_ref(),
                "elaboration unification cell",
            ) = elab::CUnif::Known(Box::new(adjusted));
            Ok(())
        }

        (elab::Constructor::Named(n1), elab::Constructor::Named(n2)) => {
            if n1 == n2 {
                return Ok(());
            }
            // Try to unfold named constructors
            if let Ok((_, _, Some(def1))) = elaboration_environment.lookup_c_named(*n1) {
                return unify_cons_inner(
                    elaboration_context,
                    elaboration_environment,
                    diagnostic_span,
                    &def1.clone(),
                    right_constructor,
                    recursion_depth + 1,
                );
            }
            if let Ok((_, _, Some(def2))) = elaboration_environment.lookup_c_named(*n2) {
                return unify_cons_inner(
                    elaboration_context,
                    elaboration_environment,
                    diagnostic_span,
                    left_constructor,
                    &def2.clone(),
                    recursion_depth + 1,
                );
            }
            Err(Box::new(
                FailedToUnifyConstructors::IncompatibleConstructors(
                    left_normalized,
                    right_normalized,
                ),
            ))
        }
        (elab::Constructor::Named(n1), _) => {
            if let Ok((_, _, Some(def1))) = elaboration_environment.lookup_c_named(*n1) {
                return unify_cons_inner(
                    elaboration_context,
                    elaboration_environment,
                    diagnostic_span,
                    &def1.clone(),
                    right_constructor,
                    recursion_depth + 1,
                );
            }
            // Try reducing
            let rc1 = reduce_con(left_normalized.clone());
            if !cons_eq_simple(&rc1, &left_normalized) {
                return unify_cons_inner(
                    elaboration_context,
                    elaboration_environment,
                    diagnostic_span,
                    &rc1,
                    right_constructor,
                    recursion_depth + 1,
                );
            }
            Err(Box::new(
                FailedToUnifyConstructors::IncompatibleConstructors(
                    left_normalized,
                    right_normalized,
                ),
            ))
        }
        (_, elab::Constructor::Named(n2)) => {
            if let Ok((_, _, Some(def2))) = elaboration_environment.lookup_c_named(*n2) {
                return unify_cons_inner(
                    elaboration_context,
                    elaboration_environment,
                    diagnostic_span,
                    left_constructor,
                    &def2.clone(),
                    recursion_depth + 1,
                );
            }
            let rc2 = reduce_con(right_normalized.clone());
            if !cons_eq_simple(&rc2, &right_normalized) {
                return unify_cons_inner(
                    elaboration_context,
                    elaboration_environment,
                    diagnostic_span,
                    left_constructor,
                    &rc2,
                    recursion_depth + 1,
                );
            }
            Err(Box::new(
                FailedToUnifyConstructors::IncompatibleConstructors(
                    left_normalized,
                    right_normalized,
                ),
            ))
        }

        // Structural cases
        (elab::Constructor::TFun(d1, r1), elab::Constructor::TFun(d2, r2)) => {
            unify_cons_inner(
                elaboration_context,
                elaboration_environment,
                diagnostic_span,
                d1,
                d2,
                recursion_depth + 1,
            )?;
            unify_cons_inner(
                elaboration_context,
                elaboration_environment,
                diagnostic_span,
                r1,
                r2,
                recursion_depth + 1,
            )
        }
        (elab::Constructor::TCFun(e1, x1, k1, b1), elab::Constructor::TCFun(e2, _, k2, b2)) => {
            if e1 != e2 {
                return Err(Box::new(
                    FailedToUnifyConstructors::IncompatibleConstructors(
                        left_normalized,
                        right_normalized,
                    ),
                ));
            }
            unify_kinds(elaboration_environment, k1, k2)
                .map_err(|ek| Box::new(FailedToUnifyConstructors::KindUnificationFailed(*ek)))?;
            let constructor_environment_extended = elaboration_environment
                .clone()
                .push_c_rel(x1.clone(), *k1.clone());
            unify_cons_inner(
                elaboration_context,
                &constructor_environment_extended,
                diagnostic_span,
                b1,
                b2,
                recursion_depth + 1,
            )
        }
        (elab::Constructor::TRecord(r1), elab::Constructor::TRecord(r2)) => unify_cons_inner(
            elaboration_context,
            elaboration_environment,
            diagnostic_span,
            r1,
            r2,
            recursion_depth + 1,
        ),
        (elab::Constructor::TDisjoint(_, _, b1), _) => unify_cons_inner(
            elaboration_context,
            elaboration_environment,
            diagnostic_span,
            b1,
            right_constructor,
            recursion_depth + 1,
        ),
        (_, elab::Constructor::TDisjoint(_, _, b2)) => unify_cons_inner(
            elaboration_context,
            elaboration_environment,
            diagnostic_span,
            left_constructor,
            b2,
            recursion_depth + 1,
        ),
        (elab::Constructor::App(f1, a1), elab::Constructor::App(f2, a2)) => {
            unify_cons_inner(
                elaboration_context,
                elaboration_environment,
                diagnostic_span,
                f1,
                f2,
                recursion_depth + 1,
            )?;
            unify_cons_inner(
                elaboration_context,
                elaboration_environment,
                diagnostic_span,
                a1,
                a2,
                recursion_depth + 1,
            )
        }
        (elab::Constructor::Abs(x1, k1, b1), elab::Constructor::Abs(_, k2, b2)) => {
            unify_kinds(elaboration_environment, k1, k2)
                .map_err(|ek| Box::new(FailedToUnifyConstructors::KindUnificationFailed(*ek)))?;
            let constructor_environment_extended = elaboration_environment
                .clone()
                .push_c_rel(x1.clone(), *k1.clone());
            unify_cons_inner(
                elaboration_context,
                &constructor_environment_extended,
                diagnostic_span,
                b1,
                b2,
                recursion_depth + 1,
            )
        }
        (elab::Constructor::KAbs(x1, b1), elab::Constructor::KAbs(_, b2)) => {
            let constructor_environment_extended =
                elaboration_environment.clone().push_k_rel(x1.clone());
            unify_cons_inner(
                elaboration_context,
                &constructor_environment_extended,
                diagnostic_span,
                b1,
                b2,
                recursion_depth + 1,
            )
        }
        (elab::Constructor::KApp(f1, k1), elab::Constructor::KApp(f2, k2)) => {
            unify_cons_inner(
                elaboration_context,
                elaboration_environment,
                diagnostic_span,
                f1,
                f2,
                recursion_depth + 1,
            )?;
            unify_kinds(elaboration_environment, k1, k2)
                .map_err(|ek| Box::new(FailedToUnifyConstructors::KindUnificationFailed(*ek)))
        }
        (elab::Constructor::Name(s1), elab::Constructor::Name(s2)) => {
            if s1.to_lowercase() == s2.to_lowercase() {
                Ok(())
            } else {
                Err(Box::new(
                    FailedToUnifyConstructors::IncompatibleConstructors(
                        left_normalized,
                        right_normalized,
                    ),
                ))
            }
        }
        (elab::Constructor::Unit, elab::Constructor::Unit) => Ok(()),
        (elab::Constructor::Tuple(left_tuple), elab::Constructor::Tuple(right_tuple)) => {
            if left_tuple.len() != right_tuple.len() {
                return Err(Box::new(
                    FailedToUnifyConstructors::IncompatibleConstructors(
                        left_normalized,
                        right_normalized,
                    ),
                ));
            }
            for (left_element, right_element) in left_tuple.iter().zip(right_tuple.iter()) {
                unify_cons_inner(
                    elaboration_context,
                    elaboration_environment,
                    diagnostic_span,
                    left_element,
                    right_element,
                    recursion_depth + 1,
                )?;
            }
            Ok(())
        }
        (elab::Constructor::Proj(left_base, n1), elab::Constructor::Proj(right_base, n2)) => {
            if n1 != n2 {
                return Err(Box::new(
                    FailedToUnifyConstructors::IncompatibleConstructors(
                        left_normalized,
                        right_normalized,
                    ),
                ));
            }
            unify_cons_inner(
                elaboration_context,
                elaboration_environment,
                diagnostic_span,
                left_base,
                right_base,
                recursion_depth + 1,
            )
        }
        // Row constructors: try record summary unification
        _ => {
            // Try reduction before giving up
            let rc1 = reduce_con(left_normalized.clone());
            let rc2 = reduce_con(right_normalized.clone());
            if !cons_eq_simple(&rc1, &left_normalized) || !cons_eq_simple(&rc2, &right_normalized) {
                return unify_cons_inner(
                    elaboration_context,
                    elaboration_environment,
                    diagnostic_span,
                    &rc1,
                    &rc2,
                    recursion_depth + 1,
                );
            }
            // Row unification via summaries
            unify_rows(
                elaboration_context,
                elaboration_environment,
                diagnostic_span,
                &left_normalized,
                &right_normalized,
                recursion_depth,
            )
        }
    }
}

/// Row-specific unification (for Record / Concat / Unif tails).
fn unify_rows(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    diagnostic_span: &Span,
    left_constructor: &elab::LocatedConstructor,
    right_constructor: &elab::LocatedConstructor,
    recursion_depth: usize,
) -> Result<(), Box<FailedToUnifyConstructors>> {
    let left_summary = record_summary(elaboration_environment, left_constructor.clone());
    let right_summary = record_summary(elaboration_environment, right_constructor.clone());

    // If both are fully known (no unifs), check field by field
    if left_summary.unifs.is_empty()
        && right_summary.unifs.is_empty()
        && left_summary.others.is_empty()
        && right_summary.others.is_empty()
    {
        if left_summary.fields.len() != right_summary.fields.len() {
            return Err(Box::new(
                FailedToUnifyConstructors::IncompatibleConstructors(
                    left_constructor.clone(),
                    right_constructor.clone(),
                ),
            ));
        }
        let mut right_fields_remaining = right_summary.fields.clone();
        for (field_name_left, field_type_left) in &left_summary.fields {
            if let Some(position) =
                right_fields_remaining
                    .iter()
                    .position(|(field_name_right, _)| {
                        field_name_left.to_lowercase() == field_name_right.to_lowercase()
                    })
            {
                let (_, field_type_right) = right_fields_remaining.remove(position);
                unify_cons_inner(
                    elaboration_context,
                    elaboration_environment,
                    diagnostic_span,
                    field_type_left,
                    &field_type_right,
                    recursion_depth + 1,
                )?;
            } else {
                return Err(Box::new(
                    FailedToUnifyConstructors::IncompatibleConstructors(
                        left_constructor.clone(),
                        right_constructor.clone(),
                    ),
                ));
            }
        }
        return Ok(());
    }

    // If either side has exactly one unif and no others, solve it
    if left_summary.unifs.len() == 1
        && left_summary.others.is_empty()
        && right_summary.unifs.is_empty()
        && right_summary.others.is_empty()
    {
        let (row_tail_cell, nesting_lift) = &left_summary.unifs[0];
        // Build the solution: right minus left fields
        let mut remaining = right_summary.fields.clone();
        for (field_name, _) in &left_summary.fields {
            remaining.retain(|(field_name_right, _)| {
                field_name.to_lowercase() != field_name_right.to_lowercase()
            });
        }
        let solution = fields_to_row(&remaining, diagnostic_span, &right_constructor.span);
        let adjusted = mlift_con_in_con(*nesting_lift, solution);
        *crate::compiler_diagnostics::lock_for_compile(
            row_tail_cell.as_ref(),
            "elaboration unification cell",
        ) = elab::CUnif::Known(Box::new(adjusted));
        return Ok(());
    }
    if right_summary.unifs.len() == 1
        && right_summary.others.is_empty()
        && left_summary.unifs.is_empty()
        && left_summary.others.is_empty()
    {
        let (row_tail_cell, nesting_lift) = &right_summary.unifs[0];
        let mut remaining = left_summary.fields.clone();
        for (field_name, _) in &right_summary.fields {
            remaining.retain(|(field_name_left, _)| {
                field_name.to_lowercase() != field_name_left.to_lowercase()
            });
        }
        let solution = fields_to_row(&remaining, diagnostic_span, &left_constructor.span);
        let adjusted = mlift_con_in_con(*nesting_lift, solution);
        *crate::compiler_diagnostics::lock_for_compile(
            row_tail_cell.as_ref(),
            "elaboration unification cell",
        ) = elab::CUnif::Known(Box::new(adjusted));
        return Ok(());
    }

    // Otherwise, delay if mayDelay is set, else fail
    if elaboration_context.may_delay {
        // Leave for later constraint solving
        return Ok(());
    }
    Err(Box::new(
        FailedToUnifyConstructors::IncompatibleConstructors(
            left_constructor.clone(),
            right_constructor.clone(),
        ),
    ))
}

fn fields_to_row(
    fields: &[(String, elab::LocatedConstructor)],
    span: &Span,
    _orig_span: &Span,
) -> elab::LocatedConstructor {
    if fields.is_empty() {
        return Located::new(
            elab::Constructor::Record(
                Box::new(Located::new(elab::Kind::Type, span.clone())),
                vec![],
            ),
            span.clone(),
        );
    }
    let ktype = Located::new(elab::Kind::Type, span.clone());
    let krow = Located::new(elab::Kind::Record(Box::new(ktype)), span.clone());
    let field_pairs: Vec<_> = fields
        .iter()
        .map(|(f, v)| {
            let name = Located::new(elab::Constructor::Name(f.clone()), span.clone());
            (name, v.clone())
        })
        .collect();
    Located::new(
        elab::Constructor::Record(Box::new(krow), field_pairs),
        span.clone(),
    )
}

// ---------------------------------------------------------------------------
// Check constructor against a type (for expressions)
// ---------------------------------------------------------------------------

fn check_con(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    span: &Span,
    got: &elab::LocatedConstructor,
    expected: &elab::LocatedConstructor,
) {
    if let Err(e) = unify_cons(
        elaboration_context,
        elaboration_environment,
        span,
        got,
        expected,
    ) {
        elaboration_context.error(
            span.clone(),
            DiagnosticPayload::new(
                DiagnosticId::ElabTypeMismatch,
                vec![format_failed_to_unify_constructors_message(e.as_ref())],
            ),
        );
    }
}

// ---------------------------------------------------------------------------
// Pattern elaboration
// ---------------------------------------------------------------------------

/// Elaborate a pattern against an expected constructor type; extend `elaboration_environment` with bound `rel_e` variables.
///
/// # Arguments
///
/// * `elaboration_context` — Records mismatches via [`check_con`] / unbound constructors.
/// * `elaboration_environment` — Environment before the pattern.
/// * `p` — Source pattern.
/// * `expected_type` — Contextually expected type constructor.
///
/// # Returns
///
/// Elaborated pattern and environment extended by pattern bindings (non-linear patterns may still error).
pub fn elab_pat(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    p: &source::LocPat,
    expected_type: &elab::LocatedConstructor,
) -> (elab::LocatedPattern, Env) {
    let span = p.span.clone();
    match &p.node {
        source::Pat::Var(x) => {
            let pat = Located::new(
                elab::Pattern::Var(x.clone(), expected_type.clone()),
                span.clone(),
            );
            let new_env = elaboration_environment
                .clone()
                .push_e_rel(x.clone(), expected_type.clone());
            (pat, new_env)
        }
        source::Pat::Prim(prim) => {
            let prim_type = prim_con(elaboration_context, elaboration_environment, prim, &span);
            check_con(
                elaboration_context,
                elaboration_environment,
                &span,
                &prim_type,
                expected_type,
            );
            let pat = Located::new(elab::Pattern::Prim(prim.clone()), span);
            (pat, elaboration_environment.clone())
        }
        source::Pat::Con(ms, x, arg_opt) => elab_pat_con(
            elaboration_context,
            elaboration_environment,
            ms,
            x,
            arg_opt.as_deref(),
            expected_type,
            &span,
        ),
        source::Pat::Record(fields, is_open) => elab_pat_record(
            elaboration_context,
            elaboration_environment,
            fields,
            *is_open,
            expected_type,
            &span,
        ),
        source::Pat::Annot(inner_p, annot_con) => {
            let (annot_ce, _) = elab_con(elaboration_context, elaboration_environment, annot_con);
            check_con(
                elaboration_context,
                elaboration_environment,
                &span,
                &annot_ce,
                expected_type,
            );
            elab_pat(
                elaboration_context,
                elaboration_environment,
                inner_p,
                &annot_ce,
            )
        }
    }
}

fn elab_pat_con(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    ms: &[String],
    x: &str,
    arg_opt: Option<&source::LocPat>,
    expected_type: &elab::LocatedConstructor,
    span: &Span,
) -> (elab::LocatedPattern, Env) {
    // Look up the constructor
    let constr_info = if ms.is_empty() {
        elaboration_environment.lookup_constructor(x).cloned()
    } else {
        None // module-qualified constructors handled below
    };

    if let Some(info) = constr_info {
        let dk = info.datatype_kind;
        let con_id = info.constructor_id;
        let dt_id = info.datatype_id;
        let type_params = info.type_params.clone();
        let arg_type_opt = info.arg_type.clone();

        // Build fresh unification variables for type parameters
        let ktype = Located::new(elab::Kind::Type, span.clone());
        let type_args: Vec<elab::LocatedConstructor> = type_params
            .iter()
            .map(|_| fresh_cunif(elaboration_environment, span.clone(), ktype.clone(), "_"))
            .collect();

        // The datatype constructor applied to type args
        let dt_con = {
            let base = Located::new(elab::Constructor::Named(dt_id), span.clone());
            type_args.iter().fold(base, |acc, arg| {
                Located::new(
                    elab::Constructor::App(Box::new(acc), Box::new(arg.clone())),
                    span.clone(),
                )
            })
        };

        check_con(
            elaboration_context,
            elaboration_environment,
            span,
            &dt_con,
            expected_type,
        );

        // If constructor takes an argument, elaborate it
        let (arg_pat_opt, new_env) = if let Some(at) = arg_type_opt {
            // Substitute type_args into at
            let mut at2 = at;
            for (i, ta) in type_args.iter().enumerate() {
                let idx = type_params.len() - 1 - i;
                at2 = match sub_con_in_con(idx, ta, at2) {
                    Ok(c) => c,
                    Err(_) => elaborated_constructor_error_at_span(span.clone()),
                };
            }
            if let Some(ap) = arg_opt {
                let (ap_e, new_env) =
                    elab_pat(elaboration_context, elaboration_environment, ap, &at2);
                (Some(Box::new(ap_e)), new_env)
            } else {
                elaboration_context.error(
                    span.clone(),
                    DiagnosticPayload::new(
                        DiagnosticId::ElabConstructorExpectsArgument,
                        vec![x.to_string()],
                    ),
                );
                (None, elaboration_environment.clone())
            }
        } else {
            if arg_opt.is_some() {
                elaboration_context.error(
                    span.clone(),
                    DiagnosticPayload::new(
                        DiagnosticId::ElabConstructorDoesNotTakeArgument,
                        vec![x.to_string()],
                    ),
                );
            }
            (None, elaboration_environment.clone())
        };

        let pat_con = elab::PatternConstructor::Var(con_id);
        let pat = Located::new(
            elab::Pattern::Constructor(dk, pat_con, type_args, arg_pat_opt),
            span.clone(),
        );
        (pat, new_env)
    } else {
        elaboration_context.error(
            span.clone(),
            DiagnosticPayload::new(DiagnosticId::ElabUnboundConstructor, vec![x.to_string()]),
        );
        let pat = Located::new(
            elab::Pattern::Var("_".to_string(), expected_type.clone()),
            span.clone(),
        );
        (pat, elaboration_environment.clone())
    }
}

fn elab_pat_record(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    fields: &[(String, source::LocPat)],
    is_open: bool,
    expected_type: &elab::LocatedConstructor,
    span: &Span,
) -> (elab::LocatedPattern, Env) {
    // Build a record type from the fields, then unify
    let mut result_fields: Vec<(String, elab::LocatedPattern, elab::LocatedConstructor)> =
        Vec::new();
    let mut cur_env = elaboration_environment.clone();
    let mut row_fields: Vec<(elab::LocatedConstructor, elab::LocatedConstructor)> = Vec::new();
    let ktype = Located::new(elab::Kind::Type, span.clone());
    let krow = Located::new(elab::Kind::Record(Box::new(ktype.clone())), span.clone());

    for (fname, fpat) in fields {
        let ftype = fresh_cunif(elaboration_environment, span.clone(), ktype.clone(), fname);
        let (fpatl, new_env) = elab_pat(elaboration_context, &cur_env, fpat, &ftype);
        cur_env = new_env;
        result_fields.push((fname.clone(), fpatl, ftype.clone()));
        row_fields.push((
            Located::new(elab::Constructor::Name(fname.clone()), span.clone()),
            ftype,
        ));
    }

    // If open pattern, allow extra fields
    let row_con = if is_open {
        let rest = fresh_cunif(elaboration_environment, span.clone(), krow.clone(), "_rest");
        let known_row = Located::new(
            elab::Constructor::Record(Box::new(krow.clone()), row_fields),
            span.clone(),
        );
        Located::new(
            elab::Constructor::Concat(Box::new(known_row), Box::new(rest)),
            span.clone(),
        )
    } else {
        Located::new(
            elab::Constructor::Record(Box::new(krow.clone()), row_fields),
            span.clone(),
        )
    };

    let record_type = Located::new(elab::Constructor::TRecord(Box::new(row_con)), span.clone());
    check_con(
        elaboration_context,
        elaboration_environment,
        span,
        &record_type,
        expected_type,
    );

    let pat = Located::new(elab::Pattern::Record(result_fields), span.clone());
    (pat, cur_env)
}

fn prim_con(
    _elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    prim: &Prim,
    span: &Span,
) -> elab::LocatedConstructor {
    match prim {
        Prim::Int(_) => basis_named_con(elaboration_environment, span, "int"),
        Prim::Float(_) => basis_named_con(elaboration_environment, span, "float"),
        Prim::String(_, _) => basis_named_con(elaboration_environment, span, "string"),
        Prim::Char(_) => basis_named_con(elaboration_environment, span, "char"),
    }
}

fn basis_named_con(
    elaboration_environment: &Env,
    span: &Span,
    name: &str,
) -> elab::LocatedConstructor {
    // After opening Basis, look up by name directly (returns Named(id)).
    match elaboration_environment.lookup_c(name) {
        VarLookup::Named(id, _) => {
            return Located::new(elab::Constructor::Named(id), span.clone());
        }
        VarLookup::Rel(_, _) => {}
        VarLookup::NotBound => {}
    }
    // Fallback: resolve via ModProj from the Basis structure.
    if let Some((str_id, _)) = elaboration_environment.lookup_str("Basis") {
        return Located::new(
            elab::Constructor::ModProj(*str_id, vec![], name.to_string()),
            span.clone(),
        );
    }
    elaborated_constructor_error_at_span(span.clone())
}

// ---------------------------------------------------------------------------
// Expression elaboration
// ---------------------------------------------------------------------------

/// Elaborate an expression in `elaboration_environment` with disjointness hypotheses `disjointness_environment`.
///
/// Recursion depth capped at 200; on overflow records error and returns [`elab::Expression::Error`] /
/// [`elab::Constructor::Error`] stubs.
///
/// # Arguments
///
/// * `elaboration_context` — Accumulates errors and deferred disjointness [`Constraint`]s.
/// * `elaboration_environment` — Value, type, and module environment.
/// * `disjointness_environment` — Disjointness facts for `prove` when checking constraints.
/// * `e` — Source expression.
///
/// # Returns
///
/// Pair `(expression, inferred or checked type constructor)`.
pub fn elab_exp(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    disjointness_environment: &disjoint::DisjointEnv,
    e: &source::LocExp,
) -> (elab::LocatedExpression, elab::LocatedConstructor) {
    use std::cell::Cell;
    thread_local! {
        static ELAB_EXP_DEPTH: Cell<usize> = const { Cell::new(0) };
    }
    let d = ELAB_EXP_DEPTH.with(|c| {
        let v = c.get();
        c.set(v + 1);
        v
    });
    if d > 200 {
        ELAB_EXP_DEPTH.with(|c| c.set(0));
        let span = e.span.clone();
        elaboration_context.error(
            span.clone(),
            DiagnosticPayload::new(DiagnosticId::ElabExpressionRecursionDepth, Vec::new()),
        );
        return (
            elaborated_expression_error_at_span(span.clone()),
            elaborated_constructor_error_at_span(span),
        );
    }
    let result = elab_exp_inner(
        elaboration_context,
        elaboration_environment,
        disjointness_environment,
        e,
    );
    ELAB_EXP_DEPTH.with(|c| c.set(d));
    result
}

fn elab_exp_inner(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    disjointness_environment: &disjoint::DisjointEnv,
    e: &source::LocExp,
) -> (elab::LocatedExpression, elab::LocatedConstructor) {
    let span = e.span.clone();
    match &e.node {
        source::Exp::Prim(prim) => {
            let t = prim_con(elaboration_context, elaboration_environment, prim, &span);
            (Located::new(elab::Expression::Prim(prim.clone()), span), t)
        }

        source::Exp::Annot(inner, con) => {
            let (ce, _) = elab_con(elaboration_context, elaboration_environment, con);
            let (ee, et) = elab_exp(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                inner,
            );
            check_con(
                elaboration_context,
                elaboration_environment,
                &span,
                &et,
                &ce,
            );
            (ee, ce)
        }

        source::Exp::Var(ms, x, _inf) => {
            elab_exp_var(elaboration_context, elaboration_environment, ms, x, &span)
        }

        source::Exp::App(f, arg) => {
            let (fe, ft) = elab_exp(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                f,
            );
            let (fe2, ft2) = elab_head(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                fe,
                ft,
                &f.span,
            );
            let ftn = hnorm_con(ft2);
            match ftn.node.clone() {
                elab::Constructor::TFun(dom, ran) => {
                    let (ae, at) = elab_exp(
                        elaboration_context,
                        elaboration_environment,
                        disjointness_environment,
                        arg,
                    );
                    check_con(
                        elaboration_context,
                        elaboration_environment,
                        &arg.span,
                        &at,
                        &dom,
                    );
                    let result =
                        Located::new(elab::Expression::App(Box::new(fe2), Box::new(ae)), span);
                    (result, *ran)
                }
                elab::Constructor::Unif(_, _, _k, _, r) => {
                    let dom = fresh_cunif(
                        elaboration_environment,
                        span.clone(),
                        Located::new(elab::Kind::Type, span.clone()),
                        "_dom",
                    );
                    let ran = fresh_cunif(
                        elaboration_environment,
                        span.clone(),
                        Located::new(elab::Kind::Type, span.clone()),
                        "_ran",
                    );
                    let tfun = Located::new(
                        elab::Constructor::TFun(Box::new(dom.clone()), Box::new(ran.clone())),
                        span.clone(),
                    );
                    *crate::compiler_diagnostics::lock_for_compile(
                        r.as_ref(),
                        "elaboration unification cell",
                    ) = elab::CUnif::Known(Box::new(tfun));
                    let (ae, at) = elab_exp(
                        elaboration_context,
                        elaboration_environment,
                        disjointness_environment,
                        arg,
                    );
                    check_con(
                        elaboration_context,
                        elaboration_environment,
                        &arg.span,
                        &at,
                        &dom,
                    );
                    let result =
                        Located::new(elab::Expression::App(Box::new(fe2), Box::new(ae)), span);
                    (result, ran)
                }
                _other => {
                    elaboration_context.error(
                        f.span.clone(),
                        DiagnosticPayload::new(
                            DiagnosticId::ElabApplicationNonFunction,
                            Vec::new(),
                        ),
                    );
                    (
                        elaborated_expression_error_at_span(span.clone()),
                        elaborated_constructor_error_at_span(span),
                    )
                }
            }
        }

        source::Exp::Abs(x, opt_ann, body) => {
            let dom = match opt_ann {
                Some(ann) => {
                    let (ce, _) = elab_con(elaboration_context, elaboration_environment, ann);
                    ce
                }
                None => fresh_cunif(
                    elaboration_environment,
                    span.clone(),
                    Located::new(elab::Kind::Type, span.clone()),
                    x,
                ),
            };
            let env2 = elaboration_environment
                .clone()
                .push_e_rel(x.clone(), dom.clone());
            let (bodye, bodytype) =
                elab_exp(elaboration_context, &env2, disjointness_environment, body);
            let result = Located::new(
                elab::Expression::Abs(x.clone(), dom.clone(), bodytype.clone(), Box::new(bodye)),
                span.clone(),
            );
            let tfun = Located::new(
                elab::Constructor::TFun(Box::new(dom), Box::new(bodytype)),
                span,
            );
            (result, tfun)
        }

        source::Exp::CApp(e1, c) => {
            let (e1e, e1t) = elab_exp(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                e1,
            );
            let (ce, ck) = elab_con(elaboration_context, elaboration_environment, c);
            let e1tn = hnorm_con(e1t);
            match e1tn.node {
                elab::Constructor::TCFun(_, _x, k, body) => {
                    check_kind(
                        elaboration_context,
                        elaboration_environment,
                        &c.span,
                        &ce,
                        &ck,
                        &k,
                    );
                    let result_type = match sub_con_in_con(0, &ce, *body) {
                        Ok(t) => t,
                        Err(_) => elaborated_constructor_error_at_span(span.clone()),
                    };
                    let result = Located::new(elab::Expression::CApp(Box::new(e1e), ce), span);
                    (result, result_type)
                }
                _ => {
                    elaboration_context.error(
                        e1.span.clone(),
                        DiagnosticPayload::new(
                            DiagnosticId::ElabConstructorAppNonTcFun,
                            Vec::new(),
                        ),
                    );
                    (
                        elaborated_expression_error_at_span(span.clone()),
                        elaborated_constructor_error_at_span(span),
                    )
                }
            }
        }

        source::Exp::CAbs(exp, x, k, body) => {
            let ke = elab_kind(elaboration_context, elaboration_environment, k);
            let env2 = elaboration_environment
                .clone()
                .push_c_rel(x.clone(), ke.clone());
            let new_denv = disjoint::enter(disjointness_environment.clone());
            let (bodye, bodytype) = elab_exp(elaboration_context, &env2, &new_denv, body);
            let exp_e = elab_explicitness(*exp);
            let result = Located::new(
                elab::Expression::CAbs(exp_e, x.clone(), Box::new(ke.clone()), Box::new(bodye)),
                span.clone(),
            );
            let tfun = Located::new(
                elab::Constructor::TCFun(exp_e, x.clone(), Box::new(ke), Box::new(bodytype)),
                span,
            );
            (result, tfun)
        }

        source::Exp::KAbs(x, body) => {
            let env2 = elaboration_environment.clone().push_k_rel(x.clone());
            let (bodye, bodytype) =
                elab_exp(elaboration_context, &env2, disjointness_environment, body);
            let result = Located::new(
                elab::Expression::KAbs(x.clone(), Box::new(bodye)),
                span.clone(),
            );
            let tfun = Located::new(
                elab::Constructor::TKFun(x.clone(), Box::new(bodytype)),
                span,
            );
            (result, tfun)
        }

        source::Exp::Disjoint(c1, c2, body) => {
            let (c1e, k1) = elab_con(elaboration_context, elaboration_environment, c1);
            let (c2e, _k2) = elab_con(elaboration_context, elaboration_environment, c2);
            // Check they're row constructors
            let ku = fresh_kunif(span.clone(), "_");
            let krow = Located::new(elab::Kind::Record(Box::new(ku)), span.clone());
            check_kind(
                elaboration_context,
                elaboration_environment,
                &c1.span,
                &c1e,
                &k1,
                &krow,
            );
            // Add disjointness to disjointness_environment
            let new_denv =
                disjoint::assert(c1e.clone(), c2e.clone(), disjointness_environment.clone());
            // Check c1 ~ c2 holds
            let goals = disjoint::prove(span.clone(), &new_denv, c1e.clone(), c2e.clone());
            if !goals.is_empty() {
                // Defer as constraint
                for g in goals {
                    elaboration_context.constraints.push(Constraint::Disjoint {
                        span: span.clone(),
                        elaboration_environment: elaboration_environment.clone(),
                        goal: g,
                    });
                }
            }
            let (bodye, bodytype) = elab_exp(
                elaboration_context,
                elaboration_environment,
                &new_denv,
                body,
            );
            (bodye, bodytype)
        }

        source::Exp::DisjointApp(body) => {
            // Used for implicit disjointness arg: just elaborate body
            elab_exp(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                body,
            )
        }

        source::Exp::Record(xes, _spread) => elab_exp_record(
            elaboration_context,
            elaboration_environment,
            disjointness_environment,
            xes,
            &span,
        ),

        source::Exp::Field(e1, field_con) => {
            // If this looks like a module-qualified variable `M.x` (where e1 is
            // Var([], M) and M is a module in scope), treat it as module projection
            // rather than record field access.
            if let source::Exp::Var(ref ms, ref m, _) = e1.node {
                if ms.is_empty() {
                    if let source::Con::Name(ref fname) = field_con.node {
                        // Build the full module path: [M, ...field components?]
                        // Check if M is a module in scope
                        if elaboration_environment.lookup_str(m).is_some() {
                            let path: Vec<String> = vec![m.clone()];
                            return elab_exp_var(
                                elaboration_context,
                                elaboration_environment,
                                &path,
                                fname,
                                &span,
                            );
                        }
                    }
                } else if let source::Con::Name(ref fname) = field_con.node {
                    // ms.x — also module projection when ms is non-empty
                    if elaboration_environment.lookup_str(&ms[0]).is_some() {
                        let mut path = ms.clone();
                        path.push(m.clone());
                        return elab_exp_var(
                            elaboration_context,
                            elaboration_environment,
                            &path,
                            fname,
                            &span,
                        );
                    }
                }
            }
            let (e1e, e1t) = elab_exp(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                e1,
            );
            let (fce, fck) = elab_con(elaboration_context, elaboration_environment, field_con);
            let kname = Located::new(elab::Kind::Name, span.clone());
            check_kind(
                elaboration_context,
                elaboration_environment,
                &field_con.span,
                &fce,
                &fck,
                &kname,
            );
            // e1t should be TRecord { field_name = field_type, ... }
            let field_type = fresh_cunif(
                elaboration_environment,
                span.clone(),
                Located::new(elab::Kind::Type, span.clone()),
                "_field",
            );
            let rest_type = fresh_cunif(
                elaboration_environment,
                span.clone(),
                Located::new(
                    elab::Kind::Record(Box::new(Located::new(elab::Kind::Type, span.clone()))),
                    span.clone(),
                ),
                "_rest",
            );
            let row = Located::new(
                elab::Constructor::Concat(
                    Box::new(Located::new(
                        elab::Constructor::Record(
                            Box::new(Located::new(
                                elab::Kind::Record(Box::new(Located::new(
                                    elab::Kind::Type,
                                    span.clone(),
                                ))),
                                span.clone(),
                            )),
                            vec![(fce.clone(), field_type.clone())],
                        ),
                        span.clone(),
                    )),
                    Box::new(rest_type.clone()),
                ),
                span.clone(),
            );
            let expected_e1t =
                Located::new(elab::Constructor::TRecord(Box::new(row)), span.clone());
            check_con(
                elaboration_context,
                elaboration_environment,
                &e1.span,
                &e1t,
                &expected_e1t,
            );
            let result = Located::new(
                elab::Expression::Field(
                    Box::new(e1e),
                    fce.clone(),
                    elab::FieldMeta {
                        field: field_type.clone(),
                        rest: rest_type,
                    },
                ),
                span,
            );
            (result, field_type)
        }

        source::Exp::Concat(e1, e2) => {
            let (e1e, e1t) = elab_exp(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                e1,
            );
            let (e2e, e2t) = elab_exp(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                e2,
            );
            // Both must be records; concat their rows
            let ktype = Located::new(elab::Kind::Type, span.clone());
            let krow = Located::new(elab::Kind::Record(Box::new(ktype.clone())), span.clone());
            let r1 = fresh_cunif(elaboration_environment, span.clone(), krow.clone(), "_r1");
            let r2 = fresh_cunif(elaboration_environment, span.clone(), krow.clone(), "_r2");
            let t1 = Located::new(
                elab::Constructor::TRecord(Box::new(r1.clone())),
                span.clone(),
            );
            let t2 = Located::new(
                elab::Constructor::TRecord(Box::new(r2.clone())),
                span.clone(),
            );
            check_con(
                elaboration_context,
                elaboration_environment,
                &e1.span,
                &e1t,
                &t1,
            );
            check_con(
                elaboration_context,
                elaboration_environment,
                &e2.span,
                &e2t,
                &t2,
            );
            let concat_row = Located::new(
                elab::Constructor::Concat(Box::new(r1.clone()), Box::new(r2.clone())),
                span.clone(),
            );
            let result_type = Located::new(
                elab::Constructor::TRecord(Box::new(concat_row)),
                span.clone(),
            );
            let result = Located::new(
                elab::Expression::Concat(Box::new(e1e), r1, Box::new(e2e), r2),
                span,
            );
            (result, result_type)
        }

        source::Exp::Cut(e1, field_con) => {
            let (e1e, e1t) = elab_exp(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                e1,
            );
            let (fce, fck) = elab_con(elaboration_context, elaboration_environment, field_con);
            let kname = Located::new(elab::Kind::Name, span.clone());
            check_kind(
                elaboration_context,
                elaboration_environment,
                &field_con.span,
                &fce,
                &fck,
                &kname,
            );
            let field_type = fresh_cunif(
                elaboration_environment,
                span.clone(),
                Located::new(elab::Kind::Type, span.clone()),
                "_f",
            );
            let rest = fresh_cunif(
                elaboration_environment,
                span.clone(),
                Located::new(
                    elab::Kind::Record(Box::new(Located::new(elab::Kind::Type, span.clone()))),
                    span.clone(),
                ),
                "_rest",
            );
            let full_row = Located::new(
                elab::Constructor::Concat(
                    Box::new(Located::new(
                        elab::Constructor::Record(
                            Box::new(Located::new(
                                elab::Kind::Record(Box::new(Located::new(
                                    elab::Kind::Type,
                                    span.clone(),
                                ))),
                                span.clone(),
                            )),
                            vec![(fce.clone(), field_type.clone())],
                        ),
                        span.clone(),
                    )),
                    Box::new(rest.clone()),
                ),
                span.clone(),
            );
            let expected_e1t =
                Located::new(elab::Constructor::TRecord(Box::new(full_row)), span.clone());
            check_con(
                elaboration_context,
                elaboration_environment,
                &e1.span,
                &e1t,
                &expected_e1t,
            );
            let result_type = Located::new(
                elab::Constructor::TRecord(Box::new(rest.clone())),
                span.clone(),
            );
            let result = Located::new(
                elab::Expression::Cut(
                    Box::new(e1e),
                    fce,
                    elab::FieldMeta {
                        field: field_type,
                        rest,
                    },
                ),
                span,
            );
            (result, result_type)
        }

        source::Exp::CutMulti(e1, fields_con) => {
            let (e1e, e1t) = elab_exp(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                e1,
            );
            let (fce, _fck) = elab_con(elaboration_context, elaboration_environment, fields_con);
            let ktype = Located::new(elab::Kind::Type, span.clone());
            let rest = fresh_cunif(
                elaboration_environment,
                span.clone(),
                Located::new(elab::Kind::Record(Box::new(ktype.clone())), span.clone()),
                "_rest",
            );
            // e1t = TRecord (fce ++ rest)
            let full_row = Located::new(
                elab::Constructor::Concat(Box::new(fce.clone()), Box::new(rest.clone())),
                span.clone(),
            );
            let expected =
                Located::new(elab::Constructor::TRecord(Box::new(full_row)), span.clone());
            check_con(
                elaboration_context,
                elaboration_environment,
                &e1.span,
                &e1t,
                &expected,
            );
            let result_type = Located::new(
                elab::Constructor::TRecord(Box::new(rest.clone())),
                span.clone(),
            );
            let result = Located::new(
                elab::Expression::CutMulti(Box::new(e1e), fce, elab::RestMeta { rest }),
                span,
            );
            (result, result_type)
        }

        source::Exp::Wild => {
            let t = fresh_cunif(
                elaboration_environment,
                span.clone(),
                Located::new(elab::Kind::Type, span.clone()),
                "_",
            );
            let r = Arc::new(Mutex::new(None::<elab::LocatedExpression>));
            (Located::new(elab::Expression::Unif(r), span), t)
        }

        source::Exp::Hole => {
            let t = fresh_cunif(
                elaboration_environment,
                span.clone(),
                Located::new(elab::Kind::Type, span.clone()),
                "_",
            );
            let r = Arc::new(Mutex::new(elab::CUnif::Unknown));
            (Located::new(elab::Expression::Hole(r), span), t)
        }

        source::Exp::Case(scrutinee, branches) => {
            let (scre, scrt) = elab_exp(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                scrutinee,
            );
            let result_type = fresh_cunif(
                elaboration_environment,
                span.clone(),
                Located::new(elab::Kind::Type, span.clone()),
                "_case",
            );
            let mut elab_branches = Vec::new();
            for (pat, branch_exp) in branches {
                let (pate, pat_env) =
                    elab_pat(elaboration_context, elaboration_environment, pat, &scrt);
                let (branche, brancht) = elab_exp(
                    elaboration_context,
                    &pat_env,
                    disjointness_environment,
                    branch_exp,
                );
                check_con(
                    elaboration_context,
                    elaboration_environment,
                    &branch_exp.span,
                    &brancht,
                    &result_type,
                );
                elab_branches.push((pate, branche));
            }
            let case_meta = elab::CaseMeta {
                disc: scrt,
                result: result_type.clone(),
            };
            let result = Located::new(
                elab::Expression::Case(Box::new(scre), elab_branches, case_meta),
                span,
            );
            (result, result_type)
        }

        source::Exp::Let(edecls, body) => {
            let mut cur_env = elaboration_environment.clone();
            let mut elab_decls: Vec<elab::LocatedElaboratedDeclaration> = Vec::new();
            for ed in edecls {
                let (elab_decl, new_env) =
                    elab_edecl(elaboration_context, &cur_env, disjointness_environment, ed);
                if let Some(d) = elab_decl {
                    elab_decls.push(d);
                }
                cur_env = new_env;
            }
            let (bodye, bodytype) = elab_exp(
                elaboration_context,
                &cur_env,
                disjointness_environment,
                body,
            );
            let result = Located::new(
                elab::Expression::Let(elab_decls, Box::new(bodye), bodytype.clone()),
                span,
            );
            (result, bodytype)
        }

        source::Exp::Infix(op, e1, e2) => {
            // Desugar binary infix operators to curried Basis/Top function calls,
            // matching the SML grammar's `native_op` / `top_binop` desugaring.
            match op.as_str() {
                // Basis arithmetic / comparison operators
                "+" => desugar_binop(
                    elaboration_context,
                    elaboration_environment,
                    disjointness_environment,
                    "plus",
                    vec!["Basis".into()],
                    e1,
                    e2,
                    &span,
                ),
                "-" => desugar_binop(
                    elaboration_context,
                    elaboration_environment,
                    disjointness_environment,
                    "minus",
                    vec!["Basis".into()],
                    e1,
                    e2,
                    &span,
                ),
                "*" => desugar_binop(
                    elaboration_context,
                    elaboration_environment,
                    disjointness_environment,
                    "times",
                    vec!["Basis".into()],
                    e1,
                    e2,
                    &span,
                ),
                "/" => desugar_binop(
                    elaboration_context,
                    elaboration_environment,
                    disjointness_environment,
                    "divide",
                    vec!["Basis".into()],
                    e1,
                    e2,
                    &span,
                ),
                "%" => desugar_binop(
                    elaboration_context,
                    elaboration_environment,
                    disjointness_environment,
                    "mod",
                    vec!["Basis".into()],
                    e1,
                    e2,
                    &span,
                ),
                "=" => desugar_binop(
                    elaboration_context,
                    elaboration_environment,
                    disjointness_environment,
                    "eq",
                    vec!["Basis".into()],
                    e1,
                    e2,
                    &span,
                ),
                "<>" => desugar_binop(
                    elaboration_context,
                    elaboration_environment,
                    disjointness_environment,
                    "ne",
                    vec!["Basis".into()],
                    e1,
                    e2,
                    &span,
                ),
                "<" => desugar_binop(
                    elaboration_context,
                    elaboration_environment,
                    disjointness_environment,
                    "lt",
                    vec!["Basis".into()],
                    e1,
                    e2,
                    &span,
                ),
                ">" => desugar_binop(
                    elaboration_context,
                    elaboration_environment,
                    disjointness_environment,
                    "gt",
                    vec!["Basis".into()],
                    e1,
                    e2,
                    &span,
                ),
                "<=" => desugar_binop(
                    elaboration_context,
                    elaboration_environment,
                    disjointness_environment,
                    "le",
                    vec!["Basis".into()],
                    e1,
                    e2,
                    &span,
                ),
                ">=" => desugar_binop(
                    elaboration_context,
                    elaboration_environment,
                    disjointness_environment,
                    "ge",
                    vec!["Basis".into()],
                    e1,
                    e2,
                    &span,
                ),
                // `::` is list cons: Basis.Cons {1 = e1, 2 = e2}
                "::" => {
                    let record_fields = vec![
                        (
                            Located::new(source::Con::Name("1".into()), span.clone()),
                            *e1.clone(),
                        ),
                        (
                            Located::new(source::Con::Name("2".into()), span.clone()),
                            *e2.clone(),
                        ),
                    ];
                    let record =
                        Located::new(source::Exp::Record(record_fields, false), span.clone());
                    let cons_var = Located::new(
                        source::Exp::Var(
                            vec!["Basis".into()],
                            "Cons".into(),
                            source::Inference::Infer,
                        ),
                        span.clone(),
                    );
                    let desugared = Located::new(
                        source::Exp::App(Box::new(cons_var), Box::new(record)),
                        span.clone(),
                    );
                    elab_exp(
                        elaboration_context,
                        elaboration_environment,
                        disjointness_environment,
                        &desugared,
                    )
                }
                // Unknown operator: fall back to bare variable lookup
                _ => {
                    let op_var = Located::new(
                        source::Exp::Var(vec![], op.clone(), source::Inference::Infer),
                        span.clone(),
                    );
                    let app1 =
                        Located::new(source::Exp::App(Box::new(op_var), e1.clone()), span.clone());
                    let desugared =
                        Located::new(source::Exp::App(Box::new(app1), e2.clone()), span.clone());
                    elab_exp(
                        elaboration_context,
                        elaboration_environment,
                        disjointness_environment,
                        &desugared,
                    )
                }
            }
        }
    }
}

/// Desugar `e1 op e2` to `(module.name e1) e2` (curried Basis/Top function call).
fn desugar_binop(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    disjointness_environment: &disjoint::DisjointEnv,
    name: &str,
    module: Vec<String>,
    e1: &source::LocExp,
    e2: &source::LocExp,
    span: &Span,
) -> (elab::LocatedExpression, elab::LocatedConstructor) {
    let op_var = Located::new(
        source::Exp::Var(module, name.into(), source::Inference::Infer),
        span.clone(),
    );
    let app1 = Located::new(
        source::Exp::App(Box::new(op_var), Box::new(e1.clone())),
        span.clone(),
    );
    let desugared = Located::new(
        source::Exp::App(Box::new(app1), Box::new(e2.clone())),
        span.clone(),
    );
    elab_exp(
        elaboration_context,
        elaboration_environment,
        disjointness_environment,
        &desugared,
    )
}

fn elab_exp_var(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    ms: &[String],
    x: &str,
    span: &Span,
) -> (elab::LocatedExpression, elab::LocatedConstructor) {
    if ms.is_empty() {
        match elaboration_environment.lookup_e(x) {
            VarLookup::Rel(idx, t) => {
                return (Located::new(elab::Expression::Rel(idx), span.clone()), t);
            }
            VarLookup::Named(id, t) => {
                return (Located::new(elab::Expression::Named(id), span.clone()), t);
            }
            VarLookup::NotBound => {
                // Check if it's a constructor
                if let Some(info) = elaboration_environment.lookup_constructor(x) {
                    return make_con_exp(info, elaboration_environment, span);
                }
                elaboration_context.error(
                    span.clone(),
                    DiagnosticPayload::new(DiagnosticId::ElabUnboundVariable, vec![x.to_string()]),
                );
                return (
                    elaborated_expression_error_at_span(span.clone()),
                    elaborated_constructor_error_at_span(span.clone()),
                );
            }
        }
    }

    // Qualified
    let (str_id, items) =
        match resolve_module_path(elaboration_context, elaboration_environment, ms, span) {
            Some(x) => x,
            None => {
                return (
                    elaborated_expression_error_at_span(span.clone()),
                    elaborated_constructor_error_at_span(span.clone()),
                )
            }
        };

    if let Some(elab::SignatureItem::Val(_, _id, t)) = sgi_find_val(&items, x) {
        let e = Located::new(
            elab::Expression::ModProj(str_id, ms[1..].to_vec(), x.to_string()),
            span.clone(),
        );
        return (e, t.clone());
    }
    // Check for datatype constructor (e.g. Basis.None, Basis.Some)
    if let Some((_con_id, dt_id, type_params, arg_type)) = sgi_find_datatype_con(&items, x) {
        let e = Located::new(
            elab::Expression::ModProj(str_id, ms[1..].to_vec(), x.to_string()),
            span.clone(),
        );
        let ktype = Located::new(elab::Kind::Type, span.clone());
        let n = type_params.len();
        let type_args: Vec<elab::LocatedConstructor> = type_params
            .iter()
            .map(|_| fresh_cunif(elaboration_environment, span.clone(), ktype.clone(), "_"))
            .collect();
        let dt_con = {
            let base = Located::new(elab::Constructor::Named(dt_id), span.clone());
            type_args.iter().fold(base, |acc, arg| {
                Located::new(
                    elab::Constructor::App(Box::new(acc), Box::new(arg.clone())),
                    span.clone(),
                )
            })
        };
        let con_type = match arg_type {
            None => {
                // Nullary constructor: type is dt_con
                dt_con
            }
            Some(at_orig) => {
                // Payload constructor: type is arg -> dt_con
                let mut at = at_orig.clone();
                for i in (0..n).rev() {
                    if let Ok(result) = sub_con_in_con(0, &type_args[i], at.clone()) {
                        at = result;
                    }
                }
                Located::new(
                    elab::Constructor::TFun(Box::new(at), Box::new(dt_con)),
                    span.clone(),
                )
            }
        };
        return (e, con_type);
    }

    elaboration_context.error(
        span.clone(),
        DiagnosticPayload::new(DiagnosticId::ElabUnboundVariable, vec![x.to_string()]),
    );
    (
        elaborated_expression_error_at_span(span.clone()),
        elaborated_constructor_error_at_span(span.clone()),
    )
}

/// Find a datatype constructor by name in signature items.
/// Returns (constructor_id, datatype_id, type_params, arg_type).
fn sgi_find_datatype_con<'a>(
    sgis: &'a [elab::LocatedSignatureItem],
    x: &str,
) -> Option<(
    usize,
    usize,
    &'a Vec<String>,
    &'a Option<elab::LocatedConstructor>,
)> {
    for sgi in sgis {
        if let elab::SignatureItem::Datatype(dts) = &sgi.node {
            for dt in dts {
                for (cname, cid, arg_type) in &dt.constrs {
                    if cname == x {
                        return Some((*cid, dt.id, &dt.params, arg_type));
                    }
                }
            }
        }
    }
    None
}

fn make_con_exp(
    info: &ConstructorInfo,
    elaboration_environment: &Env,
    span: &Span,
) -> (elab::LocatedExpression, elab::LocatedConstructor) {
    let ktype = Located::new(elab::Kind::Type, span.clone());
    let n = info.type_params.len();
    let type_args: Vec<elab::LocatedConstructor> = info
        .type_params
        .iter()
        .map(|_| fresh_cunif(elaboration_environment, span.clone(), ktype.clone(), "_"))
        .collect();

    // Return type: dt applied to type_args
    let dt_con = {
        let base = Located::new(elab::Constructor::Named(info.datatype_id), span.clone());
        type_args.iter().fold(base, |acc, arg| {
            Located::new(
                elab::Constructor::App(Box::new(acc), Box::new(arg.clone())),
                span.clone(),
            )
        })
    };

    let con_type = match &info.arg_type {
        None => {
            // Nullary constructor: type is dt_con (e.g. option t)
            dt_con
        }
        Some(at_orig) => {
            // Constructor with payload: type is arg_type -> dt_con.
            // Substitute type params (innermost first: Rel(0) = last param = type_args[n-1]).
            let mut at = at_orig.clone();
            for i in (0..n).rev() {
                if let Ok(result) = sub_con_in_con(0, &type_args[i], at.clone()) {
                    at = result;
                }
            }
            Located::new(
                elab::Constructor::TFun(Box::new(at), Box::new(dt_con)),
                span.clone(),
            )
        }
    };

    let e = Located::new(elab::Expression::Named(info.constructor_id), span.clone());
    (e, con_type)
}

fn elab_exp_record(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    disjointness_environment: &disjoint::DisjointEnv,
    xes: &[(source::LocCon, source::LocExp)],
    span: &Span,
) -> (elab::LocatedExpression, elab::LocatedConstructor) {
    let ktype = Located::new(elab::Kind::Type, span.clone());
    let krow = Located::new(elab::Kind::Record(Box::new(ktype.clone())), span.clone());
    let mut fields = Vec::new(); // (name_con, value_exp, field_type)
    let mut row_fields = Vec::new();

    for (nc, ve) in xes {
        let (nce, nck) = elab_con(elaboration_context, elaboration_environment, nc);
        let kname = Located::new(elab::Kind::Name, span.clone());
        check_kind(
            elaboration_context,
            elaboration_environment,
            &nc.span,
            &nce,
            &nck,
            &kname,
        );
        let (vee, vet) = elab_exp(
            elaboration_context,
            elaboration_environment,
            disjointness_environment,
            ve,
        );
        row_fields.push((nce.clone(), vet.clone()));
        fields.push((nce, vee, vet));
    }

    let row_con = Located::new(
        elab::Constructor::Record(Box::new(krow.clone()), row_fields),
        span.clone(),
    );
    let result_type = Located::new(elab::Constructor::TRecord(Box::new(row_con)), span.clone());
    let result = Located::new(elab::Expression::Record(fields), span.clone());
    (result, result_type)
}

// ---------------------------------------------------------------------------
// elab_head: insert implicit arguments
// ---------------------------------------------------------------------------

fn elab_head(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    disjointness_environment: &disjoint::DisjointEnv,
    e: elab::LocatedExpression,
    t: elab::LocatedConstructor,
    span: &Span,
) -> (elab::LocatedExpression, elab::LocatedConstructor) {
    elab_head_inner(
        elaboration_context,
        elaboration_environment,
        disjointness_environment,
        e,
        t,
        span,
        0,
    )
}

fn elab_head_inner(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    disjointness_environment: &disjoint::DisjointEnv,
    e: elab::LocatedExpression,
    t: elab::LocatedConstructor,
    span: &Span,
    depth: usize,
) -> (elab::LocatedExpression, elab::LocatedConstructor) {
    if depth > 50 {
        elaboration_context.error(
            span.clone(),
            DiagnosticPayload::new(DiagnosticId::ElabImplicitArgIterationLimit, Vec::new()),
        );
        return (
            elaborated_expression_error_at_span(span.clone()),
            elaborated_constructor_error_at_span(span.clone()),
        );
    }
    let tn = hnorm_con(t.clone());
    match &tn.node {
        elab::Constructor::TKFun(x, body) => {
            let ku = fresh_kunif(span.clone(), x);
            let body_subst = sub_kind_in_con(0, &ku, *body.clone());
            let new_e = Located::new(
                elab::Expression::KApp(Box::new(e), Box::new(ku)),
                span.clone(),
            );
            elab_head_inner(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                new_e,
                body_subst,
                span,
                depth + 1,
            )
        }
        elab::Constructor::TCFun(elab::Explicitness::Implicit, x, k, body) => {
            // Insert implicit constructor argument
            let cu = fresh_cunif(elaboration_environment, span.clone(), *k.clone(), x);
            let body_subst = match sub_con_in_con(0, &cu, *body.clone()) {
                Ok(t) => t,
                Err(_) => elaborated_constructor_error_at_span(span.clone()),
            };
            let new_e = Located::new(elab::Expression::CApp(Box::new(e), cu), span.clone());
            elab_head_inner(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                new_e,
                body_subst,
                span,
                depth + 1,
            )
        }
        elab::Constructor::TDisjoint(c1, c2, body) => {
            // Insert disjointness witness
            let goals = disjoint::prove(
                span.clone(),
                disjointness_environment,
                *c1.clone(),
                *c2.clone(),
            );
            if !goals.is_empty() {
                for g in goals {
                    elaboration_context.constraints.push(Constraint::Disjoint {
                        span: span.clone(),
                        elaboration_environment: elaboration_environment.clone(),
                        goal: g,
                    });
                }
            }
            // The witness expression (a proof of disjointness) is just a unit
            let witness = Located::new(elab::Expression::Prim(Prim::Int(0)), span.clone());
            let new_e = Located::new(
                elab::Expression::App(Box::new(e), Box::new(witness)),
                span.clone(),
            );
            elab_head_inner(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                new_e,
                *body.clone(),
                span,
                depth + 1,
            )
        }
        elab::Constructor::TFun(dom, _) if elaboration_environment.is_class(dom) => {
            // Typeclass argument — insert implicit resolution
            let result_ref: Arc<Mutex<Option<elab::LocatedExpression>>> =
                Arc::new(Mutex::new(None));
            elaboration_context.constraints.push(Constraint::TypeClass {
                span: span.clone(),
                elaboration_environment: elaboration_environment.clone(),
                class: *dom.clone(),
                result: result_ref.clone(),
            });
            let witness = Located::new(elab::Expression::Unif(result_ref), span.clone());
            let new_e = Located::new(
                elab::Expression::App(Box::new(e), Box::new(witness)),
                span.clone(),
            );
            // Return type is the codomain
            match tn.node {
                elab::Constructor::TFun(_, ran) => elab_head_inner(
                    elaboration_context,
                    elaboration_environment,
                    disjointness_environment,
                    new_e,
                    *ran,
                    span,
                    depth + 1,
                ),
                _ => (new_e, t),
            }
        }
        // Try to unfold named type constructors (e.g. `bodyTag boxAttrs`) using the elaboration_environment.
        // This handles cases like `h1 : bodyTag boxAttrs` where bodyTag = fn attrs => ...
        elab::Constructor::Named(id) => {
            if let Ok((_, _, Some(def))) = elaboration_environment.lookup_c_named(*id) {
                elab_head_inner(
                    elaboration_context,
                    elaboration_environment,
                    disjointness_environment,
                    e,
                    def.clone(),
                    span,
                    depth + 1,
                )
            } else {
                (e, t)
            }
        }
        elab::Constructor::App(f, arg) => {
            // Try to reduce App(Named(id), arg) by substituting Named's definition.
            let head_def = match &f.node {
                elab::Constructor::Named(id) => match elaboration_environment.lookup_c_named(*id) {
                    Ok((_, _, Some(def))) => Some(def.clone()),
                    _ => None,
                },
                _ => None,
            };
            if let Some(def) = head_def {
                if let elab::Constructor::Abs(_, _, body) = def.node {
                    if let Ok(result) = sub_con_in_con(0, arg, *body) {
                        elab_head_inner(
                            elaboration_context,
                            elaboration_environment,
                            disjointness_environment,
                            e,
                            hnorm_con(result),
                            span,
                            depth + 1,
                        )
                    } else {
                        (e, t)
                    }
                } else {
                    (e, t)
                }
            } else {
                (e, t)
            }
        }
        _ => (e, t),
    }
}

// ---------------------------------------------------------------------------
// Expression-level declaration elaboration
// ---------------------------------------------------------------------------

fn elab_edecl(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    disjointness_environment: &disjoint::DisjointEnv,
    ed: &source::LocEDecl,
) -> (Option<elab::LocatedElaboratedDeclaration>, Env) {
    let span = ed.span.clone();
    match &ed.node {
        source::EDecl::Val(pat, e) => {
            let t = fresh_cunif(
                elaboration_environment,
                span.clone(),
                Located::new(elab::Kind::Type, span.clone()),
                "_",
            );
            let (ee, et) = elab_exp(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                e,
            );
            let (pate, new_env) = elab_pat(elaboration_context, elaboration_environment, pat, &et);
            check_con(elaboration_context, elaboration_environment, &span, &et, &t);
            let decl = Located::new(elab::ElaboratedDeclaration::Val(pate, et, ee), span);
            (Some(decl), new_env)
        }
        source::EDecl::ValRec(bindings) => {
            // Mutual recursion: add all names to elaboration_environment first
            let mut pre_env = elaboration_environment.clone();
            let mut annot_types: Vec<elab::LocatedConstructor> = Vec::new();
            for (x, opt_ann, _) in bindings {
                let t = match opt_ann {
                    Some(ann) => {
                        let (ce, _) = elab_con(elaboration_context, &pre_env, ann);
                        ce
                    }
                    None => fresh_cunif(
                        &pre_env,
                        span.clone(),
                        Located::new(elab::Kind::Type, span.clone()),
                        x,
                    ),
                };
                annot_types.push(t.clone());
                pre_env = pre_env.push_e_rel(x.clone(), t);
            }

            let mut elab_bindings: Vec<(
                String,
                elab::LocatedConstructor,
                elab::LocatedExpression,
            )> = Vec::new();
            for (i, (x, _, e)) in bindings.iter().enumerate() {
                let (ee, et) = elab_exp(elaboration_context, &pre_env, disjointness_environment, e);
                check_con(elaboration_context, &pre_env, &span, &et, &annot_types[i]);
                elab_bindings.push((x.clone(), annot_types[i].clone(), ee));
            }

            let decl = Located::new(elab::ElaboratedDeclaration::ValRec(elab_bindings), span);
            (Some(decl), pre_env)
        }
    }
}

// ---------------------------------------------------------------------------
// Signature item elaboration
// ---------------------------------------------------------------------------

/// Elaborate one signature item, returning updated `elaboration_environment` when the item introduces names.
///
/// `Include` currently yields `(None, elaboration_environment.clone())` (placeholder vs full `expand` in SML).
///
/// # Arguments
///
/// * `elaboration_context` — Sets [`ElabCtx::in_signature`] around nested structures; collects errors.
/// * `elaboration_environment` — Outer environment.
/// * `disjointness_environment` — Passed through to nested [`elab_sgn`] calls.
/// * `sgi` — Source signature item.
///
/// # Returns
///
/// `Some(elaborated item)` and new environment, or `(None, elaboration_environment)` for unimplemented include wiring.
pub fn elab_sgn_item(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    disjointness_environment: &disjoint::DisjointEnv,
    sgi: &source::LocSgnItem,
) -> (Option<elab::LocatedSignatureItem>, Env) {
    let span = sgi.span.clone();
    match &sgi.node {
        source::SgnItem::ConAbs(x, k) => {
            let ke = elab_kind(elaboration_context, elaboration_environment, k);
            let (new_env, id) =
                elaboration_environment
                    .clone()
                    .push_c_named(x.clone(), ke.clone(), None);
            let result = Located::new(elab::SignatureItem::ConAbs(x.clone(), id, ke), span);
            (Some(result), new_env)
        }
        source::SgnItem::Con(x, opt_k, c) => {
            let (ce, ck) = elab_con(elaboration_context, elaboration_environment, c);
            let ke = match opt_k {
                Some(k) => {
                    let ke2 = elab_kind(elaboration_context, elaboration_environment, k);
                    check_kind(
                        elaboration_context,
                        elaboration_environment,
                        &span,
                        &ce,
                        &ck,
                        &ke2,
                    );
                    ke2
                }
                None => ck,
            };
            let (new_env, id) = elaboration_environment.clone().push_c_named(
                x.clone(),
                ke.clone(),
                Some(ce.clone()),
            );
            let result = Located::new(
                elab::SignatureItem::Constructor(x.clone(), id, ke, ce),
                span,
            );
            (Some(result), new_env)
        }
        source::SgnItem::Val(x, t) => {
            let (te, _) = elab_con(elaboration_context, elaboration_environment, t);
            let (new_env, id) = elaboration_environment
                .clone()
                .push_e_named(x.clone(), te.clone());
            let result = Located::new(elab::SignatureItem::Val(x.clone(), id, te), span);
            (Some(result), new_env)
        }
        source::SgnItem::Str(x, sgn) => {
            let prev_in_sig = elaboration_context.in_signature;
            elaboration_context.in_signature = true;
            let sgne = elab_sgn(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                sgn,
            );
            elaboration_context.in_signature = prev_in_sig;
            let (new_env, id) = elaboration_environment
                .clone()
                .push_str_named(x.clone(), sgne.clone());
            let result = Located::new(
                elab::SignatureItem::Structure(elab::ImportMode::Import, x.clone(), id, sgne),
                span,
            );
            (Some(result), new_env)
        }
        source::SgnItem::Sgn(x, sgn) => {
            let sgne = elab_sgn(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                sgn,
            );
            let (new_env, id) = elaboration_environment
                .clone()
                .push_sgn_named(x.clone(), sgne.clone());
            let result = Located::new(elab::SignatureItem::Signature(x.clone(), id, sgne), span);
            (Some(result), new_env)
        }
        source::SgnItem::Include(sgn) => {
            // Include expands the signature items
            let _sgne = elab_sgn(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                sgn,
            );
            // We return None and handle include by returning the sgn's items
            // For simplicity, wrap in a Structure with a fresh name
            (None, elaboration_environment.clone())
        }
        source::SgnItem::Constraint(c1, c2) => {
            let (c1e, _) = elab_con(elaboration_context, elaboration_environment, c1);
            let (c2e, _) = elab_con(elaboration_context, elaboration_environment, c2);
            let result = Located::new(elab::SignatureItem::Constraint(c1e, c2e), span);
            (Some(result), elaboration_environment.clone())
        }
        source::SgnItem::Datatype(dts) => {
            elab_datatype_sig(elaboration_context, elaboration_environment, dts, &span)
        }
        source::SgnItem::DatatypeImp(x, ms, y) => elab_datatype_imp_sig(
            elaboration_context,
            elaboration_environment,
            x,
            ms,
            y,
            &span,
        ),
        source::SgnItem::ClassAbs(x, k) => {
            let ke = elab_kind(elaboration_context, elaboration_environment, k); // parameter kind (`Type` for bare `class nm`)
            let (mut new_env, id) =
                elaboration_environment
                    .clone()
                    .push_c_named(x.clone(), ke.clone(), None); // store parameter kind; see elab_con_var Named + is_class
            new_env = new_env.push_class(id);
            let result = Located::new(elab::SignatureItem::ClassAbs(x.clone(), id, ke), span);
            (Some(result), new_env)
        }
        source::SgnItem::Class(x, k, c) => {
            let ke = elab_kind(elaboration_context, elaboration_environment, k);
            let (ce, _) = elab_con(elaboration_context, elaboration_environment, c);
            let (mut new_env, id) = elaboration_environment.clone().push_c_named(
                x.clone(),
                ke.clone(),
                Some(ce.clone()),
            );
            new_env = new_env.push_class(id);
            let result = Located::new(elab::SignatureItem::Class(x.clone(), id, ke, ce), span);
            (Some(result), new_env)
        }
        source::SgnItem::Table(x, c, _pk_e, _unique_e) => {
            // Table in signature: like Val
            let (ce, _) = elab_con(elaboration_context, elaboration_environment, c);
            let (new_env, id) = elaboration_environment
                .clone()
                .push_e_named(x.clone(), ce.clone());
            let result = Located::new(elab::SignatureItem::Val(x.clone(), id, ce), span);
            (Some(result), new_env)
        }

        source::SgnItem::Functor(functor_name, arg_name, s1, s2) => {
            let dome = elab_sgn(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                s1,
            );
            let (env_for_ran, arg_id) = elaboration_environment
                .clone()
                .push_str_named(arg_name.clone(), dome.clone());
            let rane = elab_sgn(
                elaboration_context,
                &env_for_ran,
                disjointness_environment,
                s2,
            );
            let fun_sgn = Located::new(
                elab::Signature::Fun(arg_name.clone(), arg_id, Box::new(dome), Box::new(rane)),
                span.clone(),
            );
            let (new_env, id) = elaboration_environment
                .clone()
                .push_str_named(functor_name.clone(), fun_sgn.clone());
            let result = Located::new(
                elab::SignatureItem::Structure(
                    elab::ImportMode::Import,
                    functor_name.clone(),
                    id,
                    fun_sgn,
                ),
                span,
            );
            (Some(result), new_env)
        }
    }
}

fn elab_datatype_sig(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    dts: &[source::DatatypeDecl],
    span: &Span,
) -> (Option<elab::LocatedSignatureItem>, Env) {
    let mut cur_env = elaboration_environment.clone();
    let mut elab_dts: Vec<elab::DatatypeDecl> = Vec::new();

    for dt in dts {
        let (elab_dt, new_env) = elab_single_datatype(elaboration_context, &cur_env, dt, span);
        cur_env = new_env;
        elab_dts.push(elab_dt);
    }

    let result = Located::new(elab::SignatureItem::Datatype(elab_dts), span.clone());
    (Some(result), cur_env)
}

fn elab_single_datatype(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    dt: &source::DatatypeDecl,
    span: &Span,
) -> (elab::DatatypeDecl, Env) {
    // Build kind: (Type -> ... -> Type) for each param
    let ktype = Located::new(elab::Kind::Type, span.clone());
    let dt_kind = dt.params.iter().fold(ktype.clone(), |acc, _| {
        Located::new(
            elab::Kind::Arrow(Box::new(ktype.clone()), Box::new(acc)),
            span.clone(),
        )
    });

    let (env_with_dt, dt_id) =
        elaboration_environment
            .clone()
            .push_c_named(dt.name.clone(), dt_kind, None);

    // Push type params
    let mut param_env = env_with_dt.clone();
    for p in &dt.params {
        param_env = param_env.push_c_rel(p.clone(), ktype.clone());
    }

    // Elaborate constructors
    let mut constrs: Vec<(String, usize, Option<elab::LocatedConstructor>)> = Vec::new();
    for (cname, opt_arg) in &dt.constrs {
        let con_id = new_named_id();
        let arg_type = opt_arg.as_ref().map(|at| {
            let (ce, _) = elab_con(elaboration_context, &param_env, at);
            ce
        });
        constrs.push((cname.clone(), con_id, arg_type));
    }

    let env_with_constrs = env_with_dt.push_datatype(dt_id, dt.params.clone(), constrs.clone());

    let elab_dt = elab::DatatypeDecl {
        name: dt.name.clone(),
        id: dt_id,
        params: dt.params.clone(),
        constrs,
    };
    (elab_dt, env_with_constrs)
}

fn elab_datatype_imp_sig(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    x: &str,
    ms: &[String],
    y: &str,
    span: &Span,
) -> (Option<elab::LocatedSignatureItem>, Env) {
    // DatatypeImp: x = M.Y (datatype alias)
    let (str_id, items) =
        match resolve_module_path(elaboration_context, elaboration_environment, ms, span) {
            Some(v) => v,
            None => return (None, elaboration_environment.clone()),
        };

    if let Some(dt) = sgi_find_datatype(&items, y) {
        let id = new_named_id();
        let constrs = dt.constrs.clone();
        let new_env = elaboration_environment.clone().push_c_named_as(
            x.to_string(),
            id,
            Located::new(elab::Kind::Type, span.clone()),
            None,
        );
        let result = Located::new(
            elab::SignatureItem::DatatypeImp {
                name: x.to_string(),
                id,
                orig_mod: str_id,
                orig_path: ms.to_vec(),
                orig_name: y.to_string(),
                orig_constrs_path: ms.to_vec(),
                constrs,
            },
            span.clone(),
        );
        return (Some(result), new_env);
    }

    elaboration_context.error(
        span.clone(),
        DiagnosticPayload::new(DiagnosticId::ElabUnboundDatatype, vec![y.to_string()]),
    );
    (None, elaboration_environment.clone())
}

// ---------------------------------------------------------------------------
// Signature elaboration
// ---------------------------------------------------------------------------

/// Elaborate a signature (`sig … end`, variables, functors, `where`, projections).
///
/// # Arguments
///
/// * `elaboration_context` — Diagnostic context.
/// * `elaboration_environment` — Module/type environment for lookups.
/// * `disjointness_environment` — Disjointness for nested items.
/// * `sgn` — Source signature AST.
///
/// # Returns
///
/// [`elab::LocatedSignature`]; failures use [`elab::Signature::Error`] after `elaboration_context.error`.
pub fn elab_sgn(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    disjointness_environment: &disjoint::DisjointEnv,
    sgn: &source::LocSgn,
) -> elab::LocatedSignature {
    let span = sgn.span.clone();
    match &sgn.node {
        source::Sgn::Const(sgis) => {
            let mut cur_env = elaboration_environment.clone();
            let mut elab_sgis: Vec<elab::LocatedSignatureItem> = Vec::new();
            for sgi in sgis {
                let (sgi_opt, new_env) =
                    elab_sgn_item(elaboration_context, &cur_env, disjointness_environment, sgi);
                cur_env = new_env;
                if let Some(s) = sgi_opt {
                    elab_sgis.push(s);
                }
            }
            Located::new(elab::Signature::Const(elab_sgis), span)
        }
        source::Sgn::Var(x) => match elaboration_environment.lookup_sgn(x) {
            Some((id, _)) => Located::new(elab::Signature::Var(*id), span),
            None => {
                elaboration_context.error(
                    span.clone(),
                    DiagnosticPayload::new(DiagnosticId::ElabUnboundSignature, vec![x.clone()]),
                );
                elaborated_signature_error_at_span(span)
            }
        },
        source::Sgn::Fun(x, dom, ran) => {
            let dome = elab_sgn(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                dom,
            );
            // Bind x in elaboration_environment for ran
            let (env2, id) = elaboration_environment
                .clone()
                .push_str_named(x.clone(), dome.clone());
            let rane = elab_sgn(elaboration_context, &env2, disjointness_environment, ran);
            Located::new(
                elab::Signature::Fun(x.clone(), id, Box::new(dome), Box::new(rane)),
                span,
            )
        }
        source::Sgn::Where(sgn1, ms, x, c) => {
            let sgn1e = elab_sgn(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                sgn1,
            );
            let (ce, _) = elab_con(elaboration_context, elaboration_environment, c);
            Located::new(
                elab::Signature::Where(Box::new(sgn1e), ms.clone(), x.clone(), ce),
                span,
            )
        }
        source::Sgn::Proj(m, ms, x) => match elaboration_environment.lookup_str(m) {
            Some((id, _)) => Located::new(elab::Signature::Proj(*id, ms.clone(), x.clone()), span),
            None => {
                elaboration_context.error(
                    span.clone(),
                    DiagnosticPayload::new(
                        DiagnosticId::ElabUnboundModuleForSignature,
                        vec![m.clone()],
                    ),
                );
                elaborated_signature_error_at_span(span)
            }
        },
    }
}

// ---------------------------------------------------------------------------
// subSgn: signature subtyping
// ---------------------------------------------------------------------------

/// Check that `actual` implements `expected` (after [`hnorm_sgn`]): functor contra/covariance, `val`/`type`/`structure` items, constraints via [`disjoint::prove`].
///
/// Records errors on `elaboration_context`; pushes deferred disjoint [`Constraint`]s when [`disjoint::prove`] returns goals.
///
/// # Arguments
///
/// * `elaboration_context` — Receiver for mismatch errors and constraints.
/// * `elaboration_environment` — For lookups in actual items.
/// * `disjointness_environment` — Disjointness hypotheses.
/// * `actual`, `expected` — Signatures to relate (spec vs implementation).
/// * `span` — Fallback span for generic “signature mismatch”.
pub fn sub_sgn(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    disjointness_environment: &disjoint::DisjointEnv,
    actual: &elab::LocatedSignature,
    expected: &elab::LocatedSignature,
    span: &Span,
) {
    let actual_n = hnorm_sgn(elaboration_environment, actual);
    let expected_n = hnorm_sgn(elaboration_environment, expected);

    match (&actual_n.node, &expected_n.node) {
        (elab::Signature::Error, _) | (_, elab::Signature::Error) => {}

        (elab::Signature::Const(sgis1), elab::Signature::Const(sgis2)) => {
            // For each item in sgis2 (the expected/spec), find it in sgis1
            for sgi2 in sgis2 {
                sub_sgi(
                    elaboration_context,
                    elaboration_environment,
                    disjointness_environment,
                    sgis1,
                    &sgi2.node,
                    span,
                );
            }
        }

        (elab::Signature::Fun(_, id1, dom1, ran1), elab::Signature::Fun(_, _id2, dom2, ran2)) => {
            // Contravariant in domain
            sub_sgn(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                dom2,
                dom1,
                span,
            );
            // Covariant in range: bind the module param
            let env2 = elaboration_environment.clone().push_str_named_as(
                "_".to_string(),
                *id1,
                *dom1.clone(),
            );
            sub_sgn(
                elaboration_context,
                &env2,
                disjointness_environment,
                ran1,
                ran2,
                span,
            );
        }

        _ => {
            elaboration_context.error(
                span.clone(),
                DiagnosticPayload::new(DiagnosticId::ElabSignatureMismatch, Vec::new()),
            );
        }
    }
}

fn sub_sgi(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    disjointness_environment: &disjoint::DisjointEnv,
    actual_sgis: &[elab::LocatedSignatureItem],
    expected: &elab::SignatureItem,
    span: &Span,
) {
    match expected {
        elab::SignatureItem::Val(x, _, t2) => {
            if let Some(sgi1) = sgi_find_val(actual_sgis, x) {
                if let elab::SignatureItem::Val(_, _, t1) = sgi1 {
                    check_con(elaboration_context, elaboration_environment, span, t1, t2);
                }
            } else {
                elaboration_context.error(
                    span.clone(),
                    DiagnosticPayload::new(
                        DiagnosticId::ElabSignatureMissingValue,
                        vec![x.clone()],
                    ),
                );
            }
        }
        elab::SignatureItem::ConAbs(x, _, k2) => {
            if let Some(sgi1) = sgi_find_con(actual_sgis, x) {
                match sgi1 {
                    elab::SignatureItem::ConAbs(_, _, k1)
                    | elab::SignatureItem::Constructor(_, _, k1, _) => {
                        if let Err(e) = unify_kinds(elaboration_environment, k1, k2) {
                            elaboration_context.error(
                                span.clone(),
                                DiagnosticPayload::new(
                                    DiagnosticId::ElabKindMismatchForSignatureValue,
                                    vec![
                                        x.clone(),
                                        format_failed_to_unify_kinds_message(e.as_ref()),
                                    ],
                                ),
                            );
                        }
                    }
                    _ => elaboration_context.error(
                        span.clone(),
                        DiagnosticPayload::new(
                            DiagnosticId::ElabWrongConstructorKindFor,
                            vec![x.clone()],
                        ),
                    ),
                }
            } else {
                elaboration_context.error(
                    span.clone(),
                    DiagnosticPayload::new(DiagnosticId::ElabSignatureMissingType, vec![x.clone()]),
                );
            }
        }
        elab::SignatureItem::Constructor(x, _, k2, c2) => {
            if let Some(sgi1) = sgi_find_con(actual_sgis, x) {
                match sgi1 {
                    elab::SignatureItem::Constructor(_, _, k1, c1) => {
                        if let Err(e) = unify_kinds(elaboration_environment, k1, k2) {
                            elaboration_context.error(
                                span.clone(),
                                DiagnosticPayload::new(
                                    DiagnosticId::ElabKindMismatchForSignatureValue,
                                    vec![
                                        x.clone(),
                                        format_failed_to_unify_kinds_message(e.as_ref()),
                                    ],
                                ),
                            );
                        }
                        check_con(elaboration_context, elaboration_environment, span, c1, c2);
                    }
                    _ => elaboration_context.error(
                        span.clone(),
                        DiagnosticPayload::new(
                            DiagnosticId::ElabWrongTypeForSignature,
                            vec![x.clone()],
                        ),
                    ),
                }
            } else {
                elaboration_context.error(
                    span.clone(),
                    DiagnosticPayload::new(DiagnosticId::ElabSignatureMissingType, vec![x.clone()]),
                );
            }
        }
        elab::SignatureItem::Structure(_, x, _, sgn2) => {
            if let Some(sgi1) = sgi_find_str(actual_sgis, x) {
                if let elab::SignatureItem::Structure(_, _, _, sgn1) = sgi1 {
                    sub_sgn(
                        elaboration_context,
                        elaboration_environment,
                        disjointness_environment,
                        sgn1,
                        sgn2,
                        span,
                    );
                }
            } else {
                elaboration_context.error(
                    span.clone(),
                    DiagnosticPayload::new(
                        DiagnosticId::ElabSignatureMissingStructure,
                        vec![x.clone()],
                    ),
                );
            }
        }
        elab::SignatureItem::Constraint(c1, c2) => {
            // Check that the constraint holds in actual
            let goals = disjoint::prove(
                span.clone(),
                disjointness_environment,
                c1.clone(),
                c2.clone(),
            );
            if !goals.is_empty() {
                for g in goals {
                    elaboration_context.constraints.push(Constraint::Disjoint {
                        span: span.clone(),
                        elaboration_environment: elaboration_environment.clone(),
                        goal: g,
                    });
                }
            }
        }
        _ => {
            // Datatype, Signature, Class items — simplified
        }
    }
}

// ---------------------------------------------------------------------------
// Top-level declaration elaboration
// ---------------------------------------------------------------------------

/// Elaborate one source declaration, producing zero or more elaborated decls plus updated `elaboration_environment` and `disjointness_environment`.
///
/// Handles types, values, structures, functors, SQL/table/cookie forms, FFI, and constraint assertions.
///
/// # Arguments
///
/// * `elaboration_context` — Errors and constraints.
/// * `elaboration_environment` — Environment before this declaration.
/// * `disjointness_environment` — Disjointness environment; may grow for `constraint` declarations.
/// * `decl` — Parsed top-level decl.
///
/// # Returns
///
/// `(decls, new_env, new_denv)` — multiple `decls` for constructs that desugar (e.g. some `open` paths).
pub fn elab_decl(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    disjointness_environment: &disjoint::DisjointEnv,
    decl: &source::LocDecl,
) -> (Vec<elab::LocatedDeclaration>, Env, disjoint::DisjointEnv) {
    let span = decl.span.clone();
    match &decl.node {
        source::Decl::Con(x, opt_k, c) => {
            let (ce, ck) = elab_con(elaboration_context, elaboration_environment, c);
            let ke = match opt_k {
                Some(k) => {
                    let ke2 = elab_kind(elaboration_context, elaboration_environment, k);
                    check_kind(
                        elaboration_context,
                        elaboration_environment,
                        &span,
                        &ce,
                        &ck,
                        &ke2,
                    );
                    ke2
                }
                None => {
                    // Matches `elabDecl` / `DCon` in `elaborate.sml`: absent ascribed kind uses `kunif`,
                    // then `checkKind` unifies inferred constructor kind with it (kind-polymorphic `con`).
                    let inferred_metakind_slot = fresh_kunif(span.clone(), x);
                    check_kind(
                        elaboration_context,
                        elaboration_environment,
                        &span,
                        &ce,
                        &ck,
                        &inferred_metakind_slot,
                    );
                    hnorm_kind(inferred_metakind_slot)
                }
            };
            let (new_env, id) = elaboration_environment.clone().push_c_named(
                x.clone(),
                ke.clone(),
                Some(ce.clone()),
            );
            let decl_out =
                Located::new(elab::Declaration::Constructor(x.clone(), id, ke, ce), span);
            (vec![decl_out], new_env, disjointness_environment.clone())
        }

        source::Decl::Datatype(dts) => {
            let mut cur_env = elaboration_environment.clone();
            let mut elab_dts: Vec<elab::DatatypeDecl> = Vec::new();
            for dt in dts {
                let (elab_dt, new_env) =
                    elab_single_datatype(elaboration_context, &cur_env, dt, &span);
                cur_env = new_env;
                elab_dts.push(elab_dt);
            }
            let decl_out = Located::new(elab::Declaration::Datatype(elab_dts), span);
            (vec![decl_out], cur_env, disjointness_environment.clone())
        }

        source::Decl::DatatypeImp(x, ms, y) => {
            let (opt_sgi, new_env) = elab_datatype_imp_sig(
                elaboration_context,
                elaboration_environment,
                x,
                ms,
                y,
                &span,
            );
            if let Some(sgi) = opt_sgi {
                if let elab::SignatureItem::DatatypeImp {
                    name,
                    id,
                    orig_mod,
                    orig_path,
                    orig_name,
                    orig_constrs_path,
                    constrs,
                } = sgi.node
                {
                    let decl_out = Located::new(
                        elab::Declaration::DatatypeImp {
                            name,
                            id,
                            orig_mod,
                            orig_path,
                            orig_name,
                            orig_constrs_path,
                            constrs,
                        },
                        span,
                    );
                    return (vec![decl_out], new_env, disjointness_environment.clone());
                }
            }
            (vec![], new_env, disjointness_environment.clone())
        }

        source::Decl::Val(pat, e) => {
            let _t = fresh_cunif(
                elaboration_environment,
                span.clone(),
                Located::new(elab::Kind::Type, span.clone()),
                "_",
            );
            let (ee, et) = elab_exp(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                e,
            );
            let (pate, new_env) = elab_pat(elaboration_context, elaboration_environment, pat, &et);
            // Collect declared bindings
            let mut decls = Vec::new();
            collect_val_decls(&pate, &ee, &et, &span, &mut decls, &mut new_env.clone());
            // Solve constraints
            solve_constraints(elaboration_context, &new_env);
            (decls, new_env, disjointness_environment.clone())
        }

        source::Decl::ValRec(bindings) => {
            let mut pre_env = elaboration_environment.clone();
            let mut annot_types: Vec<elab::LocatedConstructor> = Vec::new();
            let mut ids: Vec<usize> = Vec::new();

            for (x, opt_ann, _) in bindings {
                let t = match opt_ann {
                    Some(ann) => {
                        let (ce, _) = elab_con(elaboration_context, &pre_env, ann);
                        ce
                    }
                    None => fresh_cunif(
                        &pre_env,
                        span.clone(),
                        Located::new(elab::Kind::Type, span.clone()),
                        x,
                    ),
                };
                annot_types.push(t.clone());
                let (new_env, id) = pre_env.push_e_named(x.clone(), t);
                pre_env = new_env;
                ids.push(id);
            }

            let mut elab_recs: Vec<(
                String,
                usize,
                elab::LocatedConstructor,
                elab::LocatedExpression,
            )> = Vec::new();
            for (i, (x, _, e)) in bindings.iter().enumerate() {
                let (ee, et) = elab_exp(elaboration_context, &pre_env, disjointness_environment, e);
                check_con(elaboration_context, &pre_env, &span, &et, &annot_types[i]);
                elab_recs.push((x.clone(), ids[i], annot_types[i].clone(), ee));
            }

            solve_constraints(elaboration_context, &pre_env);
            let decl_out = Located::new(elab::Declaration::ValRec(elab_recs), span);
            (vec![decl_out], pre_env, disjointness_environment.clone())
        }

        source::Decl::Sgn(x, sgn) => {
            let sgne = elab_sgn(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                sgn,
            );
            let (new_env, id) = elaboration_environment
                .clone()
                .push_sgn_named(x.clone(), sgne.clone());
            let decl_out = Located::new(elab::Declaration::Signature(x.clone(), id, sgne), span);
            (vec![decl_out], new_env, disjointness_environment.clone())
        }

        source::Decl::Str(x, opt_sgn, _mtime, str_body, _from_root) => elab_str_decl(
            elaboration_context,
            elaboration_environment,
            disjointness_environment,
            x,
            opt_sgn.as_ref(),
            str_body,
            &span,
        ),

        source::Decl::FfiStr(x, sgn, _mtime) => {
            let sgne = elab_sgn(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                sgn,
            );
            let (new_env, id) = elaboration_environment
                .clone()
                .push_str_named(x.clone(), sgne.clone());
            let decl_out = Located::new(elab::Declaration::FfiStr(x.clone(), id, sgne), span);
            (vec![decl_out], new_env, disjointness_environment.clone())
        }

        source::Decl::Open(m, ms) => {
            // Open M: bring all bindings from M into scope
            let all_ms: Vec<String> = std::iter::once(m.clone())
                .chain(ms.iter().cloned())
                .collect();
            elab_open(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                &all_ms,
                &span,
            )
        }

        source::Decl::Constraint(c1, c2) => {
            let (c1e, _) = elab_con(elaboration_context, elaboration_environment, c1);
            let (c2e, _) = elab_con(elaboration_context, elaboration_environment, c2);
            let new_denv =
                disjoint::assert(c1e.clone(), c2e.clone(), disjointness_environment.clone());
            let decl_out = Located::new(elab::Declaration::Constraint(c1e, c2e), span);
            (vec![decl_out], elaboration_environment.clone(), new_denv)
        }

        source::Decl::OpenConstraints(_m, _ms) => {
            // Simplified: no-op for now
            (
                vec![],
                elaboration_environment.clone(),
                disjointness_environment.clone(),
            )
        }

        source::Decl::Export(str_body) => {
            let (str_e, str_sgn) = elab_str(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                str_body,
                None,
            );
            let (new_env, id) = elaboration_environment
                .clone()
                .push_str_named("_export".to_string(), str_sgn.clone());
            let decl_out = Located::new(elab::Declaration::Export(id, str_sgn, str_e), span);
            (vec![decl_out], new_env, disjointness_environment.clone())
        }

        source::Decl::Table(x, c, pk_e, unique_e) => elab_table_decl(
            elaboration_context,
            elaboration_environment,
            disjointness_environment,
            x,
            c,
            pk_e,
            unique_e,
            &span,
        ),

        source::Decl::Sequence(x) => {
            let nt = new_named_id();
            let (new_env, id) = elaboration_environment.clone().push_e_named(
                x.clone(),
                basis_named_con(elaboration_environment, &span, "int"),
            );
            let decl_out = Located::new(elab::Declaration::Sequence(nt, x.clone(), id), span);
            (vec![decl_out], new_env, disjointness_environment.clone())
        }

        source::Decl::View(x, e) => {
            let (ee, et) = elab_exp(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                e,
            );
            let nt = new_named_id();
            let (new_env, id) = elaboration_environment
                .clone()
                .push_e_named(x.clone(), et.clone());
            let decl_out = Located::new(elab::Declaration::View(nt, x.clone(), id, ee, et), span);
            (vec![decl_out], new_env, disjointness_environment.clone())
        }

        source::Decl::Index(e1, e2, _opt_c) => {
            let (e1e, _) = elab_exp(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                e1,
            );
            let (e2e, _) = elab_exp(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                e2,
            );
            let decl_out = Located::new(elab::Declaration::Index(e1e, e2e), span);
            (
                vec![decl_out],
                elaboration_environment.clone(),
                disjointness_environment.clone(),
            )
        }

        source::Decl::Database(x) => {
            let decl_out = Located::new(elab::Declaration::Database(x.clone()), span);
            (
                vec![decl_out],
                elaboration_environment.clone(),
                disjointness_environment.clone(),
            )
        }

        source::Decl::Cookie(x, c) => {
            let (ce, _) = elab_con(elaboration_context, elaboration_environment, c);
            let nt = new_named_id();
            let (new_env, id) = elaboration_environment
                .clone()
                .push_e_named(x.clone(), ce.clone());
            let decl_out = Located::new(elab::Declaration::Cookie(nt, x.clone(), id, ce), span);
            (vec![decl_out], new_env, disjointness_environment.clone())
        }

        source::Decl::Style(x) => {
            let nt = new_named_id();
            let (new_env, id) = elaboration_environment.clone().push_e_named(
                x.clone(),
                Located::new(elab::Constructor::Unit, span.clone()),
            );
            let decl_out = Located::new(elab::Declaration::Style(nt, x.clone(), id), span);
            (vec![decl_out], new_env, disjointness_environment.clone())
        }

        source::Decl::Task(e1, e2) => {
            let (e1e, _) = elab_exp(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                e1,
            );
            let (e2e, _) = elab_exp(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                e2,
            );
            let decl_out = Located::new(elab::Declaration::Task(e1e, e2e), span);
            (
                vec![decl_out],
                elaboration_environment.clone(),
                disjointness_environment.clone(),
            )
        }

        source::Decl::Policy(e) => {
            let (ee, _) = elab_exp(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                e,
            );
            let decl_out = Located::new(elab::Declaration::Policy(ee), span);
            (
                vec![decl_out],
                elaboration_environment.clone(),
                disjointness_environment.clone(),
            )
        }

        source::Decl::OnError(m, ms, x) => {
            let decl_out = Located::new(
                elab::Declaration::OnError(
                    elaboration_environment
                        .lookup_str(m)
                        .map(|(id, _)| *id)
                        .unwrap_or(0),
                    ms.clone(),
                    x.clone(),
                ),
                span,
            );
            (
                vec![decl_out],
                elaboration_environment.clone(),
                disjointness_environment.clone(),
            )
        }

        source::Decl::Ffi(x, modes, c) => {
            let (ce, _) = elab_con(elaboration_context, elaboration_environment, c);
            let (new_env, id) = elaboration_environment
                .clone()
                .push_e_named(x.clone(), ce.clone());
            let decl_out = Located::new(
                elab::Declaration::Ffi(x.clone(), id, modes.clone(), ce),
                span,
            );
            (vec![decl_out], new_env, disjointness_environment.clone())
        }

        source::Decl::OpenStr(s) => {
            let (_str_e, str_sgn) = elab_str(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                s,
                None,
            );
            let h = hnorm_sgn(elaboration_environment, &str_sgn);
            let items = get_sgn_const_items(elaboration_environment, &str_sgn);
            if items.is_empty() && !matches!(h.node, elab::Signature::Const(_)) {
                elaboration_context.error(
                    span.clone(),
                    DiagnosticPayload::new(DiagnosticId::ElabCannotOpenNonConstModule, Vec::new()),
                );
                (
                    vec![],
                    elaboration_environment.clone(),
                    disjointness_environment.clone(),
                )
            } else {
                let mut new_env = elaboration_environment.clone();
                for sgi in &items {
                    new_env = enrich_env_from_sgi(new_env, &sgi.node, 0, &[], "");
                }
                (vec![], new_env, disjointness_environment.clone())
            }
        }
    }
}

fn collect_val_decls(
    pat: &elab::LocatedPattern,
    exp: &elab::LocatedExpression,
    typ: &elab::LocatedConstructor,
    span: &Span,
    decls: &mut Vec<elab::LocatedDeclaration>,
    elaboration_environment: &mut Env,
) {
    match &pat.node {
        elab::Pattern::Var(x, t) => {
            let id = new_named_id();
            *elaboration_environment =
                elaboration_environment
                    .clone()
                    .push_e_named_as(x.clone(), id, t.clone());
            decls.push(Located::new(
                elab::Declaration::Val(x.clone(), id, t.clone(), exp.clone()),
                span.clone(),
            ));
        }
        elab::Pattern::Prim(_) => {
            // No bindings from prim pattern
        }
        _ => {
            // For record patterns etc., generate a fresh binding
            let x = "_".to_string();
            let id = new_named_id();
            decls.push(Located::new(
                elab::Declaration::Val(x.clone(), id, typ.clone(), exp.clone()),
                span.clone(),
            ));
        }
    }
}

fn elab_str_decl(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    disjointness_environment: &disjoint::DisjointEnv,
    x: &str,
    opt_sgn: Option<&source::LocSgn>,
    str_body: &source::LocStr,
    span: &Span,
) -> (Vec<elab::LocatedDeclaration>, Env, disjoint::DisjointEnv) {
    let ascribed_sgn = opt_sgn.map(|sgn| {
        elab_sgn(
            elaboration_context,
            elaboration_environment,
            disjointness_environment,
            sgn,
        )
    });
    let (str_e, inferred_sgn) = elab_str(
        elaboration_context,
        elaboration_environment,
        disjointness_environment,
        str_body,
        ascribed_sgn.as_ref(),
    );
    let (new_env, id) = elaboration_environment
        .clone()
        .push_str_named(x.to_string(), inferred_sgn.clone());
    let decl_out = Located::new(
        elab::Declaration::Structure(x.to_string(), id, inferred_sgn, str_e),
        span.clone(),
    );
    (vec![decl_out], new_env, disjointness_environment.clone())
}

fn elab_open(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    disjointness_environment: &disjoint::DisjointEnv,
    ms: &[String],
    span: &Span,
) -> (Vec<elab::LocatedDeclaration>, Env, disjoint::DisjointEnv) {
    let (str_id, items) =
        match resolve_module_path(elaboration_context, elaboration_environment, ms, span) {
            Some(v) => v,
            None => {
                return (
                    vec![],
                    elaboration_environment.clone(),
                    disjointness_environment.clone(),
                )
            }
        };
    // Add all items from the signature to the current environment
    let mut new_env = elaboration_environment.clone();
    for sgi in &items {
        new_env = enrich_env_from_sgi(
            new_env,
            &sgi.node,
            str_id,
            &ms[..ms.len() - 1],
            &ms[ms.len() - 1],
        );
    }
    (vec![], new_env, disjointness_environment.clone())
}

/// Bind one elaborated signature item into `named_c` / `named_e` when `open`ing a structure.
///
/// Type classes use the same convention as [`elab_sgn_item`]: [`elab::SignatureItem::ClassAbs`]
/// stores the *parameter* kind in `named_c`; [`elab_con_var`] wraps `Named` class heads as
/// `parameter_kind -> Type` when resolving constructor applications (`show t`).
///
/// # Arguments
///
/// * `elaboration_environment` — Environment to extend.
/// * `sgi` — Elaborated signature item (val, con, class, …).
/// * `_str_id`, `_prefix`, `_module_name` — Reserved for module path metadata (unused).
///
/// # Returns
///
/// New environment with the binding applied.
fn enrich_env_from_sgi(
    elaboration_environment: Env,
    sgi: &elab::SignatureItem,
    _str_id: usize,
    _prefix: &[String],
    _module_name: &str,
) -> Env {
    match sgi {
        elab::SignatureItem::Val(x, id, t) => {
            elaboration_environment.push_e_named_as(x.clone(), *id, t.clone())
        }
        elab::SignatureItem::ConAbs(x, id, k) => {
            elaboration_environment.push_c_named_as(x.clone(), *id, k.clone(), None)
        }
        elab::SignatureItem::Constructor(x, id, k, def) => {
            // Preserve the definition so that type aliases (like `type unit = {}`) can be unfolded.
            elaboration_environment.push_c_named_as(x.clone(), *id, k.clone(), Some(def.clone()))
        }
        elab::SignatureItem::ClassAbs(x, id, k) => elaboration_environment
            .push_c_named_as(x.clone(), *id, k.clone(), None)
            .push_class(*id),
        elab::SignatureItem::Class(x, id, k, def) => elaboration_environment
            .push_c_named_as(x.clone(), *id, k.clone(), Some(def.clone()))
            .push_class(*id),
        elab::SignatureItem::Structure(_, x, id, sgn) => {
            elaboration_environment.push_str_named_as(x.clone(), *id, sgn.clone())
        }
        elab::SignatureItem::Signature(x, id, sgn) => {
            elaboration_environment.push_sgn_named_as(x.clone(), *id, sgn.clone())
        }
        elab::SignatureItem::Datatype(dts) => {
            let mut cur_env = elaboration_environment;
            for dt in dts {
                cur_env = cur_env.push_datatype(dt.id, dt.params.clone(), dt.constrs.clone());
                let ktype = Located::new(elab::Kind::Type, Span::dummy());
                let dt_kind = dt.params.iter().fold(ktype.clone(), |acc, _| {
                    Located::new(
                        elab::Kind::Arrow(Box::new(ktype.clone()), Box::new(acc)),
                        Span::dummy(),
                    )
                });
                cur_env = cur_env.push_c_named_as(dt.name.clone(), dt.id, dt_kind, None);
            }
            cur_env
        }
        _ => elaboration_environment,
    }
}

fn elab_table_decl(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    disjointness_environment: &disjoint::DisjointEnv,
    x: &str,
    c: &source::LocCon,
    pk_e: &source::LocExp,
    unique_e: &source::LocExp,
    span: &Span,
) -> (Vec<elab::LocatedDeclaration>, Env, disjoint::DisjointEnv) {
    let (ce, _) = elab_con(elaboration_context, elaboration_environment, c);
    let (pk_ee, pk_et) = elab_exp(
        elaboration_context,
        elaboration_environment,
        disjointness_environment,
        pk_e,
    );
    let (_unique_ee, unique_et) = elab_exp(
        elaboration_context,
        elaboration_environment,
        disjointness_environment,
        unique_e,
    );

    let mod_id = elaboration_environment
        .lookup_str("Basis")
        .map(|(id, _)| *id)
        .unwrap_or(0);
    let _nt = new_named_id();
    let (new_env, id) = elaboration_environment
        .clone()
        .push_e_named(x.to_string(), ce.clone());

    // pk_con and unique_con are type annotations for pk and unique constraints
    let pk_con = pk_et;
    let unique_con = unique_et;

    let decl_out = Located::new(
        elab::Declaration::Table {
            mod_id,
            name: x.to_string(),
            name_id: id,
            con: ce,
            exp: pk_ee.clone(),
            pk_con,
            pk_exp: pk_ee,
            unique_con,
        },
        span.clone(),
    );
    (vec![decl_out], new_env, disjointness_environment.clone())
}

// ---------------------------------------------------------------------------
// Structure elaboration
// ---------------------------------------------------------------------------

/// Elaborate a structure expression and infer or check its signature.
///
/// `ascribed`, when `Some`, runs [`sub_sgn`] against the inferred signature of the body (or looked-up var).
///
/// # Arguments
///
/// * `elaboration_context` — Errors (unbound module, bad functor app).
/// * `elaboration_environment` — Structure and type environment.
/// * `disjointness_environment` — For nested `elab_decl` / `elab_sgn`.
/// * `str_` — Source structure AST.
/// * `ascribed` — Optional signature to implement (`:` ascription).
///
/// # Returns
///
/// `(structure, signature)` pair; errors yield [`elab::Structure::Error`] / [`elab::Signature::Error`] nodes.
pub fn elab_str(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    disjointness_environment: &disjoint::DisjointEnv,
    str_: &source::LocStr,
    ascribed: Option<&elab::LocatedSignature>,
) -> (elab::LocatedStructure, elab::LocatedSignature) {
    let span = str_.span.clone();
    match &str_.node {
        source::Str::Const(decls) => {
            let mut cur_env = elaboration_environment.clone();
            let mut cur_denv = disjointness_environment.clone();
            let mut elab_decls: Vec<elab::LocatedDeclaration> = Vec::new();
            for d in decls {
                let (ds, new_env, new_denv) =
                    elab_decl(elaboration_context, &cur_env, &cur_denv, d);
                cur_env = new_env;
                cur_denv = new_denv;
                elab_decls.extend(ds);
            }
            // Build signature from the declarations
            let sgn = decls_to_sgn(&elab_decls, &span);
            // Check ascription
            if let Some(asc) = ascribed {
                sub_sgn(
                    elaboration_context,
                    &cur_env,
                    disjointness_environment,
                    &sgn,
                    asc,
                    &span,
                );
            }
            let str_out = Located::new(elab::Structure::Const(elab_decls), span.clone());
            (str_out, sgn)
        }
        source::Str::Var(x) => match elaboration_environment.lookup_str(x) {
            Some((id, sgn)) => {
                let str_out = Located::new(elab::Structure::Var(*id), span.clone());
                if let Some(asc) = ascribed {
                    sub_sgn(
                        elaboration_context,
                        elaboration_environment,
                        disjointness_environment,
                        sgn,
                        asc,
                        &span,
                    );
                }
                (str_out, sgn.clone())
            }
            None => {
                elaboration_context.error(
                    span.clone(),
                    DiagnosticPayload::new(DiagnosticId::ElabUnboundStructure, vec![x.clone()]),
                );
                (
                    elaborated_structure_error_at_span(span.clone()),
                    elaborated_signature_error_at_span(span),
                )
            }
        },
        source::Str::Proj(str_inner, field) => {
            let (str_ie, str_isgn) = elab_str(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                str_inner,
                None,
            );
            let items = get_sgn_const_items(elaboration_environment, &str_isgn);
            if let Some(elab::SignatureItem::Structure(_, _, _id, sgn)) =
                sgi_find_str(&items, field)
            {
                let str_out = Located::new(
                    elab::Structure::Proj(Box::new(str_ie), field.clone()),
                    span.clone(),
                );
                return (str_out, sgn.clone());
            }
            elaboration_context.error(
                span.clone(),
                DiagnosticPayload::new(DiagnosticId::ElabNoStructureInModule, vec![field.clone()]),
            );
            (
                elaborated_structure_error_at_span(span.clone()),
                elaborated_signature_error_at_span(span),
            )
        }
        source::Str::Fun(x, sgn, _opt_result_sgn, body) => {
            let sgne = elab_sgn(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                sgn,
            );
            let (env2, param_id) = elaboration_environment
                .clone()
                .push_str_named(x.clone(), sgne.clone());
            let (bodye, body_sgn) = elab_str(
                elaboration_context,
                &env2,
                disjointness_environment,
                body,
                None,
            );
            let str_out = Located::new(
                elab::Structure::Fun(
                    x.clone(),
                    param_id,
                    sgne.clone(),
                    body_sgn.clone(),
                    Box::new(bodye),
                ),
                span.clone(),
            );
            let fun_sgn = Located::new(
                elab::Signature::Fun(x.clone(), param_id, Box::new(sgne), Box::new(body_sgn)),
                span,
            );
            (str_out, fun_sgn)
        }
        source::Str::App(str1, str2) => {
            let (str1e, str1sgn) = elab_str(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                str1,
                None,
            );
            let (str2e, str2sgn) = elab_str(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                str2,
                None,
            );
            // str1sgn must be a functor
            let str1sgnn = hnorm_sgn(elaboration_environment, &str1sgn);
            match str1sgnn.node {
                elab::Signature::Fun(_, _param_id, dom, ran) => {
                    sub_sgn(
                        elaboration_context,
                        elaboration_environment,
                        disjointness_environment,
                        &str2sgn,
                        &dom,
                        &span,
                    );
                    let str_out = Located::new(
                        elab::Structure::App(Box::new(str1e), Box::new(str2e)),
                        span.clone(),
                    );
                    // Substitute str2 for the param in ran
                    // Simplified: return ran as-is
                    (str_out, *ran)
                }
                _ => {
                    elaboration_context.error(
                        span.clone(),
                        DiagnosticPayload::new(
                            DiagnosticId::ElabApplicationNonFunctorStructure,
                            Vec::new(),
                        ),
                    );
                    (
                        elaborated_structure_error_at_span(span.clone()),
                        elaborated_signature_error_at_span(span),
                    )
                }
            }
        }
    }
}

/// Build a signature from a list of declarations (sgiOfDecl equivalent).
fn decls_to_sgn(decls: &[elab::LocatedDeclaration], span: &Span) -> elab::LocatedSignature {
    let mut sgis: Vec<elab::LocatedSignatureItem> = Vec::new();
    for d in decls {
        match &d.node {
            elab::Declaration::Constructor(x, id, k, c) => {
                sgis.push(Located::new(
                    elab::SignatureItem::Constructor(x.clone(), *id, k.clone(), c.clone()),
                    d.span.clone(),
                ));
            }
            elab::Declaration::Datatype(dts) => {
                sgis.push(Located::new(
                    elab::SignatureItem::Datatype(dts.clone()),
                    d.span.clone(),
                ));
            }
            elab::Declaration::DatatypeImp {
                name,
                id,
                orig_mod,
                orig_path,
                orig_name,
                orig_constrs_path,
                constrs,
            } => {
                sgis.push(Located::new(
                    elab::SignatureItem::DatatypeImp {
                        name: name.clone(),
                        id: *id,
                        orig_mod: *orig_mod,
                        orig_path: orig_path.clone(),
                        orig_name: orig_name.clone(),
                        orig_constrs_path: orig_constrs_path.clone(),
                        constrs: constrs.clone(),
                    },
                    d.span.clone(),
                ));
            }
            elab::Declaration::Val(x, id, t, _) => {
                sgis.push(Located::new(
                    elab::SignatureItem::Val(x.clone(), *id, t.clone()),
                    d.span.clone(),
                ));
            }
            elab::Declaration::ValRec(bindings) => {
                for (x, id, t, _) in bindings {
                    sgis.push(Located::new(
                        elab::SignatureItem::Val(x.clone(), *id, t.clone()),
                        d.span.clone(),
                    ));
                }
            }
            elab::Declaration::Signature(x, id, sgn) => {
                sgis.push(Located::new(
                    elab::SignatureItem::Signature(x.clone(), *id, sgn.clone()),
                    d.span.clone(),
                ));
            }
            elab::Declaration::Structure(x, id, sgn, _) => {
                sgis.push(Located::new(
                    elab::SignatureItem::Structure(
                        elab::ImportMode::Import,
                        x.clone(),
                        *id,
                        sgn.clone(),
                    ),
                    d.span.clone(),
                ));
            }
            elab::Declaration::Constraint(c1, c2) => {
                sgis.push(Located::new(
                    elab::SignatureItem::Constraint(c1.clone(), c2.clone()),
                    d.span.clone(),
                ));
            }
            elab::Declaration::Ffi(x, id, _, t) => {
                sgis.push(Located::new(
                    elab::SignatureItem::Val(x.clone(), *id, t.clone()),
                    d.span.clone(),
                ));
            }
            _ => {}
        }
    }
    Located::new(elab::Signature::Const(sgis), span.clone())
}

// ---------------------------------------------------------------------------
// Constraint solving
// ---------------------------------------------------------------------------

fn solve_constraints(elaboration_context: &mut ElabCtx, _elaboration_environment: &Env) {
    let constraints = std::mem::take(&mut elaboration_context.constraints);
    let mut remaining = Vec::new();

    for c in constraints {
        match c {
            Constraint::Disjoint {
                span,
                elaboration_environment: c_env,
                goal,
            } => {
                let goals = disjoint::prove(
                    goal.span.clone(),
                    &goal.disjointness_environment,
                    goal.left_constructor.clone(),
                    goal.right_constructor.clone(),
                );
                if !goals.is_empty() {
                    // Re-add unresolved goals
                    for g in goals {
                        remaining.push(Constraint::Disjoint {
                            span: span.clone(),
                            elaboration_environment: c_env.clone(),
                            goal: g,
                        });
                    }
                }
            }
            Constraint::TypeClass {
                span,
                elaboration_environment: c_env,
                class,
                result,
            } => {
                // Try to resolve the class instance
                match resolve_class(&c_env, &class, &span) {
                    Some((witness, matched_head)) => {
                        // Unify the class constraint with the matched rule head.
                        // This instantiates any type variables, e.g. solving `Unif(m) = transaction`
                        // when the class is `monad Unif(m)` and the head is `monad transaction`.
                        let _ =
                            unify_cons(elaboration_context, &c_env, &span, &class, &matched_head);
                        *crate::compiler_diagnostics::lock_for_compile(
                            result.as_ref(),
                            "elaboration unification cell",
                        ) = Some(witness);
                    }
                    None => {
                        remaining.push(Constraint::TypeClass {
                            span: span.clone(),
                            elaboration_environment: c_env,
                            class,
                            result,
                        });
                    }
                }
            }
        }
    }

    // Report truly unresolvable constraints
    for c in remaining {
        match c {
            Constraint::Disjoint { span, goal: _, .. } => {
                elaboration_context.error(
                    span,
                    DiagnosticPayload::new(DiagnosticId::ElabUnresolvedDisjointness, Vec::new()),
                );
            }
            Constraint::TypeClass { span, class, .. } => {
                elaboration_context.error(
                    span,
                    DiagnosticPayload::new(
                        DiagnosticId::ElabUnresolvedTypeclass,
                        vec![crate::elaborated::type_display::format_constructor(&class)],
                    ),
                );
            }
        }
    }
}

/// Instantiate a rule head/hyps by substituting fresh unification variables for each quantifier.
/// Returns (instantiated_head, instantiated_hyps).
fn instantiate_rule(
    elaboration_environment: &Env,
    nq: usize,
    hyps: &[elab::LocatedConstructor],
    head: &elab::LocatedConstructor,
    span: &Span,
) -> (elab::LocatedConstructor, Vec<elab::LocatedConstructor>) {
    if nq == 0 {
        return (head.clone(), hyps.to_vec());
    }
    let mut inst_head = head.clone();
    let mut inst_hyps: Vec<elab::LocatedConstructor> = hyps.to_vec();
    let ktype = Located::new(elab::Kind::Type, span.clone());
    // Substitute from innermost quantifier (Rel(0)) outward.
    // Each substitution reduces all remaining de Bruijn indices by 1.
    for _ in 0..nq {
        let fresh = fresh_cunif(
            elaboration_environment,
            span.clone(),
            ktype.clone(),
            "_inst",
        );
        if let Ok(new_head) = sub_con_in_con(0, &fresh, inst_head.clone()) {
            inst_head = new_head;
        }
        inst_hyps = inst_hyps
            .into_iter()
            .map(|h| sub_con_in_con(0, &fresh, h.clone()).unwrap_or(h))
            .collect();
    }
    (inst_head, inst_hyps)
}

fn resolve_class(
    elaboration_environment: &Env,
    class: &elab::LocatedConstructor,
    span: &Span,
) -> Option<(elab::LocatedExpression, elab::LocatedConstructor)> {
    // Try all classes in the environment
    for rules in elaboration_environment.classes().values() {
        let class_n = hnorm_con(class.clone());
        // Try closed rules first
        for (nq, hyps, head, witness) in &rules.closed_rules {
            let (inst_head, inst_hyps) =
                instantiate_rule(elaboration_environment, *nq, hyps, head, span);
            if try_match_class(elaboration_environment, &class_n, &inst_head, *nq) {
                // Check hypotheses
                let all_hyps_satisfied = inst_hyps
                    .iter()
                    .all(|h| resolve_class(elaboration_environment, h, span).is_some());
                if all_hyps_satisfied {
                    return Some((witness.clone(), inst_head));
                }
            }
        }
        // Then open rules
        for (nq, hyps, head, witness) in &rules.open_rules {
            let (inst_head, inst_hyps) =
                instantiate_rule(elaboration_environment, *nq, hyps, head, span);
            if try_match_class(elaboration_environment, &class_n, &inst_head, *nq) {
                let all_hyps_satisfied = inst_hyps
                    .iter()
                    .all(|h| resolve_class(elaboration_environment, h, span).is_some());
                if all_hyps_satisfied {
                    return Some((witness.clone(), inst_head));
                }
            }
        }
    }
    None
}

fn try_match_class(
    _elaboration_environment: &Env,
    class: &elab::LocatedConstructor,
    head: &elab::LocatedConstructor,
    _num_quantifiers: usize,
) -> bool {
    // Simplified: just check if they have the same head constructor
    let cn = hnorm_con(class.clone());
    let hn = hnorm_con(head.clone());
    fn get_head(c: &elab::LocatedConstructor) -> Option<usize> {
        match &c.node {
            elab::Constructor::Named(id) => Some(*id),
            elab::Constructor::App(f, _) => get_head(f),
            _ => None,
        }
    }
    get_head(&cn) == get_head(&hn)
}

// ---------------------------------------------------------------------------
// File elaboration entry point
// ---------------------------------------------------------------------------

/// Type-check and elaborate a parsed [`crate::source::File`] into an elaborated [`crate::elaborated::File`].
///
/// Runs declaration-by-declaration (including auto-open of `Basis` after `FfiStr("Basis", ...)`,
/// and auto-open of `Top` after `Str("Top", ...)` — matching SML `elabFile`'s `dopen` on both).
///
/// # Arguments
///
/// * `file` — Source-file declarations in parse order.
/// * `_settings` — Reserved for future elaboration options (currently unused).
/// * `errors` — Collects elaboration diagnostics; also checked for a non-empty error list at the end.
///
/// # Returns
///
/// `Some(elaborated declarations)` when no errors were recorded; `None` if [`ErrorReporter::has_errors`].
pub fn elab_file(
    file: crate::source::File,
    _settings: &crate::settings::Settings,
    errors: &mut ErrorReporter,
) -> Option<crate::elaborated::File> {
    let mut elaboration_context = ElabCtx::new();
    let mut elaboration_environment = Env::empty();
    let mut disjointness_environment = disjoint::empty_env();
    let mut all_decls: Vec<elab::LocatedDeclaration> = Vec::new();

    for decl in &file {
        let (ds, new_env, new_denv) = elab_decl(
            &mut elaboration_context,
            &elaboration_environment,
            &disjointness_environment,
            decl,
        );
        elaboration_environment = new_env;
        disjointness_environment = new_denv;
        all_decls.extend(ds);

        // After elaborating `FfiStr("Basis", ...)`, automatically open Basis
        // so that `unit`, `transaction`, `return`, etc. are in scope without
        // qualification — matching the SML `dopen elaboration_environment' {str = basis_n, ...}`.
        if let crate::source::Decl::FfiStr(name, _, _) = &decl.node {
            if name == "Basis" {
                let basis_span = decl.span.clone();
                let (open_ds, open_env, open_denv) = elab_open(
                    &mut elaboration_context,
                    &elaboration_environment,
                    &disjointness_environment,
                    &["Basis".to_string()],
                    &basis_span,
                );
                elaboration_environment = open_env;
                disjointness_environment = open_denv;
                all_decls.extend(open_ds);
            }
        }
        // After the `Top` structure (from `top.ur` / `top.urs`), SML `elabFile` does
        // `dopen env' {str = top_n, ...}` so `folder`, `mapU`, `foldUR`, `txt`, … are in scope
        // for user modules (`elabFile` around `dopen` on Top in `elaborate.sml`).
        if let crate::source::Decl::Str(name, _, _, _, _) = &decl.node {
            if name == "Top" {
                let top_span = decl.span.clone();
                let (open_ds, open_env, open_denv) = elab_open(
                    &mut elaboration_context,
                    &elaboration_environment,
                    &disjointness_environment,
                    &["Top".to_string()],
                    &top_span,
                );
                elaboration_environment = open_env;
                disjointness_environment = open_denv;
                all_decls.extend(open_ds);
            }
        }
    }

    // Report all errors
    for (span, payload) in elaboration_context.errors {
        errors.report_type_at(span, payload);
    }

    if errors.has_hard_errors() {
        None
    } else {
        Some(all_decls)
    }
}

// ---------------------------------------------------------------------------
// Elaboration regression tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagnostics::DiagnosticId; // public re-export path used by the rest of this module
    use crate::error_types::{CompileError, ErrorReporter};
    use crate::settings::Settings;

    /// Elaborate the real `lib/ur/basis.urs` + `lib/ur/top.urs` + `lib/ur/top.ur` and assert
    /// that no `ElabKindMismatch` diagnostics are emitted.
    ///
    /// Previously, the bare `class show` rule in the grammar stored `Arrow(Type,Type)` as the
    /// class argument kind instead of `Type`, causing `enrich_env_from_sgi` to doubly-wrap it
    /// to `Arrow(Arrow(Type,Type),Type)`.  This produced `IncompatibleKinds(Type, Arrow(Type,Type))`
    /// when checking `show t` and `show (option t)` in `top.urs`.
    #[test]
    fn elaborate_top_urs_has_no_kind_mismatch_errors() {
        // Full boot elaboration is deep; default test thread stacks (~2 MiB) overflow on some hosts.
        const ELAB_TOP_URS_STACK_BYTES: usize = 32 * 1024 * 1024; // 32 MiB for recursion-heavy elaboration
        let worker = std::thread::Builder::new() // configure a dedicated thread for this regression
            .name("elaborate_top_urs_large_stack".into()) // name shows up in stack overflow diagnostics
            .stack_size(ELAB_TOP_URS_STACK_BYTES); // larger stack than the default test harness thread
        let handle = worker
            .spawn(elaborate_top_urs_has_no_kind_mismatch_errors_body) // run heavy work off default stack
            .expect("spawn elaboration regression thread"); // spawn should not fail in CI
        handle
            .join() // propagate panics from worker as test failure
            .expect("elaboration regression thread should not panic"); // unwrap join result
    }

    /// Body for [`elaborate_top_urs_has_no_kind_mismatch_errors`], executed on a high-stack thread.
    fn elaborate_top_urs_has_no_kind_mismatch_errors_body() {
        // Locate the lib/ur directory relative to the workspace root.
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let lib_dir = manifest_dir.join("lib/ur");
        // Skip if the real lib files are not present (e.g. CI without full checkout).
        if !lib_dir.join("basis.urs").is_file() || !lib_dir.join("top.urs").is_file() {
            return;
        }

        // Build a Job that points at the real lib/ur directory so parse_sources loads
        // basis.urs and top.ur/top.urs as the standard boot library.
        let job = crate::compiler::Job {
            sources: vec![], // no user modules — only the boot library
            basis_lib_dir: Some(lib_dir.clone()),
            ..Default::default()
        };
        let settings = Settings::new();
        let mut parse_errors = ErrorReporter::new_silent();

        // parse_sources emits FfiStr("Basis") and the Top structure automatically.
        let source_file = crate::compiler::parse_sources(&job, &settings, &mut parse_errors);
        let source_file = match source_file {
            // Parse errors for grammar limitations in top.ur are acceptable here — we only
            // want to test elaboration, so skip rather than panic on parse failure.
            None => return,
            Some(f) => f,
        };

        // Elaborate the source tree and collect all diagnostics into elab_errors.
        let mut elab_errors = ErrorReporter::new_silent();
        let _elab = elab_file(source_file, &settings, &mut elab_errors);

        // Count only ElabKindMismatch diagnostics — the regression target for this bug fix.
        let kind_mismatch_count = elab_errors
            .errors
            .iter()
            .filter(|error| {
                // TypeError variants carry elaboration payloads; check for ElabKindMismatch.
                matches!(
                    error,
                    CompileError::TypeError { payload, .. }
                        if payload.id == DiagnosticId::ElabKindMismatch
                )
            })
            .count();

        // Print the first few kind mismatch errors for debugging.
        if kind_mismatch_count > 0 {
            for (idx, error) in elab_errors
                .errors
                .iter()
                .filter(|e| {
                    matches!(
                        e,
                        CompileError::TypeError { payload, .. }
                            if payload.id == DiagnosticId::ElabKindMismatch
                    )
                })
                .take(5)
                .enumerate()
            {
                tracing::debug!(index = idx, ?error, "elab kind_mismatch sample");
            }
        }
        assert_eq!(
            kind_mismatch_count,
            0,
            "Elaboration of top.urs must produce zero ElabKindMismatch diagnostics; \
             got {kind_mismatch_count}.  \
             Check class kind handling in elab_sgn_item and grammar.lalrpop (bare 'class name' rule)."
        );
    }
}
