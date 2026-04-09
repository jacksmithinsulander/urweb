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
//!
//! ## Input-shaped depth and iteration bounds (Power of Ten / LangSec)
//!
//! Elaboration follows solver and normalization graphs that must not diverge on hostile or buggy inputs.
//! Inventory of **explicit caps** in this crate and [`crate::elaborated::type_operations`]:
//! - [`unify_cons_inner`] — hard depth cap (see numeric guard in that function) returning
//!   [`FailedToUnifyConstructors::UnificationRecursionLimitExceeded`].
//! - `elab_con` / `elab_exp` — thread-local depth limits (see their doc comments; constructor 500, expression 200).
//! - [`CHASE_KIND_UNIFICATION_HEAD_MAX_STEPS`] — [`chase_kind_unification_head`] (`Kind::Unif` alias chains).
//! - [`ELAB_CON_HEAD_MAX_STEPS`] — [`elab_con_head`] implicit [`elab::Constructor::KApp`] insertion.
//! - [`RECORD_SUMMARY_MAX_DEPTH`] — [`record_summary`] recursion for row shapes (`Concat`, named unfold).
//! - [`crate::elaborated::environment::hnorm_sgn`] — `Signature::Var` cycles detected via a visited set.
//! - [`crate::elaborated::type_operations::hnorm_con`] — thread-local depth 200; solved-[`elab::Constructor::Unif`]
//!   peel chains additionally capped in `type_operations` (`PEEL_SOLVED_CONSTRUCTOR_UNIF_CHAIN_MAX_STEPS`).

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use crate::diagnostics::{DiagnosticId, DiagnosticPayload};
use crate::elaborated as elab;
use crate::elaborated::disjointness_analysis as disjoint;
use crate::elaborated::environment::{
    hnorm_con_expression_head, hnorm_sgn, new_named_id, ConstructorInfo, Env, VarLookup,
};
use crate::elaborated::type_operations::{
    cons_eq_simple, hnorm_con, lift_kind_in_con, mlift_con_in_con, occurs_cunif, reduce_con,
    squish_con, sub_con_in_con, sub_kind_in_con, sub_kind_in_kind, CantSquish,
};
use crate::error_types::{ErrorReporter, Located, Span};
use crate::primitives::Prim;
use crate::source::{self};

// ---------------------------------------------------------------------------
// Global state (mirrors SML refs)
// ---------------------------------------------------------------------------

/// Counter for fresh constructor unification variables.
static CUNIF_COUNT: AtomicUsize = AtomicUsize::new(0);
static DEBUG_FOLDER_UNIFY_LOG_COUNT: AtomicUsize = AtomicUsize::new(0);
static DEBUG_TOP_SUBSGI_LOG_COUNT: AtomicUsize = AtomicUsize::new(0);

thread_local! {
    static DEBUG_UNIFY_PAIR_STACK: RefCell<Vec<(String, String)>> = const { RefCell::new(Vec::new()) };
}

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
    _elaboration_environment: &Env,
    span: Span,
    kind: elab::LocatedKind,
    name: &str,
) -> elab::LocatedConstructor {
    fresh_cunif_with_nesting(span, kind, name, 0)
}

fn fresh_cunif_with_nesting(
    span: Span,
    kind: elab::LocatedKind,
    name: &str,
    nesting_level: usize,
) -> elab::LocatedConstructor {
    let _id = fresh_cunif_id();
    let r = Arc::new(Mutex::new(elab::CUnif::Unknown));
    Located::new(
        elab::Constructor::Unif(
            nesting_level,
            span.clone(),
            Box::new(kind),
            name.to_string(),
            r,
        ),
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
        // The same parity rule applies when a generic kind parameter is specialized to `Unit`
        // through row-folder helpers like `mapUX` / `foldUR*` in `lib/ur/top.ur`.
        (elab::Kind::Rel(_), elab::Kind::Unit) | (elab::Kind::Unit, elab::Kind::Rel(_)) => Ok(()),
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
        if std::env::var("URWEB_DEBUG_TOP_KIND_MISMATCH")
            .ok()
            .as_deref()
            == Some("1")
            && span.file.ends_with("/lib/ur/top.ur")
        {
            eprintln!(
                "top kind mismatch debug line={} got_kind={} expected_kind={} constructor={}",
                span.first.line,
                crate::elaborated::type_display::format_kind(got),
                crate::elaborated::type_display::format_kind(expected),
                crate::elaborated::type_display::format_constructor(_constructor_under_check),
            );
        }
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

/// Upper bound on [`elab::Kind::Unif`] / [`elab::Kind::TupleUnif`] chase steps in [`chase_kind_unification_head`].
///
/// Breaks cycles and unbounded chains without relying on stack depth (Power-of-Ten style loop bound).
const CHASE_KIND_UNIFICATION_HEAD_MAX_STEPS: usize = 8192;

/// Follow solved [`elab::Kind::Unif`] / [`elab::Kind::TupleUnif`] cells to the representative head.
///
/// Implemented as a loop so long union-find chains (no path compression) cannot overflow the stack.
/// Step cap yields [`elab::Kind::Error`] so elaboration degrades like other stuck normalization.
fn chase_kind_unification_head(mut kind: elab::LocatedKind) -> elab::LocatedKind {
    for _ in 0..CHASE_KIND_UNIFICATION_HEAD_MAX_STEPS {
        let reference = match &kind.node {
            elab::Kind::Unif(_, _, reference) | elab::Kind::TupleUnif(_, _, reference) => reference,
            _ => return kind, // Concrete kind head: chase finished.
        };
        let guard = crate::compiler_diagnostics::lock_for_compile(
            reference.as_ref(),
            "elaboration unification cell",
        );
        if let elab::KUnif::Known(inner) = &*guard {
            let next = *inner.clone();
            drop(guard);
            kind = next; // Continue chasing through solved alias.
        } else {
            drop(guard);
            return kind; // Unknown cell: this unifier is the representative head.
        }
    }
    let span = kind.span.clone();
    Located::new(elab::Kind::Error, span) // Cycle or runaway alias chain.
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

fn constructor_head_after_apps(
    constructor: &elab::LocatedConstructor,
) -> &elab::LocatedConstructor {
    match &constructor.node {
        elab::Constructor::App(function_constructor, _)
        | elab::Constructor::KApp(function_constructor, _) => {
            constructor_head_after_apps(function_constructor)
        }
        _ => constructor,
    }
}

fn constructor_is_folder_head(
    elaboration_environment: &Env,
    constructor: &elab::LocatedConstructor,
) -> bool {
    let normalized_constructor =
        hnorm_con_expression_head(elaboration_environment, constructor.clone());
    let normalized_head = constructor_head_after_apps(&normalized_constructor);
    match &normalized_head.node {
        elab::Constructor::Named(id) => elaboration_environment
            .lookup_c_named(*id)
            .map(|(name, _, _)| name == "folder")
            .unwrap_or(false),
        elab::Constructor::ModProj(_, _, name) => name == "folder",
        _ => false,
    }
}

fn expand_folder_constructor_application(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    constructor: &elab::LocatedConstructor,
) -> Option<elab::LocatedConstructor> {
    let normalized_constructor =
        hnorm_con_expression_head(elaboration_environment, constructor.clone());
    let elab::Constructor::App(folder_head, row_constructor) = &normalized_constructor.node else {
        return None;
    };
    if !constructor_is_folder_head(elaboration_environment, folder_head) {
        return None;
    }

    let row_kind = hnorm_kind(kindof(
        elaboration_context,
        elaboration_environment,
        row_constructor.as_ref(),
    ));
    let elab::Kind::Record(field_kind) = &row_kind.node else {
        return None;
    };

    let span = normalized_constructor.span.clone();
    let unit_kind = Located::new(elab::Kind::Unit, span.clone());
    let name_kind = Located::new(elab::Kind::Name, span.clone());
    let field_kind = field_kind.as_ref().clone();
    let row_kind_constructor = Located::new(
        elab::Kind::Record(Box::new(field_kind.clone())),
        span.clone(),
    );
    let tf_kind = Located::new(
        elab::Kind::Arrow(
            Box::new(row_kind_constructor.clone()),
            Box::new(Located::new(elab::Kind::Type, span.clone())),
        ),
        span.clone(),
    );

    let singleton_name_row = Located::new(
        elab::Constructor::Record(
            Box::new(Located::new(
                elab::Kind::Record(Box::new(unit_kind)),
                span.clone(),
            )),
            vec![(
                Located::new(elab::Constructor::Rel(2), span.clone()),
                Located::new(elab::Constructor::Unit, span.clone()),
            )],
        ),
        span.clone(),
    );
    let singleton_value_row = Located::new(
        elab::Constructor::Record(
            Box::new(row_kind_constructor.clone()),
            vec![(
                Located::new(elab::Constructor::Rel(2), span.clone()),
                Located::new(elab::Constructor::Rel(1), span.clone()),
            )],
        ),
        span.clone(),
    );
    let tf_of_rest = Located::new(
        elab::Constructor::App(
            Box::new(Located::new(elab::Constructor::Rel(3), span.clone())),
            Box::new(Located::new(elab::Constructor::Rel(0), span.clone())),
        ),
        span.clone(),
    );
    let tf_of_extended_rest = Located::new(
        elab::Constructor::App(
            Box::new(Located::new(elab::Constructor::Rel(3), span.clone())),
            Box::new(Located::new(
                elab::Constructor::Concat(
                    Box::new(singleton_value_row),
                    Box::new(Located::new(elab::Constructor::Rel(0), span.clone())),
                ),
                span.clone(),
            )),
        ),
        span.clone(),
    );
    let step_type = Located::new(
        elab::Constructor::TCFun(
            elab::Explicitness::Explicit,
            "nm".to_string(),
            Box::new(name_kind),
            Box::new(Located::new(
                elab::Constructor::TCFun(
                    elab::Explicitness::Explicit,
                    "v".to_string(),
                    Box::new(field_kind.clone()),
                    Box::new(Located::new(
                        elab::Constructor::TCFun(
                            elab::Explicitness::Explicit,
                            "r".to_string(),
                            Box::new(row_kind_constructor.clone()),
                            Box::new(Located::new(
                                elab::Constructor::TDisjoint(
                                    Box::new(singleton_name_row),
                                    Box::new(Located::new(elab::Constructor::Rel(0), span.clone())),
                                    Box::new(Located::new(
                                        elab::Constructor::TFun(
                                            Box::new(tf_of_rest),
                                            Box::new(tf_of_extended_rest),
                                        ),
                                        span.clone(),
                                    )),
                                ),
                                span.clone(),
                            )),
                        ),
                        span.clone(),
                    )),
                ),
                span.clone(),
            )),
        ),
        span.clone(),
    );
    let empty_row = Located::new(
        elab::Constructor::Record(Box::new(row_kind_constructor.clone()), Vec::new()),
        span.clone(),
    );
    let tf_of_empty = Located::new(
        elab::Constructor::App(
            Box::new(Located::new(elab::Constructor::Rel(0), span.clone())),
            Box::new(empty_row),
        ),
        span.clone(),
    );
    let tf_of_target_row = Located::new(
        elab::Constructor::App(
            Box::new(Located::new(elab::Constructor::Rel(0), span.clone())),
            Box::new(row_constructor.as_ref().clone()),
        ),
        span.clone(),
    );

    Some(Located::new(
        elab::Constructor::TCFun(
            elab::Explicitness::Explicit,
            "tf".to_string(),
            Box::new(tf_kind),
            Box::new(Located::new(
                elab::Constructor::TFun(
                    Box::new(step_type),
                    Box::new(Located::new(
                        elab::Constructor::TFun(Box::new(tf_of_empty), Box::new(tf_of_target_row)),
                        span.clone(),
                    )),
                ),
                span.clone(),
            )),
        ),
        span,
    ))
}

fn is_folder_constructor_application(
    elaboration_environment: &Env,
    constructor: &elab::LocatedConstructor,
) -> bool {
    let normalized_constructor =
        hnorm_con_expression_head(elaboration_environment, constructor.clone());
    match &normalized_constructor.node {
        elab::Constructor::App(folder_head, _) => {
            constructor_is_folder_head(elaboration_environment, folder_head)
        }
        _ => false,
    }
}

fn constructor_has_unit_kind(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    constructor: &elab::LocatedConstructor,
) -> bool {
    match &hnorm_con_expression_head(elaboration_environment, constructor.clone()).node {
        elab::Constructor::Rel(index) => elaboration_environment
            .lookup_c_rel(*index)
            .ok()
            .is_some_and(|(_, kind)| matches!(hnorm_kind(kind.clone()).node, elab::Kind::Unit)),
        elab::Constructor::Named(id) => elaboration_environment
            .lookup_c_named(*id)
            .ok()
            .is_some_and(|(_, kind, _)| matches!(hnorm_kind(kind.clone()).node, elab::Kind::Unit)),
        elab::Constructor::Unit => true,
        elab::Constructor::Unif(_, _, kind, _, _) => {
            matches!(hnorm_kind(kind.as_ref().clone()).node, elab::Kind::Unit)
        }
        _ => matches!(
            hnorm_kind(kindof(
                elaboration_context,
                elaboration_environment,
                constructor,
            ))
            .node,
            elab::Kind::Unit
        ),
    }
}

fn is_class_or_folder(
    elaboration_environment: &Env,
    constructor: &elab::LocatedConstructor,
) -> bool {
    match elaboration_environment.is_class(constructor) {
        true => true,
        false => constructor_is_folder_head(elaboration_environment, constructor),
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
    /// A row unification deferred because `may_delay` was true when it was first attempted.
    ///
    /// The constraint is retried in `solve_constraints` once more unification variables may
    /// have been filled in by elaborating the rest of the declaration body.
    RowUnification {
        /// Source location that triggered this row-unification attempt.
        span: Span,
        /// Environment snapshot at the point of deferral.
        elaboration_environment: Env,
        /// Left-hand row constructor.
        left_constructor: elab::LocatedConstructor,
        /// Right-hand row constructor.
        right_constructor: elab::LocatedConstructor,
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

/// Maximum implicit [`elab::Constructor::KApp`] wrappers [`elab_con_head`] may insert (pathological kind fun stack).
const ELAB_CON_HEAD_MAX_STEPS: usize = 65536;

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
    // Up to [`ELAB_CON_HEAD_MAX_STEPS`] implicit [`Constructor::KApp`] wrappers; then return remaining kind.
    for _ in 0..ELAB_CON_HEAD_MAX_STEPS {
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
    let normalized_kind = hnorm_kind(kind);
    (constructor, normalized_kind)
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
            let kn = hnorm_kind(k1.clone());
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
                    if std::env::var("URWEB_DEBUG_CON_APP_NON_ARROW")
                        .ok()
                        .as_deref()
                        == Some("1")
                    {
                        eprintln!(
                            "con app non-arrow debug span={}:{} source_head={:?} source_arg={:?} head={} head_kind={}",
                            span.file,
                            span.first.line,
                            c1.node,
                            c2.node,
                            crate::elaborated::type_display::format_constructor(&c1e),
                            crate::elaborated::type_display::format_kind(&k1),
                        );
                    }
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
            let field_kind = ku.clone();
            let krow = Located::new(elab::Kind::Record(Box::new(ku)), span.clone());
            let result = Located::new(
                elab::Constructor::Record(Box::new(field_kind), fields),
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

/// Resolve a constructor variable used in type (`con`) position: unqualified `t`, qualified `M.t`,
/// punned field labels (`Body`, …), the anonymous metavariable `_`, or a type-class head (`show`, …).
///
/// Type-class names in [`Env`] store their parameter kind in [`Env::named_c`]; this routine supplies the
/// classifier kind `parameter -> Type` via [`kind_for_class_constructor_head`] so saturated uses elaborate
/// like ordinary constructor application.
///
/// # Arguments
///
/// * `elaboration_context` — Collects [`DiagnosticId::ElabUnboundTypeConstructor`] when resolution fails.
/// * `elaboration_environment` — Kind, constructor, and structure tables built from earlier declarations.
/// * `ms` — Module path prefix before `x` (empty = unqualified); non-empty values delegate to [`resolve_module_path`].
/// * `x` — Final identifier (type name, label, `_`, or class head).
/// * `span` — Source span attached to synthesized AST and diagnostics.
///
/// # Returns
///
/// Pair of elaborated constructor AST and its kind, after [`elab_con_head`] when the head is a type class.
///
/// # Errors
///
/// Emits [`DiagnosticId::ElabUnboundTypeConstructor`] for unbound lowercase names that are not `_` and not labels.
/// Qualified lookup failures are already reported inside [`resolve_module_path`].
fn elab_con_var(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    ms: &[String],
    x: &str,
    span: &Span,
) -> (elab::LocatedConstructor, elab::LocatedKind) {
    // Unqualified occurrences use only `x` and the flat constructor namespace.
    if ms.is_empty() {
        match elaboration_environment.lookup_c(x) {
            VarLookup::Rel(de_bruijn_index, bound_kind) => {
                let relative_constructor =
                    Located::new(elab::Constructor::Rel(de_bruijn_index), span.clone());
                let (headed_constructor, headed_kind) =
                    elab_con_head(relative_constructor, bound_kind);
                if std::env::var("URWEB_DEBUG_MAPU_CON").ok().as_deref() == Some("1") && x == "mapU"
                {
                    eprintln!(
                        "mapu con var rel span={}:{} head={} kind={}",
                        span.file,
                        span.first.line,
                        crate::elaborated::type_display::format_constructor(&headed_constructor),
                        crate::elaborated::type_display::format_kind(&headed_kind),
                    );
                }
                return (headed_constructor, headed_kind);
            }
            VarLookup::Named(named_constructor_id, stored_kind) => {
                let named_head =
                    Located::new(elab::Constructor::Named(named_constructor_id), span.clone());
                let kind_for_elab_head = if elaboration_environment.is_class(&named_head) {
                    kind_for_class_constructor_head(span, &stored_kind)
                } else {
                    stored_kind.clone()
                };
                let (headed_constructor, headed_kind) =
                    elab_con_head(named_head, kind_for_elab_head);
                if std::env::var("URWEB_DEBUG_MAPU_CON").ok().as_deref() == Some("1") && x == "mapU"
                {
                    eprintln!(
                        "mapu con var named id={} span={}:{} stored_kind={} head={} kind={}",
                        named_constructor_id,
                        span.file,
                        span.first.line,
                        crate::elaborated::type_display::format_kind(&stored_kind),
                        crate::elaborated::type_display::format_constructor(&headed_constructor),
                        crate::elaborated::type_display::format_kind(&headed_kind),
                    );
                }
                return (headed_constructor, headed_kind);
            }
            VarLookup::NotBound => {
                // Parser sometimes leaves anonymous holes as `Var("_")` instead of [`source::Con::Wild`].
                if x == "_" {
                    let metavariable_kind = Located::new(elab::Kind::Type, span.clone());
                    let fresh_hole_constructor = fresh_cunif(
                        elaboration_environment,
                        span.clone(),
                        metavariable_kind.clone(),
                        "_",
                    );
                    return (fresh_hole_constructor, metavariable_kind);
                }
                // Uppercase identifiers that are not constructors behave as row **labels** (kind `Name`).
                let first_char_uppercase = x
                    .chars()
                    .next()
                    .map(|ch| ch.is_uppercase())
                    .unwrap_or(false);
                if first_char_uppercase {
                    let name_label_kind = Located::new(elab::Kind::Name, span.clone());
                    let name_literal_constructor =
                        Located::new(elab::Constructor::Name(x.to_string()), span.clone());
                    return (name_literal_constructor, name_label_kind);
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

    // Qualified paths `M1...Mn.x`: resolve the module path, then read `x` from the final signature.
    let (structure_root_id, signature_items) =
        match resolve_module_path(elaboration_context, elaboration_environment, ms, span) {
            Some(resolved) => resolved,
            None => {
                return (
                    elaborated_constructor_error_at_span(span.clone()),
                    elaborated_kind_error_at_span(span.clone()),
                );
            }
        };

    if let Some(signature_item) = sgi_find_con(&signature_items, x) {
        match signature_item {
            elab::SignatureItem::Constructor(_, _type_id, item_kind, _)
            | elab::SignatureItem::ConAbs(_, _type_id, item_kind) => {
                let module_projection = Located::new(
                    elab::Constructor::ModProj(structure_root_id, ms[1..].to_vec(), x.to_string()),
                    span.clone(),
                );
                let (headed_constructor, headed_kind) =
                    elab_con_head(module_projection, item_kind.clone());
                return (headed_constructor, headed_kind);
            }
            elab::SignatureItem::ClassAbs(_, _class_id, item_kind)
            | elab::SignatureItem::Class(_, _class_id, item_kind, _) => {
                let module_projection = Located::new(
                    elab::Constructor::ModProj(structure_root_id, ms[1..].to_vec(), x.to_string()),
                    span.clone(),
                );
                let classifier_kind = kind_for_class_constructor_head(span, item_kind);
                let (headed_constructor, headed_kind) =
                    elab_con_head(module_projection, classifier_kind);
                return (headed_constructor, headed_kind);
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

/// Compute the kind of an already-elaborated constructor in `elaboration_environment`.
///
/// Handles lookups (`Rel`, `Named`, `ModProj`), eliminators (`App`, `KApp`, tuple `Proj`), binders
/// (`Abs`, `KAbs`, [`elab::Constructor::TCFun`]), row shapes (`Record`, `Concat`, `Map`), and metavariables.
///
/// # Arguments
///
/// * `elaboration_context` — Records [`DiagnosticId::ElabUnboundRelConstructor`], [`DiagnosticId::ElabUnboundNamedConstructor`],
///   [`DiagnosticId::ElabApplicationNonArrowKind`], [`DiagnosticId::ElabKAppNonKFun`], and related failures.
/// * `elaboration_environment` — Environment whose binding stacks determine meaning of de Bruijn indices.
/// * `c` — Constructor whose kind is requested.
///
/// # Returns
///
/// The inferred [`elab::LocatedKind`]; unknown module projections receive a fresh kind metavariable from [`fresh_kunif`].
///
/// # Errors
///
/// See variants above; each arm returns [`elaborated_kind_error_at_span`] after enqueueing a diagnostic when checks fail.
pub fn kindof(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    c: &elab::LocatedConstructor,
) -> elab::LocatedKind {
    let span = c.span.clone();
    match &c.node {
        // Surface type syntax (`_ -> _`, records, disjoint constraints, `K --> _` bodies) is always classified as `Type` after elaboration.
        elab::Constructor::TFun(_, _)
        | elab::Constructor::TRecord(_)
        | elab::Constructor::TDisjoint(_, _, _)
        | elab::Constructor::TKFun(_, _) => Located::new(elab::Kind::Type, span),
        // Implicit/explicit type-level binders [`TCFun`]: mirror [`elab_con`]'s `push_c_rel` naming so `rename_c` matches elaboration.
        elab::Constructor::TCFun(_explicitness, binder_name, bound_kind, body) => {
            let environment_with_binder = elaboration_environment
                .clone()
                .push_c_rel(binder_name.clone(), *bound_kind.clone());
            let _body_kind_must_be_type =
                kindof(elaboration_context, &environment_with_binder, body);
            Located::new(elab::Kind::Type, span)
        }
        elab::Constructor::Rel(de_bruijn_index) => {
            match elaboration_environment.lookup_c_rel(*de_bruijn_index) {
                Ok((_ignored_name, bound_kind)) => bound_kind.clone(),
                Err(_) => {
                    elaboration_context.error(
                        span.clone(),
                        DiagnosticPayload::new(
                            DiagnosticId::ElabUnboundRelConstructor,
                            vec![de_bruijn_index.to_string()],
                        ),
                    );
                    elaborated_kind_error_at_span(span)
                }
            }
        }
        elab::Constructor::Named(named_constructor_id) => {
            match elaboration_environment.lookup_c_named(*named_constructor_id) {
                Ok((_name, stored_kind, _optional_definition)) => {
                    let synthetic_head = Located::new(
                        elab::Constructor::Named(*named_constructor_id),
                        span.clone(),
                    );
                    if elaboration_environment.is_class(&synthetic_head) {
                        kind_for_class_constructor_head(&span, stored_kind)
                    } else {
                        stored_kind.clone()
                    }
                }
                Err(_) => {
                    elaboration_context.error(
                        span.clone(),
                        DiagnosticPayload::new(
                            DiagnosticId::ElabUnboundNamedConstructor,
                            vec![named_constructor_id.to_string()],
                        ),
                    );
                    elaborated_kind_error_at_span(span)
                }
            }
        }
        elab::Constructor::ModProj(structure_id, _module_path_tail, exported_name) => {
            if let Ok((_structure_name, exported_signature)) =
                elaboration_environment.lookup_str_named(*structure_id)
            {
                let flattened_items =
                    get_sgn_const_items(elaboration_environment, exported_signature);
                if let Some(signature_item) = sgi_find_con(&flattened_items, exported_name) {
                    match signature_item {
                        elab::SignatureItem::ConAbs(_, _, item_kind)
                        | elab::SignatureItem::Constructor(_, _, item_kind, _) => {
                            return item_kind.clone();
                        }
                        elab::SignatureItem::ClassAbs(_, _, item_kind)
                        | elab::SignatureItem::Class(_, _, item_kind, _) => {
                            return kind_for_class_constructor_head(&span, item_kind);
                        }
                        _ => {}
                    }
                }
            }
            fresh_kunif(span, exported_name)
        }
        elab::Constructor::App(function_constructor, _argument_constructor) => {
            let function_kind = kindof(
                elaboration_context,
                elaboration_environment,
                function_constructor,
            );
            let normalized_function_kind = hnorm_kind(function_kind);
            match normalized_function_kind.node {
                elab::Kind::Arrow(_domain, codomain_kind) => *codomain_kind,
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
        elab::Constructor::Abs(binder_name, domain_kind, body) => {
            let environment_with_binder = elaboration_environment
                .clone()
                .push_c_rel(binder_name.clone(), *domain_kind.clone());
            let body_kind = kindof(elaboration_context, &environment_with_binder, body);
            Located::new(
                elab::Kind::Arrow(domain_kind.clone(), Box::new(body_kind)),
                span,
            )
        }
        elab::Constructor::KAbs(kind_binder_name, body) => {
            let environment_with_kind_binder = elaboration_environment
                .clone()
                .push_k_rel(kind_binder_name.clone());
            let body_kind = kindof(elaboration_context, &environment_with_kind_binder, body);
            Located::new(
                elab::Kind::Fun(kind_binder_name.clone(), Box::new(body_kind)),
                span,
            )
        }
        elab::Constructor::KApp(function_constructor, argument_kind) => {
            let function_kind = kindof(
                elaboration_context,
                elaboration_environment,
                function_constructor,
            );
            let normalized_function_kind = hnorm_kind(function_kind);
            match normalized_function_kind.node {
                elab::Kind::Fun(_binder, body_kind) => {
                    sub_kind_in_kind(0, argument_kind, *body_kind)
                }
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
        elab::Constructor::Record(row_kind, _fields) => {
            Located::new(elab::Kind::Record(row_kind.clone()), span)
        }
        elab::Constructor::Concat(left_row, _right_row) => {
            kindof(elaboration_context, elaboration_environment, left_row)
        }
        elab::Constructor::Map(row_element_kind_left, row_element_kind_right) => {
            let arrow_between_elements = Located::new(
                elab::Kind::Arrow(
                    row_element_kind_left.clone(),
                    row_element_kind_right.clone(),
                ),
                span.clone(),
            );
            let row_kind_left = Located::new(
                elab::Kind::Record(row_element_kind_left.clone()),
                span.clone(),
            );
            let row_kind_right = Located::new(
                elab::Kind::Record(row_element_kind_right.clone()),
                span.clone(),
            );
            Located::new(
                elab::Kind::Arrow(
                    Box::new(arrow_between_elements),
                    Box::new(Located::new(
                        elab::Kind::Arrow(Box::new(row_kind_left), Box::new(row_kind_right)),
                        span.clone(),
                    )),
                ),
                span.clone(),
            )
        }
        elab::Constructor::Unit => Located::new(elab::Kind::Unit, span),
        elab::Constructor::Tuple(components) => {
            let component_kinds: Vec<_> = components
                .iter()
                .map(|component| kindof(elaboration_context, elaboration_environment, component))
                .collect();
            Located::new(elab::Kind::Tuple(component_kinds), span)
        }
        elab::Constructor::Proj(tuple_constructor, one_based_index) => {
            let tuple_kind = kindof(
                elaboration_context,
                elaboration_environment,
                tuple_constructor,
            );
            let normalized_tuple_kind = hnorm_kind(tuple_kind);
            match normalized_tuple_kind.node {
                elab::Kind::Tuple(component_kinds) => {
                    let zero_based_index = one_based_index.checked_sub(1).unwrap_or(0);
                    component_kinds
                        .get(zero_based_index)
                        .cloned()
                        .unwrap_or_else(|| elaborated_kind_error_at_span(span))
                }
                _ => elaborated_kind_error_at_span(span),
            }
        }
        elab::Constructor::Error => elaborated_kind_error_at_span(span),
        elab::Constructor::Unif(_nesting, _span_ref, recorded_kind, _debug_name, _cell) => {
            *recorded_kind.clone()
        }
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

const SIGNATURE_REALIZATION_MAX_STEPS: usize = 256;

fn actual_signature_constructor_replacement(
    actual_item: &elab::SignatureItem,
    span: &Span,
) -> Option<elab::LocatedConstructor> {
    match actual_item {
        elab::SignatureItem::ConAbs(_, id, _)
        | elab::SignatureItem::Constructor(_, id, _, _)
        | elab::SignatureItem::ClassAbs(_, id, _)
        | elab::SignatureItem::Class(_, id, _, _) => {
            Some(Located::new(elab::Constructor::Named(*id), span.clone()))
        }
        _ => None,
    }
}

fn build_signature_realization_map(
    actual_items: &[elab::LocatedSignatureItem],
    expected_items: &[elab::LocatedSignatureItem],
    span: &Span,
) -> HashMap<usize, elab::LocatedConstructor> {
    let mut realization_map = HashMap::new();
    for expected_item in expected_items {
        let (expected_name, expected_id) = match &expected_item.node {
            elab::SignatureItem::ConAbs(name, id, _)
            | elab::SignatureItem::Constructor(name, id, _, _)
            | elab::SignatureItem::ClassAbs(name, id, _)
            | elab::SignatureItem::Class(name, id, _, _) => (name, *id),
            _ => continue,
        };
        let Some(actual_item) = sgi_find_con(actual_items, expected_name) else {
            continue;
        };
        let Some(replacement) = actual_signature_constructor_replacement(actual_item, span) else {
            continue;
        };
        realization_map.insert(expected_id, replacement);
    }
    realization_map
}

fn realize_signature_constructor_named_ids_inner(
    constructor: &elab::LocatedConstructor,
    realization_map: &HashMap<usize, elab::LocatedConstructor>,
    seen_named_ids: &mut HashSet<usize>,
    constructor_binder_depth: usize,
    kind_binder_depth: usize,
    remaining_steps: usize,
) -> elab::LocatedConstructor {
    if remaining_steps == 0 {
        return constructor.clone();
    }
    let span = constructor.span.clone();
    let next_steps = remaining_steps - 1;
    match &constructor.node {
        elab::Constructor::Named(id) => match realization_map.get(id) {
            Some(replacement) if seen_named_ids.insert(*id) => {
                let mut lifted_replacement =
                    mlift_con_in_con(constructor_binder_depth, replacement.clone());
                for _ in 0usize..kind_binder_depth {
                    lifted_replacement = lift_kind_in_con(lifted_replacement);
                }
                let realized = realize_signature_constructor_named_ids_inner(
                    &lifted_replacement,
                    realization_map,
                    seen_named_ids,
                    constructor_binder_depth,
                    kind_binder_depth,
                    next_steps,
                );
                seen_named_ids.remove(id);
                realized
            }
            _ => constructor.clone(),
        },
        elab::Constructor::TFun(domain, codomain) => Located::new(
            elab::Constructor::TFun(
                Box::new(realize_signature_constructor_named_ids_inner(
                    domain,
                    realization_map,
                    seen_named_ids,
                    constructor_binder_depth,
                    kind_binder_depth,
                    next_steps,
                )),
                Box::new(realize_signature_constructor_named_ids_inner(
                    codomain,
                    realization_map,
                    seen_named_ids,
                    constructor_binder_depth,
                    kind_binder_depth,
                    next_steps,
                )),
            ),
            span,
        ),
        elab::Constructor::TCFun(explicitness, name, kind, body) => Located::new(
            elab::Constructor::TCFun(
                *explicitness,
                name.clone(),
                kind.clone(),
                Box::new(realize_signature_constructor_named_ids_inner(
                    body,
                    realization_map,
                    seen_named_ids,
                    constructor_binder_depth + 1usize,
                    kind_binder_depth,
                    next_steps,
                )),
            ),
            span,
        ),
        elab::Constructor::TRecord(row) => Located::new(
            elab::Constructor::TRecord(Box::new(realize_signature_constructor_named_ids_inner(
                row,
                realization_map,
                seen_named_ids,
                constructor_binder_depth,
                kind_binder_depth,
                next_steps,
            ))),
            span,
        ),
        elab::Constructor::TDisjoint(left_row, right_row, body) => Located::new(
            elab::Constructor::TDisjoint(
                Box::new(realize_signature_constructor_named_ids_inner(
                    left_row,
                    realization_map,
                    seen_named_ids,
                    constructor_binder_depth,
                    kind_binder_depth,
                    next_steps,
                )),
                Box::new(realize_signature_constructor_named_ids_inner(
                    right_row,
                    realization_map,
                    seen_named_ids,
                    constructor_binder_depth,
                    kind_binder_depth,
                    next_steps,
                )),
                Box::new(realize_signature_constructor_named_ids_inner(
                    body,
                    realization_map,
                    seen_named_ids,
                    constructor_binder_depth,
                    kind_binder_depth,
                    next_steps,
                )),
            ),
            span,
        ),
        elab::Constructor::App(function_constructor, argument_constructor) => Located::new(
            elab::Constructor::App(
                Box::new(realize_signature_constructor_named_ids_inner(
                    function_constructor,
                    realization_map,
                    seen_named_ids,
                    constructor_binder_depth,
                    kind_binder_depth,
                    next_steps,
                )),
                Box::new(realize_signature_constructor_named_ids_inner(
                    argument_constructor,
                    realization_map,
                    seen_named_ids,
                    constructor_binder_depth,
                    kind_binder_depth,
                    next_steps,
                )),
            ),
            span,
        ),
        elab::Constructor::Abs(name, kind, body) => Located::new(
            elab::Constructor::Abs(
                name.clone(),
                kind.clone(),
                Box::new(realize_signature_constructor_named_ids_inner(
                    body,
                    realization_map,
                    seen_named_ids,
                    constructor_binder_depth + 1usize,
                    kind_binder_depth,
                    next_steps,
                )),
            ),
            span,
        ),
        elab::Constructor::KAbs(name, body) => Located::new(
            elab::Constructor::KAbs(
                name.clone(),
                Box::new(realize_signature_constructor_named_ids_inner(
                    body,
                    realization_map,
                    seen_named_ids,
                    constructor_binder_depth,
                    kind_binder_depth + 1usize,
                    next_steps,
                )),
            ),
            span,
        ),
        elab::Constructor::KApp(function_constructor, kind_argument) => Located::new(
            elab::Constructor::KApp(
                Box::new(realize_signature_constructor_named_ids_inner(
                    function_constructor,
                    realization_map,
                    seen_named_ids,
                    constructor_binder_depth,
                    kind_binder_depth,
                    next_steps,
                )),
                kind_argument.clone(),
            ),
            span,
        ),
        elab::Constructor::TKFun(name, body) => Located::new(
            elab::Constructor::TKFun(
                name.clone(),
                Box::new(realize_signature_constructor_named_ids_inner(
                    body,
                    realization_map,
                    seen_named_ids,
                    constructor_binder_depth,
                    kind_binder_depth,
                    next_steps,
                )),
            ),
            span,
        ),
        elab::Constructor::Record(row_kind, fields) => {
            let realized_fields = fields
                .iter()
                .map(|(field_name, field_type)| {
                    (
                        realize_signature_constructor_named_ids_inner(
                            field_name,
                            realization_map,
                            seen_named_ids,
                            constructor_binder_depth,
                            kind_binder_depth,
                            next_steps,
                        ),
                        realize_signature_constructor_named_ids_inner(
                            field_type,
                            realization_map,
                            seen_named_ids,
                            constructor_binder_depth,
                            kind_binder_depth,
                            next_steps,
                        ),
                    )
                })
                .collect();
            Located::new(
                elab::Constructor::Record(row_kind.clone(), realized_fields),
                span,
            )
        }
        elab::Constructor::Concat(left_row, right_row) => Located::new(
            elab::Constructor::Concat(
                Box::new(realize_signature_constructor_named_ids_inner(
                    left_row,
                    realization_map,
                    seen_named_ids,
                    constructor_binder_depth,
                    kind_binder_depth,
                    next_steps,
                )),
                Box::new(realize_signature_constructor_named_ids_inner(
                    right_row,
                    realization_map,
                    seen_named_ids,
                    constructor_binder_depth,
                    kind_binder_depth,
                    next_steps,
                )),
            ),
            span,
        ),
        elab::Constructor::Tuple(elements) => Located::new(
            elab::Constructor::Tuple(
                elements
                    .iter()
                    .map(|element| {
                        realize_signature_constructor_named_ids_inner(
                            element,
                            realization_map,
                            seen_named_ids,
                            constructor_binder_depth,
                            kind_binder_depth,
                            next_steps,
                        )
                    })
                    .collect(),
            ),
            span,
        ),
        elab::Constructor::Proj(base, index) => Located::new(
            elab::Constructor::Proj(
                Box::new(realize_signature_constructor_named_ids_inner(
                    base,
                    realization_map,
                    seen_named_ids,
                    constructor_binder_depth,
                    kind_binder_depth,
                    next_steps,
                )),
                *index,
            ),
            span,
        ),
        _ => constructor.clone(),
    }
}

fn realize_signature_constructor_named_ids(
    constructor: &elab::LocatedConstructor,
    realization_map: &HashMap<usize, elab::LocatedConstructor>,
) -> elab::LocatedConstructor {
    let mut seen_named_ids = HashSet::new();
    realize_signature_constructor_named_ids_inner(
        constructor,
        realization_map,
        &mut seen_named_ids,
        0usize,
        0usize,
        SIGNATURE_REALIZATION_MAX_STEPS,
    )
}

fn realize_signature_datatype_decl_named_ids(
    datatype_decl: &elab::DatatypeDecl,
    realization_map: &HashMap<usize, elab::LocatedConstructor>,
) -> elab::DatatypeDecl {
    let realized_constructors = datatype_decl
        .constrs
        .iter()
        .map(|(constructor_name, constructor_id, constructor_type)| {
            let realized_constructor_type = constructor_type.as_ref().map(|constructor| {
                realize_signature_constructor_named_ids(constructor, realization_map)
            });
            (
                constructor_name.clone(),
                *constructor_id,
                realized_constructor_type,
            )
        })
        .collect();
    elab::DatatypeDecl {
        name: datatype_decl.name.clone(),
        id: datatype_decl.id,
        params: datatype_decl.params.clone(),
        constrs: realized_constructors,
    }
}

fn realize_signature_item_named_ids(
    signature_item: &elab::LocatedSignatureItem,
    realization_map: &HashMap<usize, elab::LocatedConstructor>,
) -> elab::LocatedSignatureItem {
    let span = signature_item.span.clone();
    let realized_item = match &signature_item.node {
        elab::SignatureItem::ConAbs(name, id, kind) => {
            elab::SignatureItem::ConAbs(name.clone(), *id, kind.clone())
        }
        elab::SignatureItem::Constructor(name, id, kind, constructor) => {
            elab::SignatureItem::Constructor(
                name.clone(),
                *id,
                kind.clone(),
                realize_signature_constructor_named_ids(constructor, realization_map),
            )
        }
        elab::SignatureItem::Datatype(datatypes) => elab::SignatureItem::Datatype(
            datatypes
                .iter()
                .map(|datatype| {
                    realize_signature_datatype_decl_named_ids(datatype, realization_map)
                })
                .collect(),
        ),
        elab::SignatureItem::DatatypeImp {
            name,
            id,
            params,
            orig_mod,
            orig_path,
            orig_name,
            orig_constrs_path,
            constrs,
        } => {
            let realized_constructors = constrs
                .iter()
                .map(|(constructor_name, constructor_id, constructor_type)| {
                    let realized_constructor_type = constructor_type.as_ref().map(|constructor| {
                        realize_signature_constructor_named_ids(constructor, realization_map)
                    });
                    (
                        constructor_name.clone(),
                        *constructor_id,
                        realized_constructor_type,
                    )
                })
                .collect();
            elab::SignatureItem::DatatypeImp {
                name: name.clone(),
                id: *id,
                params: params.clone(),
                orig_mod: *orig_mod,
                orig_path: orig_path.clone(),
                orig_name: orig_name.clone(),
                orig_constrs_path: orig_constrs_path.clone(),
                constrs: realized_constructors,
            }
        }
        elab::SignatureItem::Val(name, id, constructor) => elab::SignatureItem::Val(
            name.clone(),
            *id,
            realize_signature_constructor_named_ids(constructor, realization_map),
        ),
        elab::SignatureItem::Structure(import_mode, name, id, signature) => {
            elab::SignatureItem::Structure(
                *import_mode,
                name.clone(),
                *id,
                realize_signature_named_ids(signature, realization_map),
            )
        }
        elab::SignatureItem::Signature(name, id, signature) => elab::SignatureItem::Signature(
            name.clone(),
            *id,
            realize_signature_named_ids(signature, realization_map),
        ),
        elab::SignatureItem::Constraint(left_constructor, right_constructor) => {
            elab::SignatureItem::Constraint(
                realize_signature_constructor_named_ids(left_constructor, realization_map),
                realize_signature_constructor_named_ids(right_constructor, realization_map),
            )
        }
        elab::SignatureItem::ClassAbs(name, id, kind) => {
            elab::SignatureItem::ClassAbs(name.clone(), *id, kind.clone())
        }
        elab::SignatureItem::Class(name, id, kind, constructor) => elab::SignatureItem::Class(
            name.clone(),
            *id,
            kind.clone(),
            realize_signature_constructor_named_ids(constructor, realization_map),
        ),
    };
    Located::new(realized_item, span)
}

fn realize_signature_named_ids(
    signature: &elab::LocatedSignature,
    realization_map: &HashMap<usize, elab::LocatedConstructor>,
) -> elab::LocatedSignature {
    let span = signature.span.clone();
    let realized_signature = match &signature.node {
        elab::Signature::Const(signature_items) => elab::Signature::Const(
            signature_items
                .iter()
                .map(|signature_item| {
                    realize_signature_item_named_ids(signature_item, realization_map)
                })
                .collect(),
        ),
        elab::Signature::Var(id) => elab::Signature::Var(*id),
        elab::Signature::Fun(name, id, domain, range) => elab::Signature::Fun(
            name.clone(),
            *id,
            Box::new(realize_signature_named_ids(domain, realization_map)),
            Box::new(realize_signature_named_ids(range, realization_map)),
        ),
        elab::Signature::Where(signature, modules, name, constructor) => elab::Signature::Where(
            Box::new(realize_signature_named_ids(signature, realization_map)),
            modules.clone(),
            name.clone(),
            realize_signature_constructor_named_ids(constructor, realization_map),
        ),
        elab::Signature::Proj(id, modules, name) => {
            elab::Signature::Proj(*id, modules.clone(), name.clone())
        }
        elab::Signature::Error => elab::Signature::Error,
    };
    Located::new(realized_signature, span)
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
    /// Constructor references a local variable that is out of scope for the unification variable
    /// (SML `CantSquish` → `TooDeep` / `CScope` errors).
    ConstructorTooDeepForUnif,
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
        FailedToUnifyConstructors::ConstructorTooDeepForUnif => {
            // SML TooDeep / CScope: the constructor references a variable that is not in scope
            // for the unification variable being instantiated.
            "constructor references a variable out of scope for the unification variable (TooDeep)"
                .to_string()
        }
    }
}

fn debug_constructor_head_name(
    elaboration_environment: &Env,
    constructor: &elab::LocatedConstructor,
) -> String {
    let normalized_constructor =
        hnorm_con_expression_head(elaboration_environment, constructor.clone());
    let normalized_head = constructor_head_after_apps(&normalized_constructor);
    let normalized_head_text = crate::elaborated::type_display::format_constructor(normalized_head);
    match &normalized_head.node {
        elab::Constructor::Named(id) => match elaboration_environment.lookup_c_named(*id) {
            Ok((name, kind, definition)) => format!(
                "head={} Named(#{id}, name={name}, kind={}, def={})",
                normalized_head_text,
                crate::elaborated::type_display::format_kind(kind),
                definition
                    .as_ref()
                    .map(crate::elaborated::type_display::format_constructor)
                    .unwrap_or_else(|| "<abstract>".to_string())
            ),
            Err(error) => format!(
                "head={} Named(#{id}, lookup_error={error:?})",
                normalized_head_text
            ),
        },
        elab::Constructor::ModProj(module_id, path, name) => {
            format!(
                "head={} ModProj(mod={module_id}, path={path:?}, name={name})",
                normalized_head_text
            )
        }
        elab::Constructor::Rel(index) => match elaboration_environment.lookup_c_rel(*index) {
            Ok((name, kind)) => format!(
                "head={} Rel('{index}, name={name}, kind={})",
                normalized_head_text,
                crate::elaborated::type_display::format_kind(kind)
            ),
            Err(_) => format!("head={} Rel('{index}, missing)", normalized_head_text),
        },
        _ => format!(
            "head={} normalized={}",
            normalized_head_text,
            crate::elaborated::type_display::format_constructor(&normalized_constructor)
        ),
    }
}

fn collect_named_constructor_ids(
    constructor: &elab::LocatedConstructor,
    ids: &mut std::collections::BTreeSet<usize>,
) {
    match &constructor.node {
        elab::Constructor::Named(id) => {
            ids.insert(*id);
        }
        elab::Constructor::TFun(domain, range)
        | elab::Constructor::App(domain, range)
        | elab::Constructor::Concat(domain, range) => {
            collect_named_constructor_ids(domain, ids);
            collect_named_constructor_ids(range, ids);
        }
        elab::Constructor::TCFun(_, _, _, body)
        | elab::Constructor::TRecord(body)
        | elab::Constructor::Abs(_, _, body)
        | elab::Constructor::KAbs(_, body)
        | elab::Constructor::TKFun(_, body)
        | elab::Constructor::Proj(body, _) => {
            collect_named_constructor_ids(body, ids);
        }
        elab::Constructor::TDisjoint(left, right, body) => {
            collect_named_constructor_ids(left, ids);
            collect_named_constructor_ids(right, ids);
            collect_named_constructor_ids(body, ids);
        }
        elab::Constructor::KApp(body, _) => {
            collect_named_constructor_ids(body, ids);
        }
        elab::Constructor::Record(_, fields) => {
            for (field_name, field_type) in fields {
                collect_named_constructor_ids(field_name, ids);
                collect_named_constructor_ids(field_type, ids);
            }
        }
        elab::Constructor::Tuple(items) => {
            for item in items {
                collect_named_constructor_ids(item, ids);
            }
        }
        elab::Constructor::Rel(_)
        | elab::Constructor::ModProj(_, _, _)
        | elab::Constructor::Name(_)
        | elab::Constructor::Map(_, _)
        | elab::Constructor::Unit
        | elab::Constructor::Error
        | elab::Constructor::Unif(_, _, _, _, _) => {}
    }
}

fn debug_named_ids_in_constructor(
    elaboration_environment: &Env,
    constructor: &elab::LocatedConstructor,
) -> String {
    let mut ids: std::collections::BTreeSet<usize> = std::collections::BTreeSet::new();
    collect_named_constructor_ids(constructor, &mut ids);
    ids.into_iter()
        .map(|id| match elaboration_environment.lookup_c_named(id) {
            Ok((name, kind, definition)) => format!(
                "#{id}={name}:{}={}",
                crate::elaborated::type_display::format_kind(kind),
                definition
                    .as_ref()
                    .map(crate::elaborated::type_display::format_constructor)
                    .unwrap_or_else(|| "<abstract>".to_string())
            ),
            Err(error) => format!("#{id}=<{error:?}>"),
        })
        .collect::<Vec<_>>()
        .join(", ")
}

/// Record summary for row unification.
#[derive(Debug, Clone)]
struct RecordSummary {
    /// Field name/value constructor pairs.  Mirrors SML `record_summary.fields`:
    /// names are `hnorm_con`'d but may be any constructor (Name literal, Rel, Unif, etc.).
    /// [`unifySummaries`] (SML) matches them via `consEq`/`consNeq`, not by string equality.
    fields: Vec<(elab::LocatedConstructor, elab::LocatedConstructor)>,
    /// Unification variable tails stored as their original `Constructor::Unif(...)` located nodes.
    /// Storing the full located constructor (rather than just `(CUnifRef, usize)`) lets
    /// `unsummarize_summary` include them verbatim in a solution row via `Constructor::Concat`.
    unifs: Vec<elab::LocatedConstructor>,
    /// Other unknown row pieces (non-Record, non-Concat, non-Unif constructors such as `map f r`).
    others: Vec<elab::LocatedConstructor>,
}

/// Maximum recursion depth for [`record_summary`] (`Concat`, named alias unfold) before returning an error stub.
const RECORD_SUMMARY_MAX_DEPTH: usize = 8192;

/// Head-normalise a constructor and decompose a row constructor into a RecordSummary.
/// Named type aliases are unfolded via `elaboration_environment` so their fields are visible to the row unifier.
fn record_summary(elaboration_environment: &Env, c: elab::LocatedConstructor) -> RecordSummary {
    record_summary_inner(elaboration_environment, c, 0)
}

/// Extract tuple components from a closed numeric-field record row (`{1: t1, 2: t2, ...}`).
///
/// Returns `None` unless `row_constructor` reduces to a closed record with exactly the positive
/// integer labels `1..=n` and no open tail, matching the tuple sugar used in source expressions
/// and patterns.
fn closed_numeric_record_components(
    elaboration_environment: &Env,
    row_constructor: &elab::LocatedConstructor,
) -> Option<Vec<elab::LocatedConstructor>> {
    let row_summary = record_summary(elaboration_environment, row_constructor.clone());
    match (row_summary.unifs.is_empty(), row_summary.others.is_empty()) {
        (true, true) => {}
        _ => return None,
    }
    if row_summary.fields.is_empty() {
        return None;
    }

    let mut ordered_components: Vec<Option<elab::LocatedConstructor>> =
        vec![None; row_summary.fields.len()];
    for (field_name, field_type) in row_summary.fields {
        let normalized_name = hnorm_con(field_name);
        let tuple_index = match normalized_name.node {
            elab::Constructor::Name(field_label) => match field_label.parse::<usize>() {
                Ok(parsed_index) if parsed_index >= 1 => parsed_index,
                _ => return None,
            },
            _ => return None,
        };
        if tuple_index > ordered_components.len() {
            return None;
        }
        match ordered_components[tuple_index - 1].replace(field_type) {
            None => {}
            Some(_) => return None,
        }
    }

    let mut tuple_components: Vec<elab::LocatedConstructor> =
        Vec::with_capacity(ordered_components.len());
    for component in ordered_components {
        match component {
            Some(field_type) => tuple_components.push(field_type),
            None => return None,
        }
    }
    Some(tuple_components)
}

/// Unify a closed numeric-field record type with a tuple/product type component-wise.
fn unify_closed_numeric_record_with_tuple(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    diagnostic_span: &Span,
    left_normalized: &elab::LocatedConstructor,
    right_normalized: &elab::LocatedConstructor,
    record_row: &elab::LocatedConstructor,
    tuple_components: &[elab::LocatedConstructor],
    recursion_depth: usize,
) -> Result<(), Box<FailedToUnifyConstructors>> {
    let record_components =
        match closed_numeric_record_components(elaboration_environment, record_row) {
            Some(components) => components,
            None => {
                return Err(Box::new(
                    FailedToUnifyConstructors::IncompatibleConstructors(
                        left_normalized.clone(),
                        right_normalized.clone(),
                    ),
                ));
            }
        };
    if record_components.len() != tuple_components.len() {
        return Err(Box::new(
            FailedToUnifyConstructors::IncompatibleConstructors(
                left_normalized.clone(),
                right_normalized.clone(),
            ),
        ));
    }
    for (record_component, tuple_component) in record_components.iter().zip(tuple_components.iter())
    {
        unify_cons_inner(
            elaboration_context,
            elaboration_environment,
            diagnostic_span,
            record_component,
            tuple_component,
            recursion_depth + 1,
        )?;
    }
    Ok(())
}

fn record_summary_inner(
    elaboration_environment: &Env,
    c: elab::LocatedConstructor,
    depth: usize,
) -> RecordSummary {
    if depth >= RECORD_SUMMARY_MAX_DEPTH {
        return RecordSummary {
            fields: vec![],
            unifs: vec![],
            others: vec![elaborated_constructor_error_at_span(c.span.clone())],
        };
    }
    let cn = hnorm_con(c.clone());
    match cn.node {
        elab::Constructor::Record(_, ref xcs) => {
            // Mirrors SML `recordSummary` for CRecord: ALL fields go into `fields` as
            // `(hnorm_con name, hnorm_con value)` pairs regardless of whether the name
            // is a concrete Name literal, a Rel de Bruijn variable, or a Unif.
            // `unifySummaries` (SML) matches field names via `consEq`/`consNeq`, not by
            // string equality, so abstract names can be solved during field unification.
            let fields: Vec<(elab::LocatedConstructor, elab::LocatedConstructor)> = xcs
                .iter()
                .map(|(nc, vc)| (hnorm_con(nc.clone()), hnorm_con(vc.clone())))
                .collect();
            RecordSummary {
                fields,
                unifs: vec![],
                others: vec![],
            }
        }
        elab::Constructor::Concat(c1, c2) => {
            let mut s1 = record_summary_inner(elaboration_environment, *c1, depth + 1);
            let s2 = record_summary_inner(elaboration_environment, *c2, depth + 1);
            s1.fields.extend(s2.fields);
            s1.unifs.extend(s2.unifs);
            s1.others.extend(s2.others);
            s1
        }
        elab::Constructor::Unif(nl, _, _, _, _) => {
            // Mirrors SML `recordSummary`: only `nl = 0` (outermost-scope) unification
            // variables go into `unifs`; deeper unifs go into `others`.
            // This is critical because the one-unif solve patterns (SML pattern 1/2) only
            // fire for `nl = 0` Unifs, where squish is the identity.  `nl > 0` Unifs that
            // land in `others` are handled by the final-dispatch patterns which squish before
            // assigning.
            if nl == 0 {
                RecordSummary {
                    fields: vec![],
                    unifs: vec![cn],
                    others: vec![],
                }
            } else {
                RecordSummary {
                    fields: vec![],
                    unifs: vec![],
                    others: vec![cn],
                }
            }
        }
        elab::Constructor::Unit => RecordSummary {
            fields: vec![],
            unifs: vec![],
            others: vec![],
        },
        // Unfold Named type aliases (e.g. `body'`) so their fields become visible.
        elab::Constructor::Named(id) => {
            if let Ok((_, _, Some(def))) = elaboration_environment.lookup_c_named(id) {
                record_summary_inner(elaboration_environment, def.clone(), depth + 1)
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
    if std::env::var("URWEB_DEBUG_UNIFY_SHALLOW").ok().as_deref() == Some("1")
        && recursion_depth > 20usize
    {
        eprintln!(
            "unify shallow debug depth={} span={}:{} left={} [{}] right={} [{}]",
            recursion_depth,
            diagnostic_span.file,
            diagnostic_span.first.line,
            crate::elaborated::type_display::format_constructor(left_constructor),
            debug_constructor_head_name(elaboration_environment, left_constructor),
            crate::elaborated::type_display::format_constructor(right_constructor),
            debug_constructor_head_name(elaboration_environment, right_constructor),
        );
        panic!("debug shallow unify recursion");
    }
    if recursion_depth > 400 {
        if std::env::var("URWEB_DEBUG_UNIFY_RECURSION").ok().as_deref() == Some("1") {
            eprintln!(
                "unify recursion debug span={}:{} left={} [{}] right={} [{}]",
                diagnostic_span.file,
                diagnostic_span.first.line,
                crate::elaborated::type_display::format_constructor(left_constructor),
                debug_constructor_head_name(elaboration_environment, left_constructor),
                crate::elaborated::type_display::format_constructor(right_constructor),
                debug_constructor_head_name(elaboration_environment, right_constructor),
            );
        }
        return Err(Box::new(
            FailedToUnifyConstructors::UnificationRecursionLimitExceeded,
        ));
    }

    // Chase known unif vars first (expand named abbreviations like ML normCon)
    let left_normalized =
        deep_normalize_constructor(elaboration_environment, left_constructor.clone());
    let right_normalized =
        deep_normalize_constructor(elaboration_environment, right_constructor.clone());

    struct DebugPairGuard;
    impl Drop for DebugPairGuard {
        fn drop(&mut self) {
            DEBUG_UNIFY_PAIR_STACK.with(|stack| {
                let _ = stack.borrow_mut().pop();
            });
        }
    }

    let _debug_pair_guard = if std::env::var("URWEB_DEBUG_UNIFY_PAIR_CYCLE")
        .ok()
        .as_deref()
        == Some("1")
    {
        let left_key = crate::elaborated::type_display::format_constructor(&left_normalized);
        let right_key = crate::elaborated::type_display::format_constructor(&right_normalized);
        DEBUG_UNIFY_PAIR_STACK.with(|stack| {
            let existing_stack = stack.borrow();
            if existing_stack
                .iter()
                .any(|(existing_left, existing_right)| {
                    existing_left == &left_key && existing_right == &right_key
                })
            {
                eprintln!(
                    "unify pair cycle depth={} span={}:{} left={} right={}",
                    recursion_depth,
                    diagnostic_span.file,
                    diagnostic_span.first.line,
                    left_key,
                    right_key,
                );
                panic!("debug unify pair cycle");
            }
        });
        DEBUG_UNIFY_PAIR_STACK.with(|stack| {
            stack.borrow_mut().push((left_key, right_key));
        });
        Some(DebugPairGuard)
    } else {
        None
    };

    // Quick structural equality check
    if cons_eq_simple(&left_normalized, &right_normalized) {
        return Ok(());
    }
    let left_frozen = normalize_signature_constructor(&left_normalized);
    let right_frozen = normalize_signature_constructor(&right_normalized);
    if signature_constructors_eq(&left_frozen, &right_frozen) {
        return Ok(());
    }

    if constructor_has_unit_kind(
        elaboration_context,
        elaboration_environment,
        &left_normalized,
    ) && constructor_has_unit_kind(
        elaboration_context,
        elaboration_environment,
        &right_normalized,
    ) {
        return Ok(());
    }

    let left_is_folder_application =
        is_folder_constructor_application(elaboration_environment, &left_normalized);
    let right_is_folder_application =
        is_folder_constructor_application(elaboration_environment, &right_normalized);
    match (left_is_folder_application, right_is_folder_application) {
        (true, false) => {
            if std::env::var("URWEB_DEBUG_FOLDER_UNIFY").ok().as_deref() == Some("1") {
                let log_index = DEBUG_FOLDER_UNIFY_LOG_COUNT.fetch_add(1, Ordering::Relaxed);
                if log_index < 40usize {
                    eprintln!(
                        "folder unify left depth={} span={}:{} left={} right={}",
                        recursion_depth,
                        diagnostic_span.file,
                        diagnostic_span.first.line,
                        crate::elaborated::type_display::format_constructor(&left_normalized),
                        crate::elaborated::type_display::format_constructor(&right_normalized),
                    );
                }
            }
            let Some(expanded_left_folder) = expand_folder_constructor_application(
                elaboration_context,
                elaboration_environment,
                &left_normalized,
            ) else {
                return Err(Box::new(
                    FailedToUnifyConstructors::IncompatibleConstructors(
                        left_normalized,
                        right_normalized,
                    ),
                ));
            };
            return unify_cons_inner(
                elaboration_context,
                elaboration_environment,
                diagnostic_span,
                &expanded_left_folder,
                &right_normalized,
                recursion_depth + 1,
            );
        }
        (false, true) => {
            if std::env::var("URWEB_DEBUG_FOLDER_UNIFY").ok().as_deref() == Some("1") {
                let log_index = DEBUG_FOLDER_UNIFY_LOG_COUNT.fetch_add(1, Ordering::Relaxed);
                if log_index < 40usize {
                    eprintln!(
                        "folder unify right depth={} span={}:{} left={} right={}",
                        recursion_depth,
                        diagnostic_span.file,
                        diagnostic_span.first.line,
                        crate::elaborated::type_display::format_constructor(&left_normalized),
                        crate::elaborated::type_display::format_constructor(&right_normalized),
                    );
                }
            }
            let Some(expanded_right_folder) = expand_folder_constructor_application(
                elaboration_context,
                elaboration_environment,
                &right_normalized,
            ) else {
                return Err(Box::new(
                    FailedToUnifyConstructors::IncompatibleConstructors(
                        left_normalized,
                        right_normalized,
                    ),
                ));
            };
            return unify_cons_inner(
                elaboration_context,
                elaboration_environment,
                diagnostic_span,
                &left_normalized,
                &expanded_right_folder,
                recursion_depth + 1,
            );
        }
        _ => {}
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
        //
        // SML semantics: for nl=0 store the constructor directly; for nl>0 apply
        // `squish nl c` (the inverse of mliftConInCon nl) so that when hnorm_con later
        // applies `mlift(nl, inner)` the round-trip gives back the original constructor.
        // CantSquish (constructor references one of the nl extra binders) maps to TooDeep.
        (
            elab::Constructor::Unif(nl1, _, _k1, _, r1),
            elab::Constructor::Unif(_nl2, _, _k2, _, r2),
        ) => {
            if Arc::ptr_eq(r1, r2) {
                // Same cell: already unified, nothing to do.
                return Ok(());
            }
            // Occurs check: prevent circular types before storing.
            if occurs_cunif(r1, &right_normalized) {
                return Err(Box::new(FailedToUnifyConstructors::OccursCheckWouldCycle));
            }
            // Apply squish to adjust depth from current context to the Unif's creation context.
            let adjusted = squish_con(*nl1, right_normalized.clone()).map_err(|CantSquish| {
                Box::new(FailedToUnifyConstructors::ConstructorTooDeepForUnif)
            })?;
            *crate::compiler_diagnostics::lock_for_compile(
                r1.as_ref(),
                "elaboration unification cell",
            ) = elab::CUnif::Known(Box::new(adjusted));
            Ok(())
        }
        (elab::Constructor::Unif(nl, _, _k, _, r), _) => {
            // Occurs check: prevent circular types before storing.
            if occurs_cunif(r, &right_normalized) {
                return Err(Box::new(FailedToUnifyConstructors::OccursCheckWouldCycle));
            }
            // Apply squish to adjust depth from current context to the Unif's creation context.
            let adjusted = squish_con(*nl, right_normalized.clone()).map_err(|CantSquish| {
                if std::env::var("URWEB_DEBUG_SQUISH_FAIL").ok().as_deref() == Some("1") {
                    eprintln!(
                        "squish fail left-unif span={}:{} nl={} left={} right={} right_head={}",
                        diagnostic_span.file,
                        diagnostic_span.first.line,
                        nl,
                        crate::elaborated::type_display::format_constructor(&left_normalized),
                        crate::elaborated::type_display::format_constructor(&right_normalized),
                        debug_constructor_head_name(elaboration_environment, &right_normalized),
                    );
                }
                Box::new(FailedToUnifyConstructors::ConstructorTooDeepForUnif)
            })?;
            *crate::compiler_diagnostics::lock_for_compile(
                r.as_ref(),
                "elaboration unification cell",
            ) = elab::CUnif::Known(Box::new(adjusted));
            Ok(())
        }
        (_, elab::Constructor::Unif(nl, _, _k, _, r)) => {
            // Occurs check: prevent circular types before storing.
            if occurs_cunif(r, &left_normalized) {
                return Err(Box::new(FailedToUnifyConstructors::OccursCheckWouldCycle));
            }
            // Apply squish to adjust depth from current context to the Unif's creation context.
            let adjusted = squish_con(*nl, left_normalized.clone()).map_err(|CantSquish| {
                if std::env::var("URWEB_DEBUG_SQUISH_FAIL").ok().as_deref() == Some("1") {
                    eprintln!(
                        "squish fail right-unif span={}:{} nl={} left={} left_head={} right={}",
                        diagnostic_span.file,
                        diagnostic_span.first.line,
                        nl,
                        crate::elaborated::type_display::format_constructor(&left_normalized),
                        debug_constructor_head_name(elaboration_environment, &left_normalized),
                        crate::elaborated::type_display::format_constructor(&right_normalized),
                    );
                }
                Box::new(FailedToUnifyConstructors::ConstructorTooDeepForUnif)
            })?;
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
                    &right_normalized,
                    recursion_depth + 1,
                );
            }
            if let Ok((_, _, Some(def2))) = elaboration_environment.lookup_c_named(*n2) {
                return unify_cons_inner(
                    elaboration_context,
                    elaboration_environment,
                    diagnostic_span,
                    &left_normalized,
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
                    &right_normalized,
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
                    &left_normalized,
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
        // Peel implicit `:::` binders until both sides are arrows (flex instantiation during `checkCon`).
        (
            elab::Constructor::TCFun(elab::Explicitness::Implicit, x, k, b1),
            elab::Constructor::TFun(_, _),
        ) => {
            let cu = fresh_cunif(
                elaboration_environment,
                diagnostic_span.clone(),
                *k.clone(),
                x.as_str(),
            );
            let body_subst = match sub_con_in_con(0, &cu, *b1.clone()) {
                Ok(substituted) => substituted,
                Err(_) => {
                    return Err(Box::new(
                        FailedToUnifyConstructors::IncompatibleConstructors(
                            left_normalized,
                            right_normalized,
                        ),
                    ));
                }
            };
            unify_cons_inner(
                elaboration_context,
                elaboration_environment,
                diagnostic_span,
                &body_subst,
                &right_normalized,
                recursion_depth + 1,
            )
        }
        (
            elab::Constructor::TFun(_, _),
            elab::Constructor::TCFun(elab::Explicitness::Implicit, _, _, _),
        ) => unify_cons_inner(
            elaboration_context,
            elaboration_environment,
            diagnostic_span,
            &right_normalized,
            &left_normalized,
            recursion_depth + 1,
        ),
        (elab::Constructor::TCFun(e1, x1, k1, b1), elab::Constructor::TCFun(e2, _, k2, b2)) => {
            if e1 != e2 {
                return Err(Box::new(
                    FailedToUnifyConstructors::IncompatibleConstructors(
                        left_normalized,
                        right_normalized,
                    ),
                ));
            }
            if let Err(kind_failure) = unify_kinds(elaboration_environment, k1, k2) {
                if std::env::var("URWEB_DEBUG_TOP_CON_KIND").ok().as_deref() == Some("1")
                    && diagnostic_span.file.ends_with("/lib/ur/top.ur")
                {
                    eprintln!(
                        "top con kind debug line={} left={} right={} left_kind={} right_kind={}",
                        diagnostic_span.first.line,
                        crate::elaborated::type_display::format_constructor(&left_normalized),
                        crate::elaborated::type_display::format_constructor(&right_normalized),
                        crate::elaborated::type_display::format_kind(k1),
                        crate::elaborated::type_display::format_kind(k2),
                    );
                }
                return Err(Box::new(FailedToUnifyConstructors::KindUnificationFailed(
                    *kind_failure,
                )));
            }
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
        (elab::Constructor::TRecord(record_row), elab::Constructor::Tuple(tuple_components)) => {
            unify_closed_numeric_record_with_tuple(
                elaboration_context,
                elaboration_environment,
                diagnostic_span,
                &left_normalized,
                &right_normalized,
                record_row,
                tuple_components,
                recursion_depth,
            )
        }
        (elab::Constructor::Tuple(tuple_components), elab::Constructor::TRecord(record_row)) => {
            unify_closed_numeric_record_with_tuple(
                elaboration_context,
                elaboration_environment,
                diagnostic_span,
                &right_normalized,
                &left_normalized,
                record_row,
                tuple_components,
                recursion_depth,
            )
        }
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
            if let Err(kind_failure) = unify_kinds(elaboration_environment, k1, k2) {
                if std::env::var("URWEB_DEBUG_TOP_CON_KIND").ok().as_deref() == Some("1")
                    && diagnostic_span.file.ends_with("/lib/ur/top.ur")
                {
                    eprintln!(
                        "top con kind debug line={} left={} right={} left_kind={} right_kind={}",
                        diagnostic_span.first.line,
                        crate::elaborated::type_display::format_constructor(&left_normalized),
                        crate::elaborated::type_display::format_constructor(&right_normalized),
                        crate::elaborated::type_display::format_kind(k1),
                        crate::elaborated::type_display::format_kind(k2),
                    );
                }
                return Err(Box::new(FailedToUnifyConstructors::KindUnificationFailed(
                    *kind_failure,
                )));
            }
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
            if let Err(kind_failure) = unify_kinds(elaboration_environment, k1, k2) {
                if std::env::var("URWEB_DEBUG_TOP_CON_KIND").ok().as_deref() == Some("1")
                    && diagnostic_span.file.ends_with("/lib/ur/top.ur")
                {
                    eprintln!(
                        "top con kind debug line={} left={} right={} left_kind={} right_kind={}",
                        diagnostic_span.first.line,
                        crate::elaborated::type_display::format_constructor(&left_normalized),
                        crate::elaborated::type_display::format_constructor(&right_normalized),
                        crate::elaborated::type_display::format_kind(k1),
                        crate::elaborated::type_display::format_kind(k2),
                    );
                }
                Err(Box::new(FailedToUnifyConstructors::KindUnificationFailed(
                    *kind_failure,
                )))
            } else {
                Ok(())
            }
        }
        (
            elab::Constructor::Map(left_domain, left_range),
            elab::Constructor::Map(right_domain, right_range),
        ) => {
            if let Err(kind_failure) =
                unify_kinds(elaboration_environment, left_domain, right_domain)
            {
                return Err(Box::new(FailedToUnifyConstructors::KindUnificationFailed(
                    *kind_failure,
                )));
            }
            if let Err(kind_failure) = unify_kinds(elaboration_environment, left_range, right_range)
            {
                return Err(Box::new(FailedToUnifyConstructors::KindUnificationFailed(
                    *kind_failure,
                )));
            }
            Ok(())
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
        // Row constructors: try record summary unification, then map-unfolding fallback.
        _ => {
            // Try beta/eta reduction before giving up on structural matching.
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
            // If either side is `map f r`, use guess_map eagerly before trying row summaries.
            // Row summary unification does not understand map applications (it puts them in
            // `others`), so trying guess_map first avoids spurious deferred constraints that
            // would never resolve.
            if peel_map_app(&left_normalized).is_some() || peel_map_app(&right_normalized).is_some()
            {
                return guess_map(
                    elaboration_context,
                    elaboration_environment,
                    diagnostic_span,
                    &left_normalized,
                    &right_normalized,
                    recursion_depth,
                );
            }
            // Row unification via summaries (handles Concat/Unif tails, defers when mayDelay).
            let row_result = unify_rows(
                elaboration_context,
                elaboration_environment,
                diagnostic_span,
                &left_normalized,
                &right_normalized,
                recursion_depth,
            );
            if row_result.is_ok() {
                return Ok(());
            }
            // Final fallback: try guess_map in case row-summary unification could not solve it.
            // This handles cases where reduce_con did not expose the map form until after
            // row_result failure (rare, but mirrors SML exception-catching order).
            let map_result = guess_map(
                elaboration_context,
                elaboration_environment,
                diagnostic_span,
                &left_normalized,
                &right_normalized,
                recursion_depth,
            );
            if map_result.is_ok() {
                return Ok(());
            }
            // Return the original row-unification error for a better diagnostic.
            row_result
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
    // Compute the row element kind once so any synthesized shared row tails use the same shape.
    let row_element_kind = match hnorm_kind(kindof(
        elaboration_context,
        elaboration_environment,
        left_constructor,
    ))
    .node
    {
        // Preserve the row element kind when the caller really passed a row constructor.
        elab::Kind::Record(inner_kind) => *inner_kind,
        // Fall back to `Type` on malformed inputs so the helper code stays total.
        _ => Located::new(elab::Kind::Type, diagnostic_span.clone()),
    };
    // Reuse the enclosing row kind when we need a fresh shared row-tail unification variable.
    let row_kind = Located::new(
        elab::Kind::Record(Box::new(row_element_kind.clone())),
        diagnostic_span.clone(),
    );
    let left_summary = record_summary(elaboration_environment, left_constructor.clone());
    let right_summary = record_summary(elaboration_environment, right_constructor.clone());
    // Match SML `consNeq`: only return `true` when two field names are provably distinct.
    let names_are_definitely_distinct =
        |left_name: &elab::LocatedConstructor, right_name: &elab::LocatedConstructor| match (
            &hnorm_con(left_name.clone()).node,
            &hnorm_con(right_name.clone()).node,
        ) {
            // Distinct literal names are definitely different.
            (elab::Constructor::Name(left_symbol), elab::Constructor::Name(right_symbol)) => {
                left_symbol != right_symbol
            }
            // Distinct de Bruijn names are definitely different.
            (elab::Constructor::Rel(left_index), elab::Constructor::Rel(right_index)) => {
                left_index != right_index
            }
            // Distinct named constructors are definitely different.
            (elab::Constructor::Named(left_index), elab::Constructor::Named(right_index)) => {
                left_index != right_index
            }
            // Distinct module projections with the same surface path shape are definitely different.
            (
                elab::Constructor::ModProj(left_root, left_modules, left_field),
                elab::Constructor::ModProj(right_root, right_modules, right_field),
            ) => {
                left_root != right_root
                    || left_modules != right_modules
                    || left_field != right_field
            }
            // Name literals are distinct from all rel/named/module-projected names.
            (elab::Constructor::Name(_), elab::Constructor::Rel(_))
            | (elab::Constructor::Rel(_), elab::Constructor::Name(_))
            | (elab::Constructor::Name(_), elab::Constructor::Named(_))
            | (elab::Constructor::Named(_), elab::Constructor::Name(_))
            | (elab::Constructor::Name(_), elab::Constructor::ModProj(_, _, _))
            | (elab::Constructor::ModProj(_, _, _), elab::Constructor::Name(_))
            | (elab::Constructor::Rel(_), elab::Constructor::Named(_))
            | (elab::Constructor::Named(_), elab::Constructor::Rel(_))
            | (elab::Constructor::Rel(_), elab::Constructor::ModProj(_, _, _))
            | (elab::Constructor::ModProj(_, _, _), elab::Constructor::Rel(_)) => true,
            // Any other pair may still unify, so do not treat it as definitely distinct.
            _ => false,
        };
    // Match SML `List.all ... consNeq`: every left field name must be definitely distinct
    // from every right field name before we synthesize a shared row tail.
    let fields_are_pairwise_distinct =
        |left_fields: &Vec<(elab::LocatedConstructor, elab::LocatedConstructor)>,
         right_fields: &Vec<(elab::LocatedConstructor, elab::LocatedConstructor)>| {
            left_fields.iter().all(|(left_name, _)| {
                right_fields
                    .iter()
                    .all(|(right_name, _)| names_are_definitely_distinct(left_name, right_name))
            })
        };

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
                    .position(|(field_name_right, field_type_right)| {
                        row_field_pair_matches(
                            elaboration_context,
                            elaboration_environment,
                            diagnostic_span,
                            field_name_left,
                            field_type_left,
                            field_name_right,
                            field_type_right,
                            recursion_depth,
                        )
                    })
            {
                let _ = right_fields_remaining.remove(position);
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

    let empty_row = || {
        Located::new(
            elab::Constructor::Record(Box::new(row_kind.clone()), Vec::new()),
            diagnostic_span.clone(),
        )
    };

    // Mirror the first SML `unifySummaries` empty-row cases:
    // if one side has only row-tail unifs and the other side is structurally empty,
    // solve each unknown tail to the empty row immediately.
    if left_summary.fields.is_empty()
        && left_summary.others.is_empty()
        && right_summary.unifs.is_empty()
        && right_summary.fields.is_empty()
        && right_summary.others.is_empty()
    {
        let solution = empty_row();
        for left_unif in &left_summary.unifs {
            let row_tail_cell = match &left_unif.node {
                elab::Constructor::Unif(_, _, _, _, row_tail_cell) => row_tail_cell.clone(),
                _ => unreachable!("RecordSummary.unifs must contain Constructor::Unif nodes"),
            };
            *crate::compiler_diagnostics::lock_for_compile(
                row_tail_cell.as_ref(),
                "elaboration unification cell empty-row left",
            ) = elab::CUnif::Known(Box::new(solution.clone()));
        }
        return Ok(());
    }
    if right_summary.fields.is_empty()
        && right_summary.others.is_empty()
        && left_summary.unifs.is_empty()
        && left_summary.fields.is_empty()
        && left_summary.others.is_empty()
    {
        let solution = empty_row();
        for right_unif in &right_summary.unifs {
            let row_tail_cell = match &right_unif.node {
                elab::Constructor::Unif(_, _, _, _, row_tail_cell) => row_tail_cell.clone(),
                _ => unreachable!("RecordSummary.unifs must contain Constructor::Unif nodes"),
            };
            *crate::compiler_diagnostics::lock_for_compile(
                row_tail_cell.as_ref(),
                "elaboration unification cell empty-row right",
            ) = elab::CUnif::Known(Box::new(solution.clone()));
        }
        return Ok(());
    }

    // When one side is a single rigid/abstract row piece and the other side is a pure
    // concatenation of unknown row tails, solve the first tail to that row and the rest
    // to empty. This matches the common `inp` vs `?use ++ ?bind` XML/join shape in boot Top.
    if left_summary.fields.is_empty()
        && left_summary.unifs.is_empty()
        && left_summary.others.len() == 1
        && right_summary.fields.is_empty()
        && right_summary.others.is_empty()
        && !right_summary.unifs.is_empty()
    {
        let left_row_piece = left_summary.others[0].clone();
        let first_right_tail_cell = match &right_summary.unifs[0].node {
            elab::Constructor::Unif(_, _, _, _, row_tail_cell) => row_tail_cell.clone(),
            _ => unreachable!("RecordSummary.unifs must contain Constructor::Unif nodes"),
        };
        if !occurs_cunif(&first_right_tail_cell, &left_row_piece) {
            *crate::compiler_diagnostics::lock_for_compile(
                first_right_tail_cell.as_ref(),
                "elaboration unification cell rigid-row right-first",
            ) = elab::CUnif::Known(Box::new(left_row_piece));
            let empty_solution = empty_row();
            for right_unif in &right_summary.unifs[1..] {
                let row_tail_cell = match &right_unif.node {
                    elab::Constructor::Unif(_, _, _, _, unif_cell) => unif_cell.clone(),
                    _ => unreachable!("RecordSummary.unifs must contain Constructor::Unif nodes"),
                };
                *crate::compiler_diagnostics::lock_for_compile(
                    row_tail_cell.as_ref(),
                    "elaboration unification cell rigid-row right-rest",
                ) = elab::CUnif::Known(Box::new(empty_solution.clone()));
            }
            return Ok(());
        }
    }
    if right_summary.fields.is_empty()
        && right_summary.unifs.is_empty()
        && right_summary.others.len() == 1
        && left_summary.fields.is_empty()
        && left_summary.others.is_empty()
        && !left_summary.unifs.is_empty()
    {
        let right_row_piece = right_summary.others[0].clone();
        let first_left_tail_cell = match &left_summary.unifs[0].node {
            elab::Constructor::Unif(_, _, _, _, row_tail_cell) => row_tail_cell.clone(),
            _ => unreachable!("RecordSummary.unifs must contain Constructor::Unif nodes"),
        };
        if !occurs_cunif(&first_left_tail_cell, &right_row_piece) {
            *crate::compiler_diagnostics::lock_for_compile(
                first_left_tail_cell.as_ref(),
                "elaboration unification cell rigid-row left-first",
            ) = elab::CUnif::Known(Box::new(right_row_piece));
            let empty_solution = empty_row();
            for left_unif in &left_summary.unifs[1..] {
                let row_tail_cell = match &left_unif.node {
                    elab::Constructor::Unif(_, _, _, _, unif_cell) => unif_cell.clone(),
                    _ => unreachable!("RecordSummary.unifs must contain Constructor::Unif nodes"),
                };
                *crate::compiler_diagnostics::lock_for_compile(
                    row_tail_cell.as_ref(),
                    "elaboration unification cell rigid-row left-rest",
                ) = elab::CUnif::Known(Box::new(empty_solution.clone()));
            }
            return Ok(());
        }
    }

    // Mirrors SML `unifySummaries` pattern 1: `([(_, r)], [], [], _, _, _)`.
    // Left has exactly 1 unif (nl=0), 0 unmatched fields, 0 others; right may have anything.
    // Since RecordSummary.unifs only holds nl=0 Unifs, no squish is needed: nl=0 means
    // the unif was created at the outermost scope, so the solution needs no index adjustment.
    // Solution: r := unsummarize(right remaining fields ++ right unifs ++ right others).
    if left_summary.unifs.len() == 1 && left_summary.others.is_empty() {
        // Extract the Unif cell from the stored nl=0 located constructor.
        let row_tail_cell = match &left_summary.unifs[0].node {
            elab::Constructor::Unif(_, _, _, _, r) => r.clone(),
            // RecordSummary.unifs only ever contains Unif nodes; any other variant is a bug.
            _ => unreachable!("RecordSummary.unifs must contain Constructor::Unif nodes"),
        };
        // Match all left fields against right fields (order-independent), unifying types.
        // SML eatMatching calls consEq(c1, c2) which invokes unifyCons — so we also unify
        // field types here, not just names.  Only consume a pair when both name and type unify.
        // SML requires fields1=[] after eatMatching, meaning every left field was consumed.
        let mut right_fields_remaining = right_summary.fields.clone();
        let mut all_left_fields_matched = true;
        for (field_name_left, field_type_left) in &left_summary.fields {
            if let Some(pos) =
                right_fields_remaining
                    .iter()
                    .position(|(field_name_right, field_type_right)| {
                        row_field_pair_matches(
                            elaboration_context,
                            elaboration_environment,
                            diagnostic_span,
                            field_name_left,
                            field_type_left,
                            field_name_right,
                            field_type_right,
                            recursion_depth,
                        )
                    })
            {
                right_fields_remaining.remove(pos);
            } else {
                all_left_fields_matched = false;
                break;
            }
        }
        if all_left_fields_matched {
            // Build solution from ALL remaining right pieces (fields + unifs + others).
            // This mirrors SML `unsummarize {fields=fs2, unifs=unifs2, others=others2}`.
            let solution = unsummarize_summary(
                &right_fields_remaining,
                &right_summary.unifs,
                &right_summary.others,
                diagnostic_span,
            );
            // Occurs check: refuse cyclic solutions (mirrors SML `occursCon r c`).
            // No squish needed: unifs in RecordSummary always have nl=0.
            if !occurs_cunif(&row_tail_cell, &solution) {
                *crate::compiler_diagnostics::lock_for_compile(
                    row_tail_cell.as_ref(),
                    "elaboration unification cell",
                ) = elab::CUnif::Known(Box::new(solution));
                return Ok(());
            }
        }
    }
    // Symmetric: SML pattern 2 `(_, _, _, [(_, r)], [], [])`.
    // Right has exactly 1 unif (nl=0), 0 unmatched fields, 0 others; left may have anything.
    if right_summary.unifs.len() == 1 && right_summary.others.is_empty() {
        // Extract the Unif cell from the stored nl=0 located constructor.
        let row_tail_cell = match &right_summary.unifs[0].node {
            elab::Constructor::Unif(_, _, _, _, r) => r.clone(),
            _ => unreachable!("RecordSummary.unifs must contain Constructor::Unif nodes"),
        };
        // Match all right fields against left fields (order-independent), unifying types.
        // SML eatMatching calls consEq(c1, c2) which invokes unifyCons.
        // SML requires fields2=[] after eatMatching, meaning every right field was consumed.
        let mut left_fields_remaining = left_summary.fields.clone();
        let mut all_right_fields_matched = true;
        for (field_name_right, field_type_right) in &right_summary.fields {
            if let Some(pos) =
                left_fields_remaining
                    .iter()
                    .position(|(field_name_left, field_type_left)| {
                        row_field_pair_matches(
                            elaboration_context,
                            elaboration_environment,
                            diagnostic_span,
                            field_name_left,
                            field_type_left,
                            field_name_right,
                            field_type_right,
                            recursion_depth,
                        )
                    })
            {
                left_fields_remaining.remove(pos);
            } else {
                all_right_fields_matched = false;
                break;
            }
        }
        if all_right_fields_matched {
            // Build solution from ALL remaining left pieces (fields + unifs + others).
            let solution = unsummarize_summary(
                &left_fields_remaining,
                &left_summary.unifs,
                &left_summary.others,
                diagnostic_span,
            );
            // Occurs check: refuse cyclic solutions.
            // No squish needed: unifs in RecordSummary always have nl=0.
            if !occurs_cunif(&row_tail_cell, &solution) {
                *crate::compiler_diagnostics::lock_for_compile(
                    row_tail_cell.as_ref(),
                    "elaboration unification cell",
                ) = elab::CUnif::Known(Box::new(solution));
                return Ok(());
            }
        }
    }

    // Mirror the SML shared-tail case:
    // one row-tail unif on each side, no abstract `others`, and pairwise-disjoint fields.
    // In that situation both tails can be solved as "the other side's fields ++ shared_tail".
    if left_summary.unifs.len() == 1
        && right_summary.unifs.len() == 1
        && left_summary.others.is_empty()
        && right_summary.others.is_empty()
        && fields_are_pairwise_distinct(&left_summary.fields, &right_summary.fields)
    {
        // Extract the left unknown row-tail cell.
        let left_row_tail_cell = match &left_summary.unifs[0].node {
            elab::Constructor::Unif(_, _, _, _, row_tail_cell) => row_tail_cell.clone(),
            _ => unreachable!("RecordSummary.unifs must contain Constructor::Unif nodes"),
        };
        // Extract the right unknown row-tail cell.
        let right_row_tail_cell = match &right_summary.unifs[0].node {
            elab::Constructor::Unif(_, _, _, _, row_tail_cell) => row_tail_cell.clone(),
            _ => unreachable!("RecordSummary.unifs must contain Constructor::Unif nodes"),
        };
        // Share one fresh tail so both solved rows keep the same residual unknown.
        let shared_row_tail = fresh_cunif(
            elaboration_environment,
            diagnostic_span.clone(),
            row_kind,
            "_shared_row_tail",
        );
        // Rebuild the right side's concrete fields as a row constructor.
        let right_fields_row = unsummarize_summary(
            &right_summary.fields,
            &Vec::new(),
            &Vec::new(),
            diagnostic_span,
        );
        // Rebuild the left side's concrete fields as a row constructor.
        let left_fields_row = unsummarize_summary(
            &left_summary.fields,
            &Vec::new(),
            &Vec::new(),
            diagnostic_span,
        );
        // Solve the left tail as "right fields ++ shared tail".
        let left_solution = Located::new(
            elab::Constructor::Concat(
                Box::new(right_fields_row),
                Box::new(shared_row_tail.clone()),
            ),
            diagnostic_span.clone(),
        );
        // Solve the right tail as "left fields ++ shared tail".
        let right_solution = Located::new(
            elab::Constructor::Concat(Box::new(left_fields_row), Box::new(shared_row_tail)),
            diagnostic_span.clone(),
        );
        // Only assign the synthesized solution when it does not create a cycle on the left.
        let left_assignable = !occurs_cunif(&left_row_tail_cell, &left_solution);
        // Only assign the synthesized solution when it does not create a cycle on the right.
        let right_assignable = !occurs_cunif(&right_row_tail_cell, &right_solution);
        match (left_assignable, right_assignable) {
            // The shared-tail reduction succeeded for both sides.
            (true, true) => {
                *crate::compiler_diagnostics::lock_for_compile(
                    left_row_tail_cell.as_ref(),
                    "elaboration unification cell shared-tail left",
                ) = elab::CUnif::Known(Box::new(left_solution));
                *crate::compiler_diagnostics::lock_for_compile(
                    right_row_tail_cell.as_ref(),
                    "elaboration unification cell shared-tail right",
                ) = elab::CUnif::Known(Box::new(right_solution));
                return Ok(());
            }
            // Fall through to the rest of the row-unification logic when either side cycles.
            _ => {}
        }
    }

    // Mirror the SML `isGuessable` shortcut:
    // if one side is a single abstract `other` and the other side is a pure record/unif summary,
    // try `guess_map` immediately before deferring.
    if left_summary.fields.is_empty()
        && left_summary.unifs.is_empty()
        && left_summary.others.len() == 1
        && right_summary.others.is_empty()
    {
        // Rebuild the right side into the concrete row that SML passes to `guessMap`.
        let right_summary_row = unsummarize_summary(
            &right_summary.fields,
            &right_summary.unifs,
            &right_summary.others,
            diagnostic_span,
        );
        // Try the SML-style map guess; ignore failure and continue with normal fallback paths.
        if guess_map(
            elaboration_context,
            elaboration_environment,
            diagnostic_span,
            &left_summary.others[0],
            &right_summary_row,
            recursion_depth + 1,
        )
        .is_ok()
        {
            return Ok(());
        }
    }
    // Symmetric SML `isGuessable` shortcut for a single right-side abstract `other`.
    if right_summary.fields.is_empty()
        && right_summary.unifs.is_empty()
        && right_summary.others.len() == 1
        && left_summary.others.is_empty()
    {
        // Rebuild the left side into the concrete row that SML passes to `guessMap`.
        let left_summary_row = unsummarize_summary(
            &left_summary.fields,
            &left_summary.unifs,
            &left_summary.others,
            diagnostic_span,
        );
        // Try the SML-style map guess; ignore failure and continue with normal fallback paths.
        if guess_map(
            elaboration_context,
            elaboration_environment,
            diagnostic_span,
            &left_summary_row,
            &right_summary.others[0],
            recursion_depth + 1,
        )
        .is_ok()
        {
            return Ok(());
        }
    }

    // Both sides have the same number of abstract `others` pieces and no Unif tails.
    // Try matching fields order-independently and unifying the `others` pieces pairwise.
    // This handles the common `field ++ abstract_tail  vs  abstract_tail ++ field` pattern
    // that arises in map0/foldR/etc. (commutativity of disjoint row concatenation).
    if left_summary.unifs.is_empty()
        && right_summary.unifs.is_empty()
        && !left_summary.others.is_empty()
        && left_summary.others.len() == right_summary.others.len()
        && left_summary.fields.len() == right_summary.fields.len()
        && (!left_summary.fields.is_empty() || !right_summary.fields.is_empty())
    {
        // Check all known fields match pairwise (order-independent).
        // Fields in RecordSummary.fields use concrete Name keys (as Located constructors).
        let mut right_fields_remaining = right_summary.fields.clone();
        let mut all_fields_matched = true;
        for (field_name_left, field_type_left) in &left_summary.fields {
            if let Some(position) =
                right_fields_remaining
                    .iter()
                    .position(|(field_name_right, field_type_right)| {
                        row_field_pair_matches(
                            elaboration_context,
                            elaboration_environment,
                            diagnostic_span,
                            field_name_left,
                            field_type_left,
                            field_name_right,
                            field_type_right,
                            recursion_depth,
                        )
                    })
            {
                let _ = right_fields_remaining.remove(position);
            } else {
                all_fields_matched = false;
                break;
            }
        }
        if all_fields_matched && right_fields_remaining.is_empty() {
            // Try to unify abstract pieces pairwise.
            let mut others_ok = true;
            for (left_other, right_other) in
                left_summary.others.iter().zip(right_summary.others.iter())
            {
                // Try unifying other piece; if it fails, fall through to error/delay.
                if unify_cons_inner(
                    elaboration_context,
                    elaboration_environment,
                    diagnostic_span,
                    left_other,
                    right_other,
                    recursion_depth + 1,
                )
                .is_err()
                {
                    others_ok = false;
                    break;
                }
            }
            if others_ok {
                return Ok(());
            }
        }
    }

    // SML final-dispatch: solve a deeper (nl>0) CUnif that landed in `others`.
    // These mirror the last patterns before `default()` in SML's `unifySummaries`:
    //   `(_, _, _, [], [], [CUnif(nl)])` — right has exactly 1 CUnif in others, nothing else
    //   `([], [], [CUnif(nl)], _, _, _)` — left has exactly 1 CUnif in others, nothing else
    // The solution is squished by `nl` to match the unif's creation depth; on CantSquish, fall through.
    if right_summary.unifs.is_empty()
        && right_summary.fields.is_empty()
        && right_summary.others.len() == 1
    {
        // Check whether the single right-side other IS a CUnif (nl>0).
        let right_other = &right_summary.others[0];
        if let elab::Constructor::Unif(nl, _, _, _, ref r_cell) = right_other.node {
            let current = {
                let guard = crate::compiler_diagnostics::lock_for_compile(
                    r_cell.as_ref(),
                    "unify_rows final-dispatch read",
                );
                guard.clone()
            };
            if matches!(current, elab::CUnif::Unknown) && !occurs_cunif(r_cell, left_constructor) {
                // Build the full left summary into a row constructor.
                let solution = unsummarize_summary(
                    &left_summary.fields,
                    &left_summary.unifs,
                    &left_summary.others,
                    diagnostic_span,
                );
                // Squish by nl to adjust for the creation-depth of this CUnif.
                // If squish fails (solution references locals inside nl binders), fall through to defer.
                if let Ok(adjusted) = squish_con(nl, solution) {
                    *crate::compiler_diagnostics::lock_for_compile(
                        r_cell.as_ref(),
                        "elaboration unification cell final-dispatch right",
                    ) = elab::CUnif::Known(Box::new(adjusted));
                    return Ok(());
                }
                // CantSquish: fall through to the defer/fail block below.
            }
        }
    }
    // Symmetric: left has exactly 1 CUnif (nl>0) in others, no unifs, no fields.
    if left_summary.unifs.is_empty()
        && left_summary.fields.is_empty()
        && left_summary.others.len() == 1
    {
        let left_other = &left_summary.others[0];
        if let elab::Constructor::Unif(nl, _, _, _, ref l_cell) = left_other.node {
            let current = {
                let guard = crate::compiler_diagnostics::lock_for_compile(
                    l_cell.as_ref(),
                    "unify_rows final-dispatch read left",
                );
                guard.clone()
            };
            if matches!(current, elab::CUnif::Unknown) && !occurs_cunif(l_cell, right_constructor) {
                // Build the full right summary into a row constructor.
                let solution = unsummarize_summary(
                    &right_summary.fields,
                    &right_summary.unifs,
                    &right_summary.others,
                    diagnostic_span,
                );
                if let Ok(adjusted) = squish_con(nl, solution) {
                    *crate::compiler_diagnostics::lock_for_compile(
                        l_cell.as_ref(),
                        "elaboration unification cell final-dispatch left",
                    ) = elab::CUnif::Known(Box::new(adjusted));
                    return Ok(());
                }
                // CantSquish: fall through.
            }
        }
    }

    // Otherwise, delay if mayDelay is set, else fail immediately.
    if elaboration_context.may_delay {
        // Temporary debug: print RowUnification creation site for the '15 vs '3 investigation.
        if std::env::var("URWEB_DEBUG_ROW_UNIF").is_ok() {
            eprintln!(
                "[RowUnif deferred] span={:?} left={} right={}",
                diagnostic_span,
                crate::elaborated::type_display::format_constructor(left_constructor),
                crate::elaborated::type_display::format_constructor(right_constructor),
            );
        }
        // Leave for later constraint solving; push a RowUnification constraint so
        // solve_constraints can retry once more unification variables are filled in.
        elaboration_context
            .constraints
            .push(Constraint::RowUnification {
                span: diagnostic_span.clone(),
                elaboration_environment: elaboration_environment.clone(),
                left_constructor: left_constructor.clone(),
                right_constructor: right_constructor.clone(),
            });
        return Ok(()); // optimistically succeed; solve_constraints will catch real failures
    }
    Err(Box::new(
        FailedToUnifyConstructors::IncompatibleConstructors(
            left_constructor.clone(),
            right_constructor.clone(),
        ),
    ))
}

// ---------------------------------------------------------------------------
// guess_map: unify `map f r` with a concrete row (mirror of SML `guessMap`)
// ---------------------------------------------------------------------------

/// Extract `(domain_kind, range_kind, map_function, pre_image_row)` from
/// `App(App(Map(domain_kind, range_kind), map_function), pre_image_row)`.
///
/// Returns `None` if the constructor is not in the expected map-application form after
/// head-normalisation. This is used by [`guess_map`] to detect which side (if any) of a
/// failing unification attempt is a `map`-applied row.
fn peel_map_app(
    constructor: &elab::LocatedConstructor,
) -> Option<(
    elab::LocatedKind,
    elab::LocatedKind,
    elab::LocatedConstructor,
    elab::LocatedConstructor,
)> {
    // Head-normalise so that solved unification variables and beta-redexes are resolved.
    let outer_normalized = hnorm_con(constructor.clone());
    // Outer layer must be App(middle, pre_image_row).
    if let elab::Constructor::App(middle_app, pre_image_row) = outer_normalized.node {
        let middle_normalized = hnorm_con(*middle_app);
        // Middle layer must be App(map_con, map_function).
        if let elab::Constructor::App(map_constructor, map_function) = middle_normalized.node {
            let map_normalized = hnorm_con(*map_constructor);
            // Inner layer must be Map(domain_kind, range_kind).
            if let elab::Constructor::Map(domain_kind, range_kind) = map_normalized.node {
                return Some((*domain_kind, *range_kind, *map_function, *pre_image_row));
            }
        }
    }
    None
}

/// Recursive unfold helper for [`guess_map`].
///
/// Given that we know `map(domain_kind, range_kind) map_function pre_image_row` must equal
/// `post_image_constructor`, determines what `pre_image_row` must be by recursively examining
/// the structure of `post_image_constructor` and mutating unification variables.
///
/// Mirrors the inner `unfold` closure inside SML `guessMap`.
///
/// # Arguments
///
/// * `domain_kind` — Element kind of the pre-image record (source of the map).
/// * `range_kind` — Element kind of the post-image record (target of the map).
/// * `map_function` — The type-level constructor `f :: domain_kind -> range_kind`.
/// * `pre_image_row` — The row we are solving for (what `r` in `map f r` must equal).
/// * `post_image_constructor` — What `map f r` must equal (the concrete/partially-known post row).
fn guess_map_unfold(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    diagnostic_span: &Span,
    domain_kind: &elab::LocatedKind,
    range_kind: &elab::LocatedKind,
    map_function: &elab::LocatedConstructor,
    pre_image_row: &elab::LocatedConstructor,
    post_image_constructor: &elab::LocatedConstructor,
    recursion_depth: usize,
) -> Result<(), Box<FailedToUnifyConstructors>> {
    if recursion_depth > 100 {
        // Depth cap prevents unbounded recursion on pathological inputs.
        return Err(Box::new(
            FailedToUnifyConstructors::UnificationRecursionLimitExceeded,
        ));
    }
    let span = diagnostic_span;
    // Head-normalise to resolve known unification variables and beta-redexes before switching.
    let post_normalized = hnorm_con(post_image_constructor.clone());

    match post_normalized.node.clone() {
        // Empty record {} → pre-image must also be the empty record of domain_kind.
        elab::Constructor::Record(_, ref fields) if fields.is_empty() => {
            let empty_pre_image = Located::new(
                elab::Constructor::Record(
                    Box::new(Located::new(
                        elab::Kind::Record(Box::new(domain_kind.clone())),
                        span.clone(),
                    )),
                    vec![],
                ),
                span.clone(),
            );
            // Unify pre_image_row = {}
            unify_cons_inner(
                elaboration_context,
                elaboration_environment,
                span,
                pre_image_row,
                &empty_pre_image,
                recursion_depth + 1,
            )
        }

        // Non-empty record — split into first field (singleton) + rest and handle each.
        elab::Constructor::Record(post_row_kind, ref fields) if !fields.is_empty() => {
            let (first_name_constructor, first_value_constructor) = fields[0].clone();
            let rest_fields: Vec<(elab::LocatedConstructor, elab::LocatedConstructor)> =
                fields[1..].to_vec(); // remaining fields after the first

            if rest_fields.is_empty() {
                // Singleton case: {nm = v} → v = map_function(v'), pre_image_row = {nm = v'}
                // Create the pre-image value: Unit if domain_kind = Unit, else a fresh unif variable.
                let pre_image_value = match hnorm_kind(domain_kind.clone()).node {
                    elab::Kind::Unit => Located::new(elab::Constructor::Unit, span.clone()),
                    _ => fresh_cunif(
                        elaboration_environment,
                        span.clone(),
                        domain_kind.clone(),
                        "_mv",
                    ),
                };
                // Unify first_value_constructor = map_function(pre_image_value)
                let function_applied = Located::new(
                    elab::Constructor::App(
                        Box::new(map_function.clone()),
                        Box::new(pre_image_value.clone()),
                    ),
                    span.clone(),
                );
                unify_cons_inner(
                    elaboration_context,
                    elaboration_environment,
                    span,
                    &first_value_constructor,
                    &function_applied,
                    recursion_depth + 1,
                )?;
                // Unify pre_image_row = {nm = pre_image_value}
                let singleton_pre_image = Located::new(
                    elab::Constructor::Record(
                        Box::new(Located::new(
                            elab::Kind::Record(Box::new(domain_kind.clone())),
                            span.clone(),
                        )),
                        vec![(first_name_constructor, pre_image_value)],
                    ),
                    span.clone(),
                );
                unify_cons_inner(
                    elaboration_context,
                    elaboration_environment,
                    span,
                    pre_image_row,
                    &singleton_pre_image,
                    recursion_depth + 1,
                )
            } else {
                // Multi-field case: split into singleton + rest, create two pre-image row unifs.
                let singleton_post = Located::new(
                    elab::Constructor::Record(
                        post_row_kind.clone(),
                        vec![(first_name_constructor, first_value_constructor)],
                    ),
                    span.clone(),
                );
                let rest_post = Located::new(
                    elab::Constructor::Record(post_row_kind, rest_fields),
                    span.clone(),
                );
                // Fresh row unification variables for the two pre-image sub-rows.
                let krecord_dom = Located::new(
                    elab::Kind::Record(Box::new(domain_kind.clone())),
                    span.clone(),
                );
                let pre_row_left = fresh_cunif(
                    elaboration_environment,
                    span.clone(),
                    krecord_dom.clone(),
                    "_mr1",
                );
                let pre_row_right =
                    fresh_cunif(elaboration_environment, span.clone(), krecord_dom, "_mr2");
                // Recursively unfold each sub-row.
                guess_map_unfold(
                    elaboration_context,
                    elaboration_environment,
                    span,
                    domain_kind,
                    range_kind,
                    map_function,
                    &pre_row_left,
                    &singleton_post,
                    recursion_depth + 1,
                )?;
                guess_map_unfold(
                    elaboration_context,
                    elaboration_environment,
                    span,
                    domain_kind,
                    range_kind,
                    map_function,
                    &pre_row_right,
                    &rest_post,
                    recursion_depth + 1,
                )?;
                // Unify pre_image_row = pre_row_left ++ pre_row_right
                let concat_pre = Located::new(
                    elab::Constructor::Concat(Box::new(pre_row_left), Box::new(pre_row_right)),
                    span.clone(),
                );
                unify_cons_inner(
                    elaboration_context,
                    elaboration_environment,
                    span,
                    pre_image_row,
                    &concat_pre,
                    recursion_depth + 1,
                )
            }
        }

        // Concatenated rows c1' ++ c2': split and determine pre-images for each half.
        elab::Constructor::Concat(post_left, post_right) => {
            let krecord_dom = Located::new(
                elab::Kind::Record(Box::new(domain_kind.clone())),
                span.clone(),
            );
            let pre_row_left = fresh_cunif(
                elaboration_environment,
                span.clone(),
                krecord_dom.clone(),
                "_mr1",
            );
            let pre_row_right =
                fresh_cunif(elaboration_environment, span.clone(), krecord_dom, "_mr2");
            guess_map_unfold(
                elaboration_context,
                elaboration_environment,
                span,
                domain_kind,
                range_kind,
                map_function,
                &pre_row_left,
                &post_left,
                recursion_depth + 1,
            )?;
            guess_map_unfold(
                elaboration_context,
                elaboration_environment,
                span,
                domain_kind,
                range_kind,
                map_function,
                &pre_row_right,
                &post_right,
                recursion_depth + 1,
            )?;
            let concat_pre = Located::new(
                elab::Constructor::Concat(Box::new(pre_row_left), Box::new(pre_row_right)),
                span.clone(),
            );
            unify_cons_inner(
                elaboration_context,
                elaboration_environment,
                span,
                pre_image_row,
                &concat_pre,
                recursion_depth + 1,
            )
        }

        // Unknown unification variable: set it to `map map_function pre_image_row`.
        elab::Constructor::Unif(nesting_level, _, _unif_kind, _, ref unif_cell) => {
            // Read the current cell value without holding the lock across the occurs check.
            let current_value = {
                let guard = crate::compiler_diagnostics::lock_for_compile(
                    unif_cell.as_ref(),
                    "guess_map_unfold check unif cell",
                );
                guard.clone() // clone so we can drop the lock before further work
            };
            match current_value {
                elab::CUnif::Known(known_constructor) => {
                    // Already resolved — chase through the known value and retry.
                    let resolved = hnorm_con(*known_constructor);
                    guess_map_unfold(
                        elaboration_context,
                        elaboration_environment,
                        span,
                        domain_kind,
                        range_kind,
                        map_function,
                        pre_image_row,
                        &resolved,
                        recursion_depth + 1,
                    )
                }
                elab::CUnif::Unknown => {
                    // Build `map(domain_kind, range_kind) map_function pre_image_row` and assign.
                    let map_applied_to_function = Located::new(
                        elab::Constructor::App(
                            Box::new(Located::new(
                                elab::Constructor::Map(
                                    Box::new(domain_kind.clone()),
                                    Box::new(range_kind.clone()),
                                ),
                                span.clone(),
                            )),
                            Box::new(map_function.clone()),
                        ),
                        span.clone(),
                    );
                    let map_f_pre_image = Located::new(
                        elab::Constructor::App(
                            Box::new(map_applied_to_function),
                            Box::new(pre_image_row.clone()),
                        ),
                        span.clone(),
                    );
                    // Occurs check: prevent circular constructors.
                    if occurs_cunif(unif_cell, &map_f_pre_image) {
                        return Err(Box::new(FailedToUnifyConstructors::OccursCheckWouldCycle));
                    }
                    // Squish adjusts from current depth to Unif's creation depth (mirrors SML unifyCons'').
                    let adjusted =
                        squish_con(nesting_level, map_f_pre_image).map_err(|CantSquish| {
                            Box::new(FailedToUnifyConstructors::ConstructorTooDeepForUnif)
                        })?;
                    *crate::compiler_diagnostics::lock_for_compile(
                        unif_cell.as_ref(),
                        "guess_map_unfold assign unif cell",
                    ) = elab::CUnif::Known(Box::new(adjusted));
                    Ok(())
                }
            }
        }

        // Any other constructor form: cannot determine the pre-image; fail.
        _ => Err(Box::new(
            FailedToUnifyConstructors::IncompatibleConstructors(
                post_image_constructor.clone(),
                pre_image_row.clone(),
            ),
        )),
    }
}

/// Mirror of SML `guessMap`: attempt to unify `map f r` with a concrete or partially-known row.
///
/// Called from [`unify_cons_inner`]'s wildcard fallback when standard structural unification
/// and row summary unification both fail and one side is of the form `map f r`.
///
/// Determines what the pre-image row `r` must be by examining the structure of the other side
/// and mutating unification variables in place.
///
/// # Returns
///
/// `Ok(())` when the map unification was successfully resolved; `Err(...)` otherwise.
fn guess_map(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    diagnostic_span: &Span,
    left_constructor: &elab::LocatedConstructor,
    right_constructor: &elab::LocatedConstructor,
    recursion_depth: usize,
) -> Result<(), Box<FailedToUnifyConstructors>> {
    // Check if the left side is map f r; if so, unfold the right to determine r.
    if let Some((domain_kind, range_kind, map_function, pre_image_row)) =
        peel_map_app(left_constructor)
    {
        return guess_map_unfold(
            elaboration_context,
            elaboration_environment,
            diagnostic_span,
            &domain_kind,
            &range_kind,
            &map_function,
            &pre_image_row,
            right_constructor,
            recursion_depth,
        );
    }
    // Check if the right side is map f r; if so, unfold the left to determine r.
    if let Some((domain_kind, range_kind, map_function, pre_image_row)) =
        peel_map_app(right_constructor)
    {
        return guess_map_unfold(
            elaboration_context,
            elaboration_environment,
            diagnostic_span,
            &domain_kind,
            &range_kind,
            &map_function,
            &pre_image_row,
            left_constructor,
            recursion_depth,
        );
    }
    // Neither side is a map application; cannot help.
    Err(Box::new(
        FailedToUnifyConstructors::IncompatibleConstructors(
            left_constructor.clone(),
            right_constructor.clone(),
        ),
    ))
}

/// Mirrors SML `unsummarize {fields, unifs, others}`: build a row constructor from summary pieces.
///
/// Produces `CRecord(k, fields) ++ unif_0 ++ unif_1 ++ ... ++ other_0 ++ ...`.
/// Each `++` is [`elab::Constructor::Concat`].  Used when solving a unification variable tail
/// to include all remaining right-side pieces (not just the field subset).
fn unsummarize_summary(
    fields: &[(elab::LocatedConstructor, elab::LocatedConstructor)],
    unifs: &[elab::LocatedConstructor],
    others: &[elab::LocatedConstructor],
    span: &Span,
) -> elab::LocatedConstructor {
    // Start with the fields assembled into a Record constructor.
    let ktype = Located::new(elab::Kind::Type, span.clone());
    let mut result = Located::new(
        elab::Constructor::Record(Box::new(ktype), fields.to_vec()),
        span.clone(),
    );
    // Concat each unification-variable tail piece onto the result row.
    for unif_piece in unifs {
        result = Located::new(
            elab::Constructor::Concat(Box::new(result), Box::new(unif_piece.clone())),
            span.clone(),
        );
    }
    // Concat each abstract "other" piece (e.g. `map f r`) onto the result row.
    for other_piece in others {
        result = Located::new(
            elab::Constructor::Concat(Box::new(result), Box::new(other_piece.clone())),
            span.clone(),
        );
    }
    result
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
        if std::env::var("URWEB_DEBUG_HIDDEN_TYPE_MISMATCH")
            .ok()
            .as_deref()
            == Some("1")
            && span.file == "<top>"
        {
            eprintln!(
                "hidden mismatch debug got={} expected={} got_head={} expected_head={} got_named=[{}] expected_named=[{}] msg={}",
                crate::elaborated::type_display::format_constructor(got),
                crate::elaborated::type_display::format_constructor(expected),
                debug_constructor_head_name(elaboration_environment, got),
                debug_constructor_head_name(elaboration_environment, expected),
                debug_named_ids_in_constructor(elaboration_environment, got),
                debug_named_ids_in_constructor(elaboration_environment, expected),
                format_failed_to_unify_constructors_message(e.as_ref()),
            );
        }
        if std::env::var("URWEB_DEBUG_TOP_TYPE_MISMATCH")
            .ok()
            .as_deref()
            == Some("1")
            && span.file.ends_with("/lib/ur/top.ur")
            && matches!(
                span.first.line,
                256 | 260
                    | 281
                    | 305
                    | 312
                    | 325
                    | 335
                    | 344
                    | 353
                    | 384
                    | 385
                    | 390
                    | 391
                    | 396
                    | 397
                    | 406
                    | 413
            )
        {
            eprintln!(
                "top mismatch debug line={} got={} expected={} got_head={} expected_head={}",
                span.first.line,
                crate::elaborated::type_display::format_constructor(got),
                crate::elaborated::type_display::format_constructor(expected),
                debug_constructor_head_name(elaboration_environment, got),
                debug_constructor_head_name(elaboration_environment, expected),
            );
        }
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

/// Finish elaborating a constructor pattern after resolving the datatype (unqualified or qualified module path).
///
/// Builds fresh type arguments for the datatype, unifies with `expected_type`, and optionally elaborates
/// the constructor payload pattern.
fn elab_pat_con_after_resolve(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    datatype_kind: crate::datatype_kind::DatatypeKind,
    pattern_constructor: elab::PatternConstructor,
    datatype_id: usize,
    type_params: &[String],
    arg_type: Option<&elab::LocatedConstructor>,
    arg_opt: Option<&source::LocPat>,
    expected_type: &elab::LocatedConstructor,
    ctor_name_for_errors: &str,
    span: &Span,
) -> (elab::LocatedPattern, Env) {
    let ktype = Located::new(elab::Kind::Type, span.clone());
    let type_args: Vec<elab::LocatedConstructor> = type_params
        .iter()
        .map(|_| fresh_cunif(elaboration_environment, span.clone(), ktype.clone(), "_"))
        .collect();

    let dt_con = {
        let base = Located::new(elab::Constructor::Named(datatype_id), span.clone());
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

    let (arg_pat_opt, new_env) = if let Some(at) = arg_type {
        let mut at2 = at.clone();
        for (i, ta) in type_args.iter().enumerate() {
            let idx = type_params.len() - 1 - i;
            at2 = match sub_con_in_con(idx, ta, at2) {
                Ok(c) => c,
                Err(_) => elaborated_constructor_error_at_span(span.clone()),
            };
        }
        if let Some(ap) = arg_opt {
            let (ap_e, new_env) = elab_pat(elaboration_context, elaboration_environment, ap, &at2);
            (Some(Box::new(ap_e)), new_env)
        } else {
            elaboration_context.error(
                span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::ElabConstructorExpectsArgument,
                    vec![ctor_name_for_errors.to_string()],
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
                    vec![ctor_name_for_errors.to_string()],
                ),
            );
        }
        (None, elaboration_environment.clone())
    };

    let pat = Located::new(
        elab::Pattern::Constructor(datatype_kind, pattern_constructor, type_args, arg_pat_opt),
        span.clone(),
    );
    (pat, new_env)
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
    if !ms.is_empty() {
        if let Some((str_id, items)) =
            resolve_module_path(elaboration_context, elaboration_environment, ms, span)
        {
            if let Some((_con_id, dt_id, type_params, arg_type)) = sgi_find_datatype_con(&items, x)
            {
                let datatype_kind = match elaboration_environment.lookup_datatype(dt_id) {
                    Ok(dt_info) => {
                        let specs: Vec<(String, usize, Option<elab::LocatedConstructor>)> = dt_info
                            .constructors_by_id
                            .iter()
                            .map(|(cid, (nm, at))| (nm.clone(), *cid, at.clone()))
                            .collect();
                        crate::elaborated::utilities::classify_datatype(&specs)
                    }
                    Err(_) => crate::datatype_kind::DatatypeKind::Default,
                };
                let pat_con =
                    elab::PatternConstructor::Proj(str_id, ms[1..].to_vec(), x.to_string());
                return elab_pat_con_after_resolve(
                    elaboration_context,
                    elaboration_environment,
                    datatype_kind,
                    pat_con,
                    dt_id,
                    type_params,
                    arg_type.as_ref(),
                    arg_opt,
                    expected_type,
                    x,
                    span,
                );
            }
        } else {
            let pat = Located::new(
                elab::Pattern::Var("_".to_string(), expected_type.clone()),
                span.clone(),
            );
            return (pat, elaboration_environment.clone());
        }
    }

    if let Some(info) = elaboration_environment.lookup_constructor(x).cloned() {
        let pat_con = elab::PatternConstructor::Var(info.constructor_id);
        return elab_pat_con_after_resolve(
            elaboration_context,
            elaboration_environment,
            info.datatype_kind,
            pat_con,
            info.datatype_id,
            &info.type_params,
            info.arg_type.as_ref(),
            arg_opt,
            expected_type,
            x,
            span,
        );
    }

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
            elab::Constructor::Record(Box::new(ktype.clone()), row_fields),
            span.clone(),
        );
        Located::new(
            elab::Constructor::Concat(Box::new(known_row), Box::new(rest)),
            span.clone(),
        )
    } else {
        Located::new(
            elab::Constructor::Record(Box::new(ktype.clone()), row_fields),
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

fn elab_exp_against_type(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    disjointness_environment: &disjoint::DisjointEnv,
    expression: &source::LocExp,
    expected_type: &elab::LocatedConstructor,
) -> (elab::LocatedExpression, elab::LocatedConstructor) {
    use std::cell::Cell;
    thread_local! {
        static ELAB_EXP_AGAINST_TYPE_DEPTH: Cell<usize> = const { Cell::new(0) };
    }
    let against_type_depth = ELAB_EXP_AGAINST_TYPE_DEPTH.with(|cell| {
        let current_depth = cell.get();
        cell.set(current_depth + 1);
        current_depth
    });
    if std::env::var("URWEB_DEBUG_AGAINST_TYPE").ok().as_deref() == Some("1") {
        eprintln!(
            "against_type debug depth={} span={}:{} exp={:?} expected={}",
            against_type_depth,
            expression.span.file,
            expression.span.first.line,
            expression.node,
            crate::elaborated::type_display::format_constructor(expected_type),
        );
    }
    let normalized_expected_type =
        hnorm_con_expression_head(elaboration_environment, expected_type.clone());
    let result = match (&expression.node, &normalized_expected_type.node) {
        (
            source::Exp::CAbs(explicitness, parameter_name, kind, body),
            elab::Constructor::TCFun(expected_explicitness, _, expected_kind, expected_body),
        ) => {
            let elaborated_kind = elab_kind(elaboration_context, elaboration_environment, kind);
            let expected_explicitness_matches =
                elab_explicitness(*explicitness) == *expected_explicitness;
            if !expected_explicitness_matches {
                let (elaborated_expression, inferred_type) = elab_exp(
                    elaboration_context,
                    elaboration_environment,
                    disjointness_environment,
                    expression,
                );
                check_con(
                    elaboration_context,
                    elaboration_environment,
                    &expression.span,
                    &inferred_type,
                    expected_type,
                );
                return (elaborated_expression, inferred_type);
            }
            if let Err(_kind_failure) =
                unify_kinds(elaboration_environment, &elaborated_kind, expected_kind)
            {
                elaboration_context.error(
                    kind.span.clone(),
                    DiagnosticPayload::new(
                        DiagnosticId::ElabKindMismatch,
                        vec![format!(
                            "{} vs {}",
                            crate::elaborated::type_display::format_kind(&elaborated_kind),
                            crate::elaborated::type_display::format_kind(expected_kind),
                        )],
                    ),
                );
                return (
                    elaborated_expression_error_at_span(expression.span.clone()),
                    elaborated_constructor_error_at_span(expression.span.clone()),
                );
            }
            let body_environment = elaboration_environment
                .clone()
                .push_c_rel(parameter_name.clone(), expected_kind.as_ref().clone());
            let body_disjointness_environment = disjoint::enter(disjointness_environment.clone());
            let (body_expression, body_type) = elab_exp_against_type(
                elaboration_context,
                &body_environment,
                &body_disjointness_environment,
                body,
                expected_body,
            );
            let elaborated_expression = Located::new(
                elab::Expression::CAbs(
                    *expected_explicitness,
                    parameter_name.clone(),
                    Box::new(expected_kind.as_ref().clone()),
                    Box::new(body_expression),
                ),
                expression.span.clone(),
            );
            let elaborated_type = Located::new(
                elab::Constructor::TCFun(
                    *expected_explicitness,
                    parameter_name.clone(),
                    Box::new(expected_kind.as_ref().clone()),
                    Box::new(body_type),
                ),
                expression.span.clone(),
            );
            (elaborated_expression, elaborated_type)
        }
        (
            source::Exp::Disjoint(left_row, right_row, body),
            elab::Constructor::TDisjoint(expected_left_row, expected_right_row, expected_body_type),
        ) => {
            let (left_constructor, left_kind) =
                elab_con(elaboration_context, elaboration_environment, left_row);
            let (right_constructor, _right_kind) =
                elab_con(elaboration_context, elaboration_environment, right_row);
            let fresh_row_kind = fresh_kunif(expression.span.clone(), "_dj_elem_check");
            let row_kind = Located::new(
                elab::Kind::Record(Box::new(fresh_row_kind)),
                expression.span.clone(),
            );
            check_kind(
                elaboration_context,
                elaboration_environment,
                &left_row.span,
                &left_constructor,
                &left_kind,
                &row_kind,
            );
            check_con(
                elaboration_context,
                elaboration_environment,
                &left_row.span,
                &left_constructor,
                expected_left_row,
            );
            check_con(
                elaboration_context,
                elaboration_environment,
                &right_row.span,
                &right_constructor,
                expected_right_row,
            );
            let asserted_disjointness_environment = disjoint::assert(
                left_constructor.clone(),
                right_constructor.clone(),
                disjointness_environment.clone(),
            );
            let goals = disjoint::prove(
                expression.span.clone(),
                &asserted_disjointness_environment,
                left_constructor,
                right_constructor,
            );
            if !goals.is_empty() {
                for goal in goals {
                    elaboration_context.constraints.push(Constraint::Disjoint {
                        span: expression.span.clone(),
                        elaboration_environment: elaboration_environment.clone(),
                        goal,
                    });
                }
            }
            elab_exp_against_type(
                elaboration_context,
                elaboration_environment,
                &asserted_disjointness_environment,
                body,
                expected_body_type,
            )
        }
        (source::Exp::Abs(parameter_name, annotation, body), elab::Constructor::TFun(dom, ran)) => {
            let parameter_type = match annotation {
                Some(annotation_constructor) => {
                    let (annotated_type, _) = elab_con(
                        elaboration_context,
                        elaboration_environment,
                        annotation_constructor,
                    );
                    check_con(
                        elaboration_context,
                        elaboration_environment,
                        &annotation_constructor.span,
                        &annotated_type,
                        dom,
                    );
                    annotated_type
                }
                None => dom.as_ref().clone(),
            };
            let body_environment = elaboration_environment
                .clone()
                .push_e_rel(parameter_name.clone(), parameter_type.clone());
            let (body_expression, body_type) = elab_exp_against_type(
                elaboration_context,
                &body_environment,
                disjointness_environment,
                body,
                ran,
            );
            let lambda_expression = Located::new(
                elab::Expression::Abs(
                    parameter_name.clone(),
                    parameter_type.clone(),
                    body_type.clone(),
                    Box::new(body_expression),
                ),
                expression.span.clone(),
            );
            let lambda_type = Located::new(
                elab::Constructor::TFun(Box::new(parameter_type), Box::new(body_type)),
                expression.span.clone(),
            );
            (lambda_expression, lambda_type)
        }
        _ => {
            let (elaborated_expression, inferred_type) = elab_exp(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                expression,
            );
            check_con(
                elaboration_context,
                elaboration_environment,
                &expression.span,
                &inferred_type,
                expected_type,
            );
            (elaborated_expression, inferred_type)
        }
    };
    ELAB_EXP_AGAINST_TYPE_DEPTH.with(|cell| cell.set(against_type_depth));
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

        source::Exp::Var(ms, x, ref inf) => elab_exp_var(
            elaboration_context,
            elaboration_environment,
            disjointness_environment,
            ms,
            x,
            *inf,
            &span,
        ),

        source::Exp::App(f, arg) => {
            // Like `elabExp` / `EApp` in `elaborate.sml`: `elabExp e1` already ran `elabHead` on
            // variables; do not re-run it here. After building `EApp`, optionally `elabHead` again
            // when `findHead` applies (`infer_for_second_elab_head`).
            let (fe, ft) = elab_exp(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                f,
            );
            // Value application needs the expression-head normalizer, not the constructor-app one:
            // this mirrors SML `hnormCon env` at `EApp` sites and keeps `folder r` aliases callable
            // without eagerly rewriting unrelated constructor arguments.
            let ftn = hnorm_con_expression_head(elaboration_environment, ft);
            if std::env::var("URWEB_TEST_SHOW_OPTION_APP_DEBUG")
                .ok()
                .as_deref()
                == Some("1")
                && span.file.ends_with("/lib/ur/top.ur")
                && (76..=80).contains(&span.first.line)
            {
                eprintln!(
                    "show_option app debug span={}:{} f={:?} ft_norm={:?}",
                    span.file, span.first.line, fe, ftn
                );
            }
            if std::env::var("URWEB_DEBUG_TOP_APP_NONFUNCTION")
                .ok()
                .as_deref()
                == Some("1")
                && span.file.ends_with("/lib/ur/top.ur")
                && (181..=230).contains(&span.first.line)
            {
                eprintln!(
                    "top app debug line={} ft={} ft_head={}",
                    span.first.line,
                    crate::elaborated::type_display::format_constructor(&ftn),
                    debug_constructor_head_name(elaboration_environment, &ftn),
                );
            }
            match ftn.node.clone() {
                elab::Constructor::TFun(dom, ran) => {
                    let (ae, _at) = elab_exp_against_type(
                        elaboration_context,
                        elaboration_environment,
                        disjointness_environment,
                        arg,
                        &dom,
                    );
                    let second_infer = infer_for_second_elab_head(f.as_ref(), &fe);
                    let result = Located::new(
                        elab::Expression::App(Box::new(fe), Box::new(ae)),
                        span.clone(),
                    );
                    let (out_e, out_t) = match second_infer {
                        Some(infer) => elab_head(
                            elaboration_context,
                            elaboration_environment,
                            disjointness_environment,
                            result,
                            *ran,
                            &span,
                            infer,
                        ),
                        None => (result, *ran),
                    };
                    (out_e, out_t)
                }
                elab::Constructor::Unif(unif_nesting_level, _, _k, _, r) => {
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
                    // Fresh Unifs start at nl=0, so squish(0, tfun) = tfun.  For lifted Unifs,
                    // squish adjusts the solution to the Unif's creation depth.
                    let tfun_squished =
                        squish_con(unif_nesting_level, tfun).unwrap_or_else(|CantSquish| {
                            // If squish fails (Unif was lifted through binders that tfun references),
                            // store tfun directly as best-effort; a type error will surface later.
                            Located::new(
                                elab::Constructor::TFun(
                                    Box::new(dom.clone()),
                                    Box::new(ran.clone()),
                                ),
                                span.clone(),
                            )
                        });
                    *crate::compiler_diagnostics::lock_for_compile(
                        r.as_ref(),
                        "elaboration unification cell",
                    ) = elab::CUnif::Known(Box::new(tfun_squished));
                    let (ae, _at) = elab_exp_against_type(
                        elaboration_context,
                        elaboration_environment,
                        disjointness_environment,
                        arg,
                        &dom,
                    );
                    let second_infer = infer_for_second_elab_head(f.as_ref(), &fe);
                    let result = Located::new(
                        elab::Expression::App(Box::new(fe), Box::new(ae)),
                        span.clone(),
                    );
                    let (out_e, out_t) = match second_infer {
                        Some(infer) => elab_head(
                            elaboration_context,
                            elaboration_environment,
                            disjointness_environment,
                            result,
                            ran.clone(),
                            &span,
                            infer,
                        ),
                        None => (result, ran),
                    };
                    (out_e, out_t)
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
            if std::env::var("URWEB_DEBUG_CAPP_ALL").ok().as_deref() == Some("1") {
                eprintln!(
                    "capp debug pre span={}:{} head_type={} arg_con={}",
                    span.file,
                    span.first.line,
                    crate::elaborated::type_display::format_constructor(&e1t),
                    crate::elaborated::type_display::format_constructor(&ce),
                );
            }
            // Constructor application needs enough normalization to expose the outer constructor
            // binder, but full-tree abbreviation expansion here can explode higher-order row code
            // like `folder`/`mapU` before we even substitute the argument.
            let e1tn = hnorm_con_expression_head(elaboration_environment, e1t.clone());
            if std::env::var("URWEB_DEBUG_CAPP_ALL").ok().as_deref() == Some("1") {
                eprintln!(
                    "capp debug head span={}:{} norm_head={}",
                    span.file,
                    span.first.line,
                    crate::elaborated::type_display::format_constructor(&e1tn),
                );
            }
            if std::env::var("URWEB_DEBUG_TOP_CAPP").ok().as_deref() == Some("1")
                && span.file.ends_with("/lib/ur/top.ur")
                && (180..=230).contains(&span.first.line)
            {
                eprintln!(
                    "top capp debug line={} head_type={} head_norm={} head_norm_head={}",
                    span.first.line,
                    crate::elaborated::type_display::format_constructor(&e1t),
                    crate::elaborated::type_display::format_constructor(&e1tn),
                    debug_constructor_head_name(elaboration_environment, &e1tn),
                );
            }
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
                    // Clone the constructor body so debug reporting can still inspect the original on failure.
                    let constructor_body = *body.clone();
                    // Substitute the constructor argument through the result body, matching SML constructor application.
                    let result_type = match sub_con_in_con(0, &ce, constructor_body) {
                        Ok(substituted_type) => {
                            if std::env::var("URWEB_DEBUG_CAPP_ALL").ok().as_deref() == Some("1") {
                                eprintln!(
                                    "capp debug sub span={}:{} substituted={}",
                                    span.file,
                                    span.first.line,
                                    crate::elaborated::type_display::format_constructor(
                                        &substituted_type
                                    ),
                                );
                            }
                            hnorm_con_expression_head(elaboration_environment, substituted_type)
                        }
                        Err(_) => {
                            if std::env::var("URWEB_DEBUG_TOP_CAPP").ok().as_deref() == Some("1")
                                && span.file.ends_with("/lib/ur/top.ur")
                                && (180..=230).contains(&span.first.line)
                            {
                                eprintln!(
                                    "top capp debug line={} substitution_hit_subunif arg={} body_head={}",
                                    span.first.line,
                                    crate::elaborated::type_display::format_constructor(&ce),
                                    debug_constructor_head_name(
                                        elaboration_environment,
                                        body.as_ref()
                                    ),
                                );
                            }
                            elaborated_constructor_error_at_span(span.clone())
                        }
                    };
                    let second_infer = infer_for_second_elab_head(e1.as_ref(), &e1e);
                    let result =
                        Located::new(elab::Expression::CApp(Box::new(e1e), ce), span.clone());
                    let (out_e, out_t) = match second_infer {
                        Some(infer) => elab_head(
                            elaboration_context,
                            elaboration_environment,
                            disjointness_environment,
                            result,
                            result_type,
                            &span,
                            infer,
                        ),
                        None => (result, result_type),
                    };
                    (out_e, out_t)
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
            let disjoint_body_type = Located::new(
                elab::Constructor::TDisjoint(
                    Box::new(c1e),
                    Box::new(c2e),
                    Box::new(bodytype),
                ),
                span.clone(),
            );
            (bodye, disjoint_body_type)
        }

        source::Exp::DisjointApp(body) => {
            // `!` postfix (`urweb.grm` `eapps BANG`) and rare bare `@` + atom (non-path) use this;
            // `@v` / `@@v` on names parse as [`Exp::Var`] via [`Token::AtTypesOnlyPath`].
            let (body_e, body_t) = elab_exp(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                body,
            );
            let k1_inner = fresh_kunif(span.clone(), "_dj_elem_1");
            let kind_left_row = Located::new(elab::Kind::Record(Box::new(k1_inner)), span.clone());
            let disjoint_left_row = fresh_cunif(
                elaboration_environment,
                span.clone(),
                kind_left_row,
                "_dj_left",
            );
            let k2_inner = fresh_kunif(span.clone(), "_dj_elem_2");
            let kind_right_row = Located::new(elab::Kind::Record(Box::new(k2_inner)), span.clone());
            let disjoint_right_row = fresh_cunif(
                elaboration_environment,
                span.clone(),
                kind_right_row,
                "_dj_right",
            );
            let inner_type_kind = Located::new(elab::Kind::Type, span.clone());
            let inner_result_type = fresh_cunif(
                elaboration_environment,
                span.clone(),
                inner_type_kind,
                "_dj_result",
            );
            let expected_disjoint = Located::new(
                elab::Constructor::TDisjoint(
                    Box::new(disjoint_left_row.clone()),
                    Box::new(disjoint_right_row.clone()),
                    Box::new(inner_result_type.clone()),
                ),
                span.clone(),
            );
            check_con(
                elaboration_context,
                elaboration_environment,
                &span,
                &body_t,
                &expected_disjoint,
            );
            let disjoint_goals = disjoint::prove(
                span.clone(),
                disjointness_environment,
                disjoint_left_row,
                disjoint_right_row,
            );
            if !disjoint_goals.is_empty() {
                for goal in disjoint_goals {
                    elaboration_context.constraints.push(Constraint::Disjoint {
                        span: span.clone(),
                        elaboration_environment: elaboration_environment.clone(),
                        goal,
                    });
                }
            }
            (body_e, hnorm_con(inner_result_type))
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
            if let source::Exp::Var(ref ms, ref m, vinf) = e1.node {
                if ms.is_empty() {
                    if let source::Con::Name(ref fname) = field_con.node {
                        // Build the full module path: [M, ...field components?]
                        // Check if M is a module in scope
                        if elaboration_environment.lookup_str(m).is_some() {
                            let path: Vec<String> = vec![m.clone()];
                            return elab_exp_var(
                                elaboration_context,
                                elaboration_environment,
                                disjointness_environment,
                                &path,
                                fname,
                                vinf,
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
                            disjointness_environment,
                            &path,
                            fname,
                            vinf,
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
                            Box::new(Located::new(elab::Kind::Type, span.clone())),
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
                            Box::new(Located::new(elab::Kind::Type, span.clone())),
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
                solve_constraints(elaboration_context, &cur_env);
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

/// Mirrors `findHead` in `elaborate.sml`: only some heads get a second `elabHead` after `EApp` / `ECApp`.
fn infer_for_second_elab_head(
    source_head: &source::LocExp,
    elaborated_head: &elab::LocatedExpression,
) -> Option<source::Inference> {
    fn elaborated_is_head_eligible(exp: &elab::LocatedExpression) -> bool {
        match &exp.node {
            elab::Expression::Named(_)
            | elab::Expression::ModProj(_, _, _)
            | elab::Expression::Rel(_) => true,
            elab::Expression::App(inner, _)
            | elab::Expression::CApp(inner, _)
            | elab::Expression::KApp(inner, _) => elaborated_is_head_eligible(inner),
            _ => false,
        }
    }
    fn source_head_inference(exp: &source::LocExp) -> Option<source::Inference> {
        match &exp.node {
            source::Exp::Var(_, _, inference) => Some(*inference),
            source::Exp::App(inner, _)
            | source::Exp::CApp(inner, _)
            | source::Exp::DisjointApp(inner) => source_head_inference(inner),
            _ => None,
        }
    }
    if elaborated_is_head_eligible(elaborated_head) {
        source_head_inference(source_head)
    } else {
        None
    }
}

const DEEP_CONSTRUCTOR_NORMALIZATION_MAX_DEPTH: usize = 128;

fn deep_normalize_constructor(
    elaboration_environment: &Env,
    constructor: elab::LocatedConstructor,
) -> elab::LocatedConstructor {
    deep_normalize_constructor_with_budget(
        elaboration_environment,
        constructor,
        DEEP_CONSTRUCTOR_NORMALIZATION_MAX_DEPTH,
    )
}

fn deep_normalize_constructor_with_budget(
    elaboration_environment: &Env,
    constructor: elab::LocatedConstructor,
    remaining_depth: usize,
) -> elab::LocatedConstructor {
    let normalized_constructor = hnorm_con_expression_head(elaboration_environment, constructor);
    if remaining_depth == 0 {
        return normalized_constructor;
    }
    let next_depth = remaining_depth - 1;
    let span = normalized_constructor.span.clone();
    let rebuilt_constructor = match normalized_constructor.node {
        elab::Constructor::TFun(domain, range) => Located::new(
            elab::Constructor::TFun(
                Box::new(deep_normalize_constructor_with_budget(
                    elaboration_environment,
                    *domain,
                    next_depth,
                )),
                Box::new(deep_normalize_constructor_with_budget(
                    elaboration_environment,
                    *range,
                    next_depth,
                )),
            ),
            span,
        ),
        elab::Constructor::TCFun(explicitness, name, kind, body) => Located::new(
            elab::Constructor::TCFun(
                explicitness,
                name,
                kind,
                Box::new(deep_normalize_constructor_with_budget(
                    elaboration_environment,
                    *body,
                    next_depth,
                )),
            ),
            span,
        ),
        elab::Constructor::TRecord(row) => Located::new(
            elab::Constructor::TRecord(Box::new(deep_normalize_constructor_with_budget(
                elaboration_environment,
                *row,
                next_depth,
            ))),
            span,
        ),
        elab::Constructor::TDisjoint(left, right, body) => Located::new(
            elab::Constructor::TDisjoint(
                Box::new(deep_normalize_constructor_with_budget(
                    elaboration_environment,
                    *left,
                    next_depth,
                )),
                Box::new(deep_normalize_constructor_with_budget(
                    elaboration_environment,
                    *right,
                    next_depth,
                )),
                Box::new(deep_normalize_constructor_with_budget(
                    elaboration_environment,
                    *body,
                    next_depth,
                )),
            ),
            span,
        ),
        elab::Constructor::App(function_constructor, argument_constructor) => Located::new(
            elab::Constructor::App(
                Box::new(deep_normalize_constructor_with_budget(
                    elaboration_environment,
                    *function_constructor,
                    next_depth,
                )),
                Box::new(deep_normalize_constructor_with_budget(
                    elaboration_environment,
                    *argument_constructor,
                    next_depth,
                )),
            ),
            span,
        ),
        elab::Constructor::Abs(name, kind, body) => Located::new(
            elab::Constructor::Abs(
                name,
                kind,
                Box::new(deep_normalize_constructor_with_budget(
                    elaboration_environment,
                    *body,
                    next_depth,
                )),
            ),
            span,
        ),
        elab::Constructor::KAbs(name, body) => Located::new(
            elab::Constructor::KAbs(
                name,
                Box::new(deep_normalize_constructor_with_budget(
                    elaboration_environment,
                    *body,
                    next_depth,
                )),
            ),
            span,
        ),
        elab::Constructor::KApp(function_constructor, kind) => Located::new(
            elab::Constructor::KApp(
                Box::new(deep_normalize_constructor_with_budget(
                    elaboration_environment,
                    *function_constructor,
                    next_depth,
                )),
                kind,
            ),
            span,
        ),
        elab::Constructor::TKFun(name, body) => Located::new(
            elab::Constructor::TKFun(
                name,
                Box::new(deep_normalize_constructor_with_budget(
                    elaboration_environment,
                    *body,
                    next_depth,
                )),
            ),
            span,
        ),
        elab::Constructor::Record(kind, fields) => Located::new(
            elab::Constructor::Record(
                kind,
                fields
                    .into_iter()
                    .map(|(field_name, field_type)| {
                        (
                            deep_normalize_constructor_with_budget(
                                elaboration_environment,
                                field_name,
                                next_depth,
                            ),
                            deep_normalize_constructor_with_budget(
                                elaboration_environment,
                                field_type,
                                next_depth,
                            ),
                        )
                    })
                    .collect(),
            ),
            span,
        ),
        elab::Constructor::Concat(left, right) => Located::new(
            elab::Constructor::Concat(
                Box::new(deep_normalize_constructor_with_budget(
                    elaboration_environment,
                    *left,
                    next_depth,
                )),
                Box::new(deep_normalize_constructor_with_budget(
                    elaboration_environment,
                    *right,
                    next_depth,
                )),
            ),
            span,
        ),
        elab::Constructor::Tuple(items) => Located::new(
            elab::Constructor::Tuple(
                items
                    .into_iter()
                    .map(|item| {
                        deep_normalize_constructor_with_budget(
                            elaboration_environment,
                            item,
                            next_depth,
                        )
                    })
                    .collect(),
            ),
            span,
        ),
        elab::Constructor::Proj(constructor, index) => Located::new(
            elab::Constructor::Proj(
                Box::new(deep_normalize_constructor_with_budget(
                    elaboration_environment,
                    *constructor,
                    next_depth,
                )),
                index,
            ),
            span,
        ),
        other_constructor => Located::new(other_constructor, span),
    };
    hnorm_con_expression_head(elaboration_environment, rebuilt_constructor)
}

fn elab_exp_var(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    disjointness_environment: &disjoint::DisjointEnv,
    ms: &[String],
    x: &str,
    inference: source::Inference,
    span: &Span,
) -> (elab::LocatedExpression, elab::LocatedConstructor) {
    if ms.is_empty() {
        if std::env::var("URWEB_DEBUG_TOP_VAR_LOOKUP").ok().as_deref() == Some("1")
            && span.file.ends_with("/lib/ur/top.ur")
            && (256..=264).contains(&span.first.line)
        {
            eprintln!(
                "top var debug line={} name={} lookup={:?}",
                span.first.line,
                x,
                elaboration_environment.lookup_e(x),
            );
        }
        match elaboration_environment.lookup_e(x) {
            VarLookup::Rel(idx, t) => {
                let e = Located::new(elab::Expression::Rel(idx), span.clone());
                let result = elab_head(
                    elaboration_context,
                    elaboration_environment,
                    disjointness_environment,
                    e,
                    t,
                    span,
                    inference,
                );
                return result;
            }
            VarLookup::Named(id, t) => {
                let e = Located::new(elab::Expression::Named(id), span.clone());
                let result = elab_head(
                    elaboration_context,
                    elaboration_environment,
                    disjointness_environment,
                    e,
                    t,
                    span,
                    inference,
                );
                return result;
            }
            VarLookup::NotBound => {
                // Check if it's a constructor
                if let Some(info) = elaboration_environment.lookup_constructor(x) {
                    let (e, t) = make_con_exp(info, elaboration_environment, span);
                    let result = elab_head(
                        elaboration_context,
                        elaboration_environment,
                        disjointness_environment,
                        e,
                        t,
                        span,
                        inference,
                    );
                    return result;
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
        return elab_head(
            elaboration_context,
            elaboration_environment,
            disjointness_environment,
            e,
            t.clone(),
            span,
            inference,
        );
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
        return elab_head(
            elaboration_context,
            elaboration_environment,
            disjointness_environment,
            e,
            con_type,
            span,
            inference,
        );
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
        elab::Constructor::Record(Box::new(ktype.clone()), row_fields),
        span.clone(),
    );
    let result_type = Located::new(elab::Constructor::TRecord(Box::new(row_con)), span.clone());
    let result = Located::new(elab::Expression::Record(fields), span.clone());
    (result, result_type)
}

// ---------------------------------------------------------------------------
// elab_head: insert implicit arguments
// ---------------------------------------------------------------------------

/// Insert implicit kind/type arguments per `elabHead` / `unravel` in `elaborate.sml`.
///
/// `inference` selects `unravel` (`Infer`), `unravelKind` (`DontInfer`), or the `TypesOnly` subset of `unravel`.
fn elab_head(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    disjointness_environment: &disjoint::DisjointEnv,
    e: elab::LocatedExpression,
    t: elab::LocatedConstructor,
    span: &Span,
    inference: source::Inference,
) -> (elab::LocatedExpression, elab::LocatedConstructor) {
    elab_head_inner(
        elaboration_context,
        elaboration_environment,
        disjointness_environment,
        e,
        t,
        span,
        0,
        inference,
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
    inference: source::Inference,
) -> (elab::LocatedExpression, elab::LocatedConstructor) {
    if std::env::var("URWEB_DEBUG_ELAB_HEAD").ok().as_deref() == Some("1") && depth >= 8 {
        eprintln!(
            "elab_head debug depth={} span={}:{} expr={:?} type={}",
            depth,
            span.file,
            span.first.line,
            e.node,
            crate::elaborated::type_display::format_constructor(&t),
        );
    }
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
    // Match SML `unravel`/`unravelKind`: normalize with the elaboration environment
    // so named constructor aliases on the head reduce before we decide whether
    // more implicit kind/type arguments are available.
    let tn = hnorm_con_expression_head(elaboration_environment, t.clone());
    match (&tn.node, inference) {
        (elab::Constructor::TKFun(x, body), _) => {
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
                inference,
            )
        }
        (_, source::Inference::DontInfer) => (e, tn),
        (
            elab::Constructor::TCFun(elab::Explicitness::Implicit, x, k, body),
            source::Inference::Infer | source::Inference::TypesOnly,
        ) => {
            let cu = fresh_cunif(elaboration_environment, span.clone(), *k.clone(), x);
            let body_subst = match sub_con_in_con(0, &cu, *body.clone()) {
                Ok(substituted) => substituted,
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
                inference,
            )
        }
        (elab::Constructor::TDisjoint(_, _, _), source::Inference::TypesOnly) => (e, t),
        (elab::Constructor::TDisjoint(c1, c2, body), source::Inference::Infer) => {
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
                inference,
            )
        }
        (elab::Constructor::TFun(dom, _), source::Inference::TypesOnly)
            if is_class_or_folder(elaboration_environment, dom) =>
        {
            (e, t)
        }
        (elab::Constructor::TFun(dom, ran), _)
            if is_class_or_folder(elaboration_environment, dom)
                && !matches!(inference, source::Inference::TypesOnly) =>
        {
            if std::env::var("URWEB_DEBUG_TYPECLASS_INSERT")
                .ok()
                .as_deref()
                == Some("1")
            {
                eprintln!(
                    "typeclass insert debug span={}:{} expr={:?} dom={} dom_head={} ran={}",
                    span.file,
                    span.first.line,
                    e.node,
                    crate::elaborated::type_display::format_constructor(dom),
                    debug_constructor_head_name(elaboration_environment, dom),
                    crate::elaborated::type_display::format_constructor(ran),
                );
            }
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
            elab_head_inner(
                elaboration_context,
                elaboration_environment,
                disjointness_environment,
                new_e,
                *ran.clone(),
                span,
                depth + 1,
                inference,
            )
        }
        (elab::Constructor::Named(id), source::Inference::Infer | source::Inference::TypesOnly) => {
            if let Ok((_, _, Some(def))) = elaboration_environment.lookup_c_named(*id) {
                elab_head_inner(
                    elaboration_context,
                    elaboration_environment,
                    disjointness_environment,
                    e,
                    def.clone(),
                    span,
                    depth + 1,
                    inference,
                )
            } else {
                (e, t)
            }
        }
        (
            elab::Constructor::App(f, arg),
            source::Inference::Infer | source::Inference::TypesOnly,
        ) => {
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
                            inference,
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
        _ => (e, tn),
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

            solve_constraints(elaboration_context, &pre_env);
            let mut normalized_env = elaboration_environment.clone();
            let mut normalized_bindings: Vec<(
                String,
                elab::LocatedConstructor,
                elab::LocatedExpression,
            )> = Vec::with_capacity(elab_bindings.len());
            for (name, binding_type, expression) in elab_bindings {
                let normalized_type = hnorm_con_expression_head(&pre_env, binding_type);
                normalized_env = normalized_env.push_e_rel(name.clone(), normalized_type.clone());
                normalized_bindings.push((name, normalized_type, expression));
            }
            let decl = Located::new(
                elab::ElaboratedDeclaration::ValRec(normalized_bindings),
                span,
            );
            (Some(decl), normalized_env)
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
            let ke = normalize_signature_kind(&elab_kind(
                elaboration_context,
                elaboration_environment,
                k,
            ));
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
            let stored_kind = normalize_signature_kind(&ke);
            let stored_constructor = normalize_signature_constructor(&ce);
            let (new_env, id) = elaboration_environment.clone().push_c_named(
                x.clone(),
                stored_kind.clone(),
                Some(stored_constructor.clone()),
            );
            let result = Located::new(
                elab::SignatureItem::Constructor(x.clone(), id, stored_kind, stored_constructor),
                span,
            );
            (Some(result), new_env)
        }
        source::SgnItem::Val(x, t) => {
            let (te, _) = elab_con(elaboration_context, elaboration_environment, t);
            let stored_type = normalize_signature_constructor(&te);
            let (new_env, id) = elaboration_environment
                .clone()
                .push_e_named(x.clone(), stored_type.clone());
            let result = Located::new(elab::SignatureItem::Val(x.clone(), id, stored_type), span);
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
            let ke = normalize_signature_kind(&elab_kind(
                elaboration_context,
                elaboration_environment,
                k,
            )); // parameter kind (`Type` for bare `class nm`)
            let (mut new_env, id) =
                elaboration_environment
                    .clone()
                    .push_c_named(x.clone(), ke.clone(), None); // store parameter kind; see elab_con_var Named + is_class
            new_env = new_env.push_class(id);
            let result = Located::new(elab::SignatureItem::ClassAbs(x.clone(), id, ke), span);
            (Some(result), new_env)
        }
        source::SgnItem::Class(x, k, c) => {
            let ke = normalize_signature_kind(&elab_kind(
                elaboration_context,
                elaboration_environment,
                k,
            ));
            let (ce, _) = elab_con(elaboration_context, elaboration_environment, c);
            let stored_constructor = normalize_signature_constructor(&ce);
            let (mut new_env, id) = elaboration_environment.clone().push_c_named(
                x.clone(),
                ke.clone(),
                Some(stored_constructor.clone()),
            );
            new_env = new_env.push_class(id);
            let result = Located::new(
                elab::SignatureItem::Class(x.clone(), id, ke, stored_constructor),
                span,
            );
            (Some(result), new_env)
        }
        source::SgnItem::Table(x, c, _pk_e, _unique_e) => {
            // Table in signature: like Val
            let (ce, _) = elab_con(elaboration_context, elaboration_environment, c);
            let stored_type = normalize_signature_constructor(&ce);
            let (new_env, id) = elaboration_environment
                .clone()
                .push_e_named(x.clone(), stored_type.clone());
            let result = Located::new(elab::SignatureItem::Val(x.clone(), id, stored_type), span);
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
                params: dt.params.clone(),
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
            let actual_items_environment = sgis1
                .iter()
                .fold(elaboration_environment.clone(), |current_env, sgi| {
                    enrich_env_from_sgi(current_env, &sgi.node, 0usize, &[], "")
                });
            let realization_map = build_signature_realization_map(sgis1, sgis2, span);
            // For each item in sgis2 (the expected/spec), find it in sgis1
            for sgi2 in sgis2 {
                debug_trace_top_sgn_item(&sgi2.node, span);
                sub_sgi(
                    elaboration_context,
                    &actual_items_environment,
                    disjointness_environment,
                    sgis1,
                    &realization_map,
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

fn debug_trace_constructor_signature_item(name: &str) -> bool {
    matches!(
        name,
        "folder" | "mapU" | "foldUR2" | "mapUX2" | "mapX2" | "mapX3" | "mapX4" | "mapUX_rev"
    )
}

fn debug_trace_top_subsgi_item_name(name: &str, span: &Span) {
    if std::env::var("URWEB_DEBUG_TOP_SUBSGI_NAMES")
        .ok()
        .as_deref()
        != Some("1")
    {
        return;
    }
    let log_index = DEBUG_TOP_SUBSGI_LOG_COUNT.fetch_add(1, Ordering::Relaxed);
    if log_index < 200usize {
        eprintln!(
            "top subsgi item {} span={}:{}",
            name, span.file, span.first.line,
        );
    }
}

fn debug_trace_top_sgn_item(expected: &elab::SignatureItem, span: &Span) {
    let debug_mode = std::env::var("URWEB_DEBUG_TOP_SGN_ITEMS").ok();
    let Some(debug_mode) = debug_mode.as_deref() else {
        return;
    };
    let log_index = DEBUG_TOP_SUBSGI_LOG_COUNT.fetch_add(1, Ordering::Relaxed);
    if log_index >= 200usize {
        return;
    }
    let label = match expected {
        elab::SignatureItem::Val(name, _, _) => format!("Val {name}"),
        elab::SignatureItem::ConAbs(name, _, _) => format!("ConAbs {name}"),
        elab::SignatureItem::Constructor(name, _, _, _) => format!("Constructor {name}"),
        elab::SignatureItem::Structure(_, name, _, _) => format!("Structure {name}"),
        elab::SignatureItem::ClassAbs(name, _, _) => format!("ClassAbs {name}"),
        elab::SignatureItem::Class(name, _, _, _) => format!("Class {name}"),
        elab::SignatureItem::Datatype(_) => "Datatype".to_string(),
        elab::SignatureItem::DatatypeImp { name, .. } => format!("DatatypeImp {name}"),
        elab::SignatureItem::Signature(name, _, _) => format!("Signature {name}"),
        elab::SignatureItem::Constraint(_, _) => "Constraint".to_string(),
    };
    eprintln!(
        "top sgn item {} span={}:{}",
        label, span.file, span.first.line,
    );
    if debug_mode == "panic" {
        panic!("debug top signature item");
    }
}

fn sub_sgi(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    disjointness_environment: &disjoint::DisjointEnv,
    actual_sgis: &[elab::LocatedSignatureItem],
    realization_map: &HashMap<usize, elab::LocatedConstructor>,
    expected: &elab::SignatureItem,
    span: &Span,
) {
    match expected {
        elab::SignatureItem::Val(x, _, t2) => {
            if let Some(sgi1) = sgi_find_val(actual_sgis, x) {
                if let elab::SignatureItem::Val(_, _, t1) = sgi1 {
                    let realized_expected_type =
                        realize_signature_constructor_named_ids(t2, realization_map);
                    check_con(
                        elaboration_context,
                        elaboration_environment,
                        span,
                        t1,
                        &realized_expected_type,
                    );
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
            debug_trace_top_subsgi_item_name(x, span);
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
            debug_trace_top_subsgi_item_name(x, span);
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
                        let realized_expected_constructor =
                            realize_signature_constructor_named_ids(c2, realization_map);
                        if std::env::var("URWEB_DEBUG_TOP_CON_SUBSGI").ok().as_deref() == Some("1")
                            && debug_trace_constructor_signature_item(x)
                        {
                            eprintln!(
                                "top subsgi con {} span={}:{} actual={} expected={} actual_kind={} expected_kind={}",
                                x,
                                span.file,
                                span.first.line,
                                crate::elaborated::type_display::format_constructor(c1),
                                crate::elaborated::type_display::format_constructor(
                                    &realized_expected_constructor
                                ),
                                crate::elaborated::type_display::format_kind(k1),
                                crate::elaborated::type_display::format_kind(k2),
                            );
                        }
                        if std::env::var("URWEB_DEBUG_LOCALMAP_SUBSGI").ok().as_deref() == Some("1")
                            && (x == "localMap" || x == "localRow" || x == "mapU")
                        {
                            eprintln!(
                                "subsgi con {} span={}:{} actual={} expected={} actual_kind={} expected_kind={}",
                                x,
                                span.file,
                                span.first.line,
                                crate::elaborated::type_display::format_constructor(c1),
                                crate::elaborated::type_display::format_constructor(&realized_expected_constructor),
                                crate::elaborated::type_display::format_kind(k1),
                                crate::elaborated::type_display::format_kind(k2),
                            );
                        }
                        check_con(
                            elaboration_context,
                            elaboration_environment,
                            span,
                            c1,
                            &realized_expected_constructor,
                        );
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
                    let realized_expected_signature =
                        realize_signature_named_ids(sgn2, realization_map);
                    sub_sgn(
                        elaboration_context,
                        elaboration_environment,
                        disjointness_environment,
                        sgn1,
                        &realized_expected_signature,
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
            let stored_kind = normalize_signature_kind(&ke);
            let stored_constructor = normalize_signature_constructor(&ce);
            if std::env::var("URWEB_DEBUG_MAPU_CON").ok().as_deref() == Some("1")
                && (x == "mapU" || x == "localMap" || x == "localRow")
            {
                eprintln!(
                    "mapu con decl {} span={}:{} constructor={} inferred_kind={} stored_kind={}",
                    x,
                    span.file,
                    span.first.line,
                    crate::elaborated::type_display::format_constructor(&stored_constructor),
                    crate::elaborated::type_display::format_kind(&ck),
                    crate::elaborated::type_display::format_kind(&stored_kind),
                );
            }
            let (new_env, id) = elaboration_environment.clone().push_c_named(
                x.clone(),
                stored_kind.clone(),
                Some(stored_constructor.clone()),
            );
            let decl_out = Located::new(
                elab::Declaration::Constructor(x.clone(), id, stored_kind, stored_constructor),
                span,
            );
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
                    params,
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
                            params,
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
            let mut value_env = new_env;
            collect_val_decls(&pate, &ee, &et, &span, &mut decls, &mut value_env);
            // Solve constraints
            solve_constraints(elaboration_context, &value_env);
            let mut normalized_env = elaboration_environment.clone();
            let mut normalized_decls: Vec<elab::LocatedDeclaration> =
                Vec::with_capacity(decls.len());
            for declaration in decls {
                match declaration.node {
                    elab::Declaration::Val(name, id, typ, expression) => {
                        let normalized_type = deep_normalize_constructor(&value_env, typ);
                        normalized_env = normalized_env.push_e_named_as(
                            name.clone(),
                            id,
                            normalized_type.clone(),
                        );
                        normalized_decls.push(Located::new(
                            elab::Declaration::Val(name, id, normalized_type, expression),
                            declaration.span,
                        ));
                    }
                    other_declaration => {
                        normalized_decls.push(Located::new(other_declaration, declaration.span));
                    }
                }
            }
            (
                normalized_decls,
                normalized_env,
                disjointness_environment.clone(),
            )
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
            let mut normalized_env = pre_env.clone();
            let mut normalized_recs: Vec<(
                String,
                usize,
                elab::LocatedConstructor,
                elab::LocatedExpression,
            )> = Vec::with_capacity(elab_recs.len());
            for (name, id, declared_type, expression) in elab_recs {
                let normalized_type = deep_normalize_constructor(&pre_env, declared_type);
                normalized_env =
                    normalized_env.push_e_named_as(name.clone(), id, normalized_type.clone());
                normalized_recs.push((name, id, normalized_type, expression));
            }
            let decl_out = Located::new(elab::Declaration::ValRec(normalized_recs), span);
            (
                vec![decl_out],
                normalized_env,
                disjointness_environment.clone(),
            )
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
            let dummy_span = Span::dummy();
            let mut cur_env = elaboration_environment;
            for dt in dts {
                cur_env = cur_env.push_datatype(dt.id, dt.params.clone(), dt.constrs.clone());
                let ktype = Located::new(elab::Kind::Type, dummy_span.clone());
                let dt_kind = dt.params.iter().fold(ktype.clone(), |acc, _| {
                    Located::new(
                        elab::Kind::Arrow(Box::new(ktype.clone()), Box::new(acc)),
                        dummy_span.clone(),
                    )
                });
                cur_env = cur_env.push_c_named_as(dt.name.clone(), dt.id, dt_kind, None);
                for (con_name, con_id, arg_type) in &dt.constrs {
                    let expression_type = crate::elaborated::environment::build_constructor_type(
                        dt.id,
                        &dt.params,
                        arg_type.as_ref(),
                        dummy_span.clone(),
                    );
                    cur_env = cur_env.push_e_named_as(con_name.clone(), *con_id, expression_type);
                }
            }
            cur_env
        }
        elab::SignatureItem::DatatypeImp {
            name,
            id,
            params,
            orig_mod,
            orig_path,
            orig_name,
            orig_constrs_path: _,
            constrs,
        } => {
            let dummy_span = Span::dummy();
            let kind_type = Located::new(elab::Kind::Type, dummy_span.clone());
            let datatype_kind = params
                .iter()
                .fold(kind_type.clone(), |accumulated_kind, _| {
                    Located::new(
                        elab::Kind::Arrow(Box::new(kind_type.clone()), Box::new(accumulated_kind)),
                        dummy_span.clone(),
                    )
                });
            let definition = Located::new(
                elab::Constructor::ModProj(*orig_mod, orig_path.clone(), orig_name.clone()),
                dummy_span.clone(),
            );
            let mut cur_env = elaboration_environment.push_c_named_as(
                name.clone(),
                *id,
                datatype_kind,
                Some(definition),
            );
            cur_env = cur_env.push_datatype(*id, params.clone(), constrs.clone());
            for (con_name, con_id, arg_type) in constrs {
                let expression_type = crate::elaborated::environment::build_constructor_type(
                    *id,
                    params,
                    arg_type.as_ref(),
                    dummy_span.clone(),
                );
                cur_env = cur_env.push_e_named_as(con_name.clone(), *con_id, expression_type);
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

fn build_ascription_environment(
    base_environment: &Env,
    ascribed_signature: Option<&elab::LocatedSignature>,
) -> Env {
    match ascribed_signature {
        Some(signature) => {
            let normalized_signature = hnorm_sgn(base_environment, signature);
            let items = get_sgn_const_items(base_environment, &normalized_signature);
            items
                .iter()
                .fold(base_environment.clone(), |current_env, sgi| {
                    enrich_env_from_sgi(current_env, &sgi.node, 0, &[], "")
                })
        }
        None => base_environment.clone(),
    }
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
                // Keep deferred elaboration constraints declaration-local inside structures,
                // matching the SML pipeline more closely and preventing earlier helpers from
                // leaking unresolved state into later declarations like `rev` / `queryL`.
                solve_constraints(elaboration_context, &cur_env);
                elab_decls.extend(ds);
            }
            // Build signature from the declarations
            let sgn = decls_to_sgn(&elab_decls, &span);
            // Check ascription
            if let Some(asc) = ascribed {
                let ascription_environment = build_ascription_environment(&cur_env, ascribed);
                sub_sgn(
                    elaboration_context,
                    &ascription_environment,
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
                    let ascription_environment =
                        build_ascription_environment(elaboration_environment, ascribed);
                    sub_sgn(
                        elaboration_context,
                        &ascription_environment,
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
fn normalize_signature_kind(kind: &elab::LocatedKind) -> elab::LocatedKind {
    let normalized_kind = hnorm_kind(kind.clone());
    let span = normalized_kind.span.clone();
    match normalized_kind.node {
        elab::Kind::Arrow(domain, range) => Located::new(
            elab::Kind::Arrow(
                Box::new(normalize_signature_kind(&domain)),
                Box::new(normalize_signature_kind(&range)),
            ),
            span,
        ),
        elab::Kind::Record(inner) => Located::new(
            elab::Kind::Record(Box::new(normalize_signature_kind(&inner))),
            span,
        ),
        elab::Kind::Tuple(items) => Located::new(
            elab::Kind::Tuple(items.iter().map(normalize_signature_kind).collect()),
            span,
        ),
        elab::Kind::Fun(name, body) => Located::new(
            elab::Kind::Fun(name, Box::new(normalize_signature_kind(&body))),
            span,
        ),
        other => Located::new(other, span),
    }
}

fn normalize_signature_constructor(
    constructor: &elab::LocatedConstructor,
) -> elab::LocatedConstructor {
    let normalized_constructor = hnorm_con(constructor.clone());
    let span = normalized_constructor.span.clone();
    match normalized_constructor.node {
        elab::Constructor::TFun(domain, range) => Located::new(
            elab::Constructor::TFun(
                Box::new(normalize_signature_constructor(&domain)),
                Box::new(normalize_signature_constructor(&range)),
            ),
            span,
        ),
        elab::Constructor::TCFun(explicitness, name, kind, body) => Located::new(
            elab::Constructor::TCFun(
                explicitness,
                name,
                Box::new(normalize_signature_kind(&kind)),
                Box::new(normalize_signature_constructor(&body)),
            ),
            span,
        ),
        elab::Constructor::TRecord(row) => Located::new(
            elab::Constructor::TRecord(Box::new(normalize_signature_constructor(&row))),
            span,
        ),
        elab::Constructor::TDisjoint(left, right, body) => Located::new(
            elab::Constructor::TDisjoint(
                Box::new(normalize_signature_constructor(&left)),
                Box::new(normalize_signature_constructor(&right)),
                Box::new(normalize_signature_constructor(&body)),
            ),
            span,
        ),
        elab::Constructor::App(function_constructor, argument_constructor) => Located::new(
            elab::Constructor::App(
                Box::new(normalize_signature_constructor(&function_constructor)),
                Box::new(normalize_signature_constructor(&argument_constructor)),
            ),
            span,
        ),
        elab::Constructor::Abs(name, kind, body) => Located::new(
            elab::Constructor::Abs(
                name,
                Box::new(normalize_signature_kind(&kind)),
                Box::new(normalize_signature_constructor(&body)),
            ),
            span,
        ),
        elab::Constructor::KAbs(name, body) => Located::new(
            elab::Constructor::KAbs(name, Box::new(normalize_signature_constructor(&body))),
            span,
        ),
        elab::Constructor::KApp(function_constructor, kind_argument) => Located::new(
            elab::Constructor::KApp(
                Box::new(normalize_signature_constructor(&function_constructor)),
                Box::new(normalize_signature_kind(&kind_argument)),
            ),
            span,
        ),
        elab::Constructor::TKFun(name, body) => Located::new(
            elab::Constructor::TKFun(name, Box::new(normalize_signature_constructor(&body))),
            span,
        ),
        elab::Constructor::Record(row_kind, fields) => Located::new(
            elab::Constructor::Record(
                Box::new(normalize_signature_kind(&row_kind)),
                fields
                    .iter()
                    .map(|(field_name, field_type)| {
                        (
                            normalize_signature_constructor(field_name),
                            normalize_signature_constructor(field_type),
                        )
                    })
                    .collect(),
            ),
            span,
        ),
        elab::Constructor::Concat(left, right) => Located::new(
            elab::Constructor::Concat(
                Box::new(normalize_signature_constructor(&left)),
                Box::new(normalize_signature_constructor(&right)),
            ),
            span,
        ),
        elab::Constructor::Map(left_kind, right_kind) => Located::new(
            elab::Constructor::Map(
                Box::new(normalize_signature_kind(&left_kind)),
                Box::new(normalize_signature_kind(&right_kind)),
            ),
            span,
        ),
        elab::Constructor::Tuple(items) => Located::new(
            elab::Constructor::Tuple(items.iter().map(normalize_signature_constructor).collect()),
            span,
        ),
        elab::Constructor::Proj(base, index) => Located::new(
            elab::Constructor::Proj(Box::new(normalize_signature_constructor(&base)), index),
            span,
        ),
        other => Located::new(other, span),
    }
}

fn signature_kinds_eq(left_kind: &elab::LocatedKind, right_kind: &elab::LocatedKind) -> bool {
    match (&left_kind.node, &right_kind.node) {
        (elab::Kind::Rel(left_index), elab::Kind::Rel(right_index)) => left_index == right_index,
        (elab::Kind::Type, elab::Kind::Type) => true,
        (elab::Kind::Name, elab::Kind::Name) => true,
        (elab::Kind::Unit, elab::Kind::Unit) => true,
        (elab::Kind::Error, elab::Kind::Error) => true,
        (elab::Kind::Record(left_inner), elab::Kind::Record(right_inner)) => {
            signature_kinds_eq(left_inner, right_inner)
        }
        (
            elab::Kind::Arrow(left_domain, left_range),
            elab::Kind::Arrow(right_domain, right_range),
        ) => {
            signature_kinds_eq(left_domain, right_domain)
                && signature_kinds_eq(left_range, right_range)
        }
        (elab::Kind::Tuple(left_items), elab::Kind::Tuple(right_items)) => {
            left_items.len() == right_items.len()
                && left_items
                    .iter()
                    .zip(right_items.iter())
                    .all(|(left_item, right_item)| signature_kinds_eq(left_item, right_item))
        }
        (elab::Kind::Fun(_, left_body), elab::Kind::Fun(_, right_body)) => {
            signature_kinds_eq(left_body, right_body)
        }
        (elab::Kind::Unif(_, _, left_cell), elab::Kind::Unif(_, _, right_cell))
        | (elab::Kind::TupleUnif(_, _, left_cell), elab::Kind::TupleUnif(_, _, right_cell)) => {
            Arc::ptr_eq(left_cell, right_cell)
        }
        _ => false,
    }
}

fn signature_constructors_eq(
    left_constructor: &elab::LocatedConstructor,
    right_constructor: &elab::LocatedConstructor,
) -> bool {
    match (&left_constructor.node, &right_constructor.node) {
        (elab::Constructor::Rel(left_index), elab::Constructor::Rel(right_index)) => {
            left_index == right_index
        }
        (elab::Constructor::Named(left_id), elab::Constructor::Named(right_id)) => {
            left_id == right_id
        }
        (
            elab::Constructor::ModProj(left_root, left_path, left_name),
            elab::Constructor::ModProj(right_root, right_path, right_name),
        ) => left_root == right_root && left_path == right_path && left_name == right_name,
        (
            elab::Constructor::TFun(left_domain, left_range),
            elab::Constructor::TFun(right_domain, right_range),
        ) => {
            signature_constructors_eq(left_domain, right_domain)
                && signature_constructors_eq(left_range, right_range)
        }
        (
            elab::Constructor::TCFun(left_explicitness, _, left_kind, left_body),
            elab::Constructor::TCFun(right_explicitness, _, right_kind, right_body),
        ) => {
            left_explicitness == right_explicitness
                && signature_kinds_eq(left_kind, right_kind)
                && signature_constructors_eq(left_body, right_body)
        }
        (elab::Constructor::TRecord(left_row), elab::Constructor::TRecord(right_row)) => {
            signature_constructors_eq(left_row, right_row)
        }
        (
            elab::Constructor::TDisjoint(left_a, left_b, left_body),
            elab::Constructor::TDisjoint(right_a, right_b, right_body),
        ) => {
            signature_constructors_eq(left_a, right_a)
                && signature_constructors_eq(left_b, right_b)
                && signature_constructors_eq(left_body, right_body)
        }
        (
            elab::Constructor::App(left_functor, left_argument),
            elab::Constructor::App(right_functor, right_argument),
        ) => {
            signature_constructors_eq(left_functor, right_functor)
                && signature_constructors_eq(left_argument, right_argument)
        }
        (
            elab::Constructor::Abs(_, left_kind, left_body),
            elab::Constructor::Abs(_, right_kind, right_body),
        ) => {
            signature_kinds_eq(left_kind, right_kind)
                && signature_constructors_eq(left_body, right_body)
        }
        (elab::Constructor::KAbs(_, left_body), elab::Constructor::KAbs(_, right_body))
        | (elab::Constructor::TKFun(_, left_body), elab::Constructor::TKFun(_, right_body)) => {
            signature_constructors_eq(left_body, right_body)
        }
        (
            elab::Constructor::KApp(left_functor, left_kind),
            elab::Constructor::KApp(right_functor, right_kind),
        ) => {
            signature_constructors_eq(left_functor, right_functor)
                && signature_kinds_eq(left_kind, right_kind)
        }
        (
            elab::Constructor::Record(left_kind, left_fields),
            elab::Constructor::Record(right_kind, right_fields),
        ) => {
            signature_kinds_eq(left_kind, right_kind)
                && left_fields.len() == right_fields.len()
                && left_fields.iter().zip(right_fields.iter()).all(
                    |((left_name, left_type), (right_name, right_type))| {
                        signature_constructors_eq(left_name, right_name)
                            && signature_constructors_eq(left_type, right_type)
                    },
                )
        }
        (
            elab::Constructor::Concat(left_row, left_rest),
            elab::Constructor::Concat(right_row, right_rest),
        ) => {
            signature_constructors_eq(left_row, right_row)
                && signature_constructors_eq(left_rest, right_rest)
        }
        (
            elab::Constructor::Map(left_domain, left_range),
            elab::Constructor::Map(right_domain, right_range),
        ) => {
            signature_kinds_eq(left_domain, right_domain)
                && signature_kinds_eq(left_range, right_range)
        }
        (elab::Constructor::Tuple(left_items), elab::Constructor::Tuple(right_items)) => {
            left_items.len() == right_items.len()
                && left_items
                    .iter()
                    .zip(right_items.iter())
                    .all(|(left_item, right_item)| signature_constructors_eq(left_item, right_item))
        }
        (
            elab::Constructor::Proj(left_base, left_index),
            elab::Constructor::Proj(right_base, right_index),
        ) => left_index == right_index && signature_constructors_eq(left_base, right_base),
        (elab::Constructor::Name(left_name), elab::Constructor::Name(right_name)) => {
            left_name == right_name
        }
        (elab::Constructor::Unit, elab::Constructor::Unit) => true,
        (elab::Constructor::Error, elab::Constructor::Error) => true,
        (
            elab::Constructor::Unif(_, _, left_kind, _, left_cell),
            elab::Constructor::Unif(_, _, right_kind, _, right_cell),
        ) => Arc::ptr_eq(left_cell, right_cell) && signature_kinds_eq(left_kind, right_kind),
        _ => false,
    }
}

fn decls_to_sgn(decls: &[elab::LocatedDeclaration], span: &Span) -> elab::LocatedSignature {
    let mut sgis: Vec<elab::LocatedSignatureItem> = Vec::new();
    for d in decls {
        match &d.node {
            elab::Declaration::Constructor(x, id, k, c) => {
                sgis.push(Located::new(
                    elab::SignatureItem::Constructor(
                        x.clone(),
                        *id,
                        normalize_signature_kind(k),
                        normalize_signature_constructor(c),
                    ),
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
                params,
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
                        params: params.clone(),
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
                    elab::SignatureItem::Val(x.clone(), *id, normalize_signature_constructor(t)),
                    d.span.clone(),
                ));
            }
            elab::Declaration::ValRec(bindings) => {
                for (x, id, t, _) in bindings {
                    sgis.push(Located::new(
                        elab::SignatureItem::Val(
                            x.clone(),
                            *id,
                            normalize_signature_constructor(t),
                        ),
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
                    elab::SignatureItem::Constraint(
                        normalize_signature_constructor(c1),
                        normalize_signature_constructor(c2),
                    ),
                    d.span.clone(),
                ));
            }
            elab::Declaration::Ffi(x, id, _, t) => {
                sgis.push(Located::new(
                    elab::SignatureItem::Val(x.clone(), *id, normalize_signature_constructor(t)),
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

const CONSTRAINT_SOLVE_MAX_PASSES: usize = 8;

fn solve_constraints(elaboration_context: &mut ElabCtx, elaboration_environment: &Env) {
    let mut pending_constraints = std::mem::take(&mut elaboration_context.constraints);
    let mut remaining = Vec::new();

    for _pass_index in 0..CONSTRAINT_SOLVE_MAX_PASSES {
        if pending_constraints.is_empty() {
            break;
        }
        let mut next_pending = Vec::new();
        let mut made_progress = false;
        for c in pending_constraints {
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
                    if goals.is_empty() {
                        made_progress = true;
                    } else {
                        for g in goals {
                            next_pending.push(Constraint::Disjoint {
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
                } => match resolve_class(&c_env, &class, &span) {
                    Some((witness, matched_head)) => {
                        let _ =
                            unify_cons(elaboration_context, &c_env, &span, &class, &matched_head);
                        *crate::compiler_diagnostics::lock_for_compile(
                            result.as_ref(),
                            "elaboration unification cell",
                        ) = Some(witness);
                        made_progress = true;
                    }
                    None => {
                        next_pending.push(Constraint::TypeClass {
                            span: span.clone(),
                            elaboration_environment: c_env,
                            class,
                            result,
                        });
                    }
                },
                Constraint::RowUnification {
                    span,
                    elaboration_environment: c_env,
                    left_constructor,
                    right_constructor,
                } => {
                    let retry_result = unify_rows(
                        elaboration_context,
                        &c_env,
                        &span,
                        &left_constructor,
                        &right_constructor,
                        0,
                    );
                    if retry_result.is_ok() {
                        made_progress = true;
                    } else {
                        let map_result = guess_map(
                            elaboration_context,
                            &c_env,
                            &span,
                            &left_constructor,
                            &right_constructor,
                            0,
                        );
                        match map_result {
                            Ok(()) => {
                                made_progress = true;
                            }
                            Err(_) => {
                                next_pending.push(Constraint::RowUnification {
                                    span,
                                    elaboration_environment: c_env,
                                    left_constructor,
                                    right_constructor,
                                });
                            }
                        }
                    }
                }
            }
        }
        if next_pending.is_empty() {
            pending_constraints = next_pending;
            break;
        }
        if !made_progress {
            remaining = next_pending;
            pending_constraints = Vec::new();
            break;
        }
        pending_constraints = next_pending;
    }
    if remaining.is_empty() {
        remaining = pending_constraints;
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
                if std::env::var("URWEB_DEBUG_UNRESOLVED_CLASS")
                    .ok()
                    .as_deref()
                    == Some("1")
                {
                    eprintln!(
                        "unresolved class debug span={}:{} class={} head_info={}",
                        span.file,
                        span.first.line,
                        crate::elaborated::type_display::format_constructor(&class),
                        debug_constructor_head_name(elaboration_environment, &class),
                    );
                }
                elaboration_context.error(
                    span,
                    DiagnosticPayload::new(
                        DiagnosticId::ElabUnresolvedTypeclass,
                        vec![crate::elaborated::type_display::format_constructor(&class)],
                    ),
                );
            }
            Constraint::RowUnification {
                span,
                left_constructor,
                right_constructor,
                ..
            } => {
                // The deferred row constraint could not be resolved even after the full body
                // was elaborated. Report it as a type mismatch so the user sees a concrete error.
                elaboration_context.error(
                    span,
                    DiagnosticPayload::new(
                        DiagnosticId::ElabTypeMismatch,
                        vec![format!(
                            "incompatible types: {} vs {}",
                            crate::elaborated::type_display::format_constructor(&left_constructor),
                            crate::elaborated::type_display::format_constructor(&right_constructor),
                        )],
                    ),
                );
            }
        }
    }
}

/// Instantiate a rule head/hyps by substituting fresh unification variables for each quantifier.
/// Returns (instantiated_head, instantiated_hyps).
fn instantiate_rule(
    _elaboration_environment: &Env,
    quantifier_kinds: &[elab::LocatedKind],
    hyps: &[elab::LocatedConstructor],
    head: &elab::LocatedConstructor,
    span: &Span,
) -> (elab::LocatedConstructor, Vec<elab::LocatedConstructor>) {
    if quantifier_kinds.is_empty() {
        return (head.clone(), hyps.to_vec());
    }
    let mut inst_head = head.clone();
    let mut inst_hyps: Vec<elab::LocatedConstructor> = hyps.to_vec();
    // Substitute from innermost quantifier (Rel(0)) outward.
    // Each substitution reduces all remaining de Bruijn indices by 1.
    // Previously inserted fresh unifiers are traversed by later substitutions, so
    // they must start with a nesting level equal to the number of remaining outer
    // substitutions. That keeps them at nl=0 after the last pass instead of
    // underflowing to the `~1` sentinel (`usize::MAX`).
    let total_quantifiers = quantifier_kinds.len();
    for (substitution_index, quantified_kind) in quantifier_kinds.iter().rev().enumerate() {
        let remaining_outer_substitutions =
            total_quantifiers.saturating_sub(substitution_index.saturating_add(1));
        let fresh = fresh_cunif_with_nesting(
            span.clone(),
            quantified_kind.clone(),
            "_inst",
            remaining_outer_substitutions,
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

fn snapshot_class_resolution_attempt(
    class: &elab::LocatedConstructor,
    head: &elab::LocatedConstructor,
    hypotheses: &[elab::LocatedConstructor],
) -> (
    Vec<(elab::CUnifRef, elab::CUnif)>,
    Vec<(elab::KUnifRef, elab::KUnif)>,
) {
    let mut constructor_snapshots: Vec<(elab::CUnifRef, elab::CUnif)> = Vec::new();
    let mut seen_constructor_unifs: HashSet<usize> = HashSet::new();
    let mut kind_snapshots: Vec<(elab::KUnifRef, elab::KUnif)> = Vec::new();
    let mut seen_kind_unifs: HashSet<usize> = HashSet::new();
    let mut remaining_budget = CLASS_MATCH_SNAPSHOT_MAX_NODES;

    snapshot_constructor_unifiers(
        class,
        &mut constructor_snapshots,
        &mut seen_constructor_unifs,
        &mut kind_snapshots,
        &mut seen_kind_unifs,
        &mut remaining_budget,
    );
    snapshot_constructor_unifiers(
        head,
        &mut constructor_snapshots,
        &mut seen_constructor_unifs,
        &mut kind_snapshots,
        &mut seen_kind_unifs,
        &mut remaining_budget,
    );
    for hypothesis in hypotheses {
        snapshot_constructor_unifiers(
            hypothesis,
            &mut constructor_snapshots,
            &mut seen_constructor_unifs,
            &mut kind_snapshots,
            &mut seen_kind_unifs,
            &mut remaining_budget,
        );
    }

    (constructor_snapshots, kind_snapshots)
}

fn try_resolve_class_rule(
    elaboration_environment: &Env,
    class: &elab::LocatedConstructor,
    span: &Span,
    quantifier_kinds: &[elab::LocatedKind],
    hypotheses: &[elab::LocatedConstructor],
    head: &elab::LocatedConstructor,
    witness: &elab::LocatedExpression,
) -> Option<(elab::LocatedExpression, elab::LocatedConstructor)> {
    let (inst_head, inst_hyps) = instantiate_rule(
        elaboration_environment,
        quantifier_kinds,
        hypotheses,
        head,
        span,
    );
    let (constructor_snapshots, kind_snapshots) =
        snapshot_class_resolution_attempt(class, &inst_head, &inst_hyps);

    match try_match_class(
        elaboration_environment,
        class,
        &inst_head,
        quantifier_kinds.len(),
    ) {
        true => {
            let all_hypotheses_satisfied = inst_hyps.iter().all(|hypothesis| {
                resolve_class(elaboration_environment, hypothesis, span).is_some()
            });
            match all_hypotheses_satisfied {
                true => Some((witness.clone(), inst_head)),
                false => {
                    restore_class_match_snapshots(constructor_snapshots, kind_snapshots);
                    None
                }
            }
        }
        false => {
            restore_class_match_snapshots(constructor_snapshots, kind_snapshots);
            None
        }
    }
}

fn resolve_class(
    elaboration_environment: &Env,
    class: &elab::LocatedConstructor,
    span: &Span,
) -> Option<(elab::LocatedExpression, elab::LocatedConstructor)> {
    if let Some(folder_witness) = resolve_folder_witness(elaboration_environment, class, span) {
        return Some(folder_witness);
    }
    // Try all classes in the environment
    for rules in elaboration_environment.classes().values() {
        let class_n = hnorm_con(class.clone());
        // Try closed rules first
        for (quantifier_kinds, hyps, head, witness) in &rules.closed_rules {
            match try_resolve_class_rule(
                elaboration_environment,
                &class_n,
                span,
                quantifier_kinds,
                hyps,
                head,
                witness,
            ) {
                Some(resolved) => return Some(resolved),
                None => {}
            }
        }
        // Then open rules
        for (quantifier_kinds, hyps, head, witness) in &rules.open_rules {
            match try_resolve_class_rule(
                elaboration_environment,
                &class_n,
                span,
                quantifier_kinds,
                hyps,
                head,
                witness,
            ) {
                Some(resolved) => return Some(resolved),
                None => {}
            }
        }
    }
    None
}

const CLASS_MATCH_SNAPSHOT_MAX_NODES: usize = 4096;

fn snapshot_constructor_unifiers(
    constructor: &elab::LocatedConstructor,
    constructor_snapshots: &mut Vec<(elab::CUnifRef, elab::CUnif)>,
    seen_constructor_unifs: &mut HashSet<usize>,
    kind_snapshots: &mut Vec<(elab::KUnifRef, elab::KUnif)>,
    seen_kind_unifs: &mut HashSet<usize>,
    remaining_budget: &mut usize,
) {
    if *remaining_budget == 0 {
        return;
    }
    *remaining_budget -= 1;

    match &constructor.node {
        elab::Constructor::TFun(domain, range) => {
            snapshot_constructor_unifiers(
                domain,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
            snapshot_constructor_unifiers(
                range,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
        }
        elab::Constructor::TCFun(_, _, kind, body) => {
            snapshot_kind_unifiers(
                kind,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
            snapshot_constructor_unifiers(
                body,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
        }
        elab::Constructor::TRecord(row) => {
            snapshot_constructor_unifiers(
                row,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
        }
        elab::Constructor::TDisjoint(left, right, body) => {
            snapshot_constructor_unifiers(
                left,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
            snapshot_constructor_unifiers(
                right,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
            snapshot_constructor_unifiers(
                body,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
        }
        elab::Constructor::App(function_constructor, argument_constructor)
        | elab::Constructor::Concat(function_constructor, argument_constructor) => {
            snapshot_constructor_unifiers(
                function_constructor,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
            snapshot_constructor_unifiers(
                argument_constructor,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
        }
        elab::Constructor::Abs(_, kind, body) => {
            snapshot_kind_unifiers(
                kind,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
            snapshot_constructor_unifiers(
                body,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
        }
        elab::Constructor::KAbs(_, body) | elab::Constructor::TKFun(_, body) => {
            snapshot_constructor_unifiers(
                body,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
        }
        elab::Constructor::KApp(function_constructor, kind) => {
            snapshot_constructor_unifiers(
                function_constructor,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
            snapshot_kind_unifiers(
                kind,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
        }
        elab::Constructor::Record(kind, fields) => {
            snapshot_kind_unifiers(
                kind,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
            for (field_name, field_type) in fields {
                snapshot_constructor_unifiers(
                    field_name,
                    constructor_snapshots,
                    seen_constructor_unifs,
                    kind_snapshots,
                    seen_kind_unifs,
                    remaining_budget,
                );
                snapshot_constructor_unifiers(
                    field_type,
                    constructor_snapshots,
                    seen_constructor_unifs,
                    kind_snapshots,
                    seen_kind_unifs,
                    remaining_budget,
                );
            }
        }
        elab::Constructor::Map(left_kind, right_kind) => {
            snapshot_kind_unifiers(
                left_kind,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
            snapshot_kind_unifiers(
                right_kind,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
        }
        elab::Constructor::Tuple(items) => {
            for item in items {
                snapshot_constructor_unifiers(
                    item,
                    constructor_snapshots,
                    seen_constructor_unifs,
                    kind_snapshots,
                    seen_kind_unifs,
                    remaining_budget,
                );
            }
        }
        elab::Constructor::Proj(inner, _) => {
            snapshot_constructor_unifiers(
                inner,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
        }
        elab::Constructor::Unif(_, _, kind, _, cell) => {
            let key = Arc::as_ptr(cell) as usize;
            if seen_constructor_unifs.insert(key) {
                let snapshot = crate::compiler_diagnostics::lock_for_compile(
                    cell.as_ref(),
                    "class-match constructor snapshot",
                )
                .clone();
                constructor_snapshots.push((cell.clone(), snapshot));
            }
            snapshot_kind_unifiers(
                kind,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
        }
        elab::Constructor::Rel(_)
        | elab::Constructor::Named(_)
        | elab::Constructor::ModProj(_, _, _)
        | elab::Constructor::Name(_)
        | elab::Constructor::Unit
        | elab::Constructor::Error => {}
    }
}

fn snapshot_kind_unifiers(
    kind: &elab::LocatedKind,
    constructor_snapshots: &mut Vec<(elab::CUnifRef, elab::CUnif)>,
    seen_constructor_unifs: &mut HashSet<usize>,
    kind_snapshots: &mut Vec<(elab::KUnifRef, elab::KUnif)>,
    seen_kind_unifs: &mut HashSet<usize>,
    remaining_budget: &mut usize,
) {
    if *remaining_budget == 0 {
        return;
    }
    *remaining_budget -= 1;

    match &kind.node {
        elab::Kind::Arrow(left, right) => {
            snapshot_kind_unifiers(
                left,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
            snapshot_kind_unifiers(
                right,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
        }
        elab::Kind::Record(inner) | elab::Kind::Fun(_, inner) => {
            snapshot_kind_unifiers(
                inner,
                constructor_snapshots,
                seen_constructor_unifs,
                kind_snapshots,
                seen_kind_unifs,
                remaining_budget,
            );
        }
        elab::Kind::Tuple(items) => {
            for item in items {
                snapshot_kind_unifiers(
                    item,
                    constructor_snapshots,
                    seen_constructor_unifs,
                    kind_snapshots,
                    seen_kind_unifs,
                    remaining_budget,
                );
            }
        }
        elab::Kind::Unif(_, _, cell) | elab::Kind::TupleUnif(_, _, cell) => {
            let key = Arc::as_ptr(cell) as usize;
            if seen_kind_unifs.insert(key) {
                let snapshot = crate::compiler_diagnostics::lock_for_compile(
                    cell.as_ref(),
                    "class-match kind snapshot",
                )
                .clone();
                kind_snapshots.push((cell.clone(), snapshot));
            }
        }
        elab::Kind::Type
        | elab::Kind::Name
        | elab::Kind::Unit
        | elab::Kind::Error
        | elab::Kind::Rel(_) => {}
    }
}

fn restore_class_match_snapshots(
    constructor_snapshots: Vec<(elab::CUnifRef, elab::CUnif)>,
    kind_snapshots: Vec<(elab::KUnifRef, elab::KUnif)>,
) {
    for (cell, snapshot) in constructor_snapshots {
        *crate::compiler_diagnostics::lock_for_compile(
            cell.as_ref(),
            "class-match constructor restore",
        ) = snapshot;
    }
    for (cell, snapshot) in kind_snapshots {
        *crate::compiler_diagnostics::lock_for_compile(cell.as_ref(), "class-match kind restore") =
            snapshot;
    }
}

fn snapshot_constructor_match_attempt(
    constructors: &[&elab::LocatedConstructor],
) -> (
    Vec<(elab::CUnifRef, elab::CUnif)>,
    Vec<(elab::KUnifRef, elab::KUnif)>,
) {
    let mut constructor_snapshots: Vec<(elab::CUnifRef, elab::CUnif)> = Vec::new();
    let mut seen_constructor_unifs: HashSet<usize> = HashSet::new();
    let mut kind_snapshots: Vec<(elab::KUnifRef, elab::KUnif)> = Vec::new();
    let mut seen_kind_unifs: HashSet<usize> = HashSet::new();
    let mut remaining_budget = CLASS_MATCH_SNAPSHOT_MAX_NODES;

    for constructor in constructors {
        snapshot_constructor_unifiers(
            constructor,
            &mut constructor_snapshots,
            &mut seen_constructor_unifs,
            &mut kind_snapshots,
            &mut seen_kind_unifs,
            &mut remaining_budget,
        );
    }

    (constructor_snapshots, kind_snapshots)
}

fn row_field_pair_matches(
    elaboration_context: &mut ElabCtx,
    elaboration_environment: &Env,
    diagnostic_span: &Span,
    left_name: &elab::LocatedConstructor,
    left_type: &elab::LocatedConstructor,
    right_name: &elab::LocatedConstructor,
    right_type: &elab::LocatedConstructor,
    recursion_depth: usize,
) -> bool {
    let (constructor_snapshots, kind_snapshots) =
        snapshot_constructor_match_attempt(&[left_name, left_type, right_name, right_type]);
    let mut probe_context = ElabCtx::new();
    let name_match = unify_cons_inner(
        &mut probe_context,
        elaboration_environment,
        diagnostic_span,
        left_name,
        right_name,
        recursion_depth + 1,
    )
    .is_ok();
    if !name_match {
        restore_class_match_snapshots(constructor_snapshots, kind_snapshots);
        return false;
    }
    let type_match = unify_cons_inner(
        elaboration_context,
        elaboration_environment,
        diagnostic_span,
        left_type,
        right_type,
        recursion_depth + 1,
    )
    .is_ok();
    if !type_match {
        restore_class_match_snapshots(constructor_snapshots, kind_snapshots);
        return false;
    }
    true
}

fn resolve_folder_witness(
    elaboration_environment: &Env,
    class: &elab::LocatedConstructor,
    span: &Span,
) -> Option<(elab::LocatedExpression, elab::LocatedConstructor)> {
    let normalized_class = hnorm_con_expression_head(elaboration_environment, class.clone());
    match &normalized_class.node {
        elab::Constructor::App(folder_head, row_constructor)
            if constructor_is_folder_head(elaboration_environment, folder_head) =>
        {
            let normalized_row = hnorm_con(row_constructor.as_ref().clone());
            match &normalized_row.node {
                elab::Constructor::Record(kind, fields) => {
                    let witness =
                        build_folder_witness(elaboration_environment, kind.as_ref(), fields, span)?;
                    Some((witness, normalized_class))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn build_folder_witness(
    elaboration_environment: &Env,
    kind: &elab::LocatedKind,
    fields: &[(elab::LocatedConstructor, elab::LocatedConstructor)],
    span: &Span,
) -> Option<elab::LocatedExpression> {
    let folder_module = resolve_folder_module(elaboration_environment)?;
    let mut witness = Located::new(
        elab::Expression::ModProj(
            folder_module.structure_id,
            folder_module.path.clone(),
            "nil".to_string(),
        ),
        span.clone(),
    );
    witness = Located::new(
        elab::Expression::KApp(Box::new(witness), Box::new(kind.clone())),
        span.clone(),
    );

    let mut accumulated_fields: Vec<(elab::LocatedConstructor, elab::LocatedConstructor)> =
        Vec::new();
    for (field_name, field_type) in fields.iter().rev() {
        let rest_row = Located::new(
            elab::Constructor::Record(Box::new(kind.clone()), accumulated_fields.clone()),
            span.clone(),
        );
        let mut cons_expression = Located::new(
            elab::Expression::ModProj(
                folder_module.structure_id,
                folder_module.path.clone(),
                "cons".to_string(),
            ),
            span.clone(),
        );
        cons_expression = Located::new(
            elab::Expression::KApp(Box::new(cons_expression), Box::new(kind.clone())),
            span.clone(),
        );
        cons_expression = Located::new(
            elab::Expression::CApp(Box::new(cons_expression), rest_row),
            span.clone(),
        );
        cons_expression = Located::new(
            elab::Expression::CApp(Box::new(cons_expression), field_name.clone()),
            span.clone(),
        );
        cons_expression = Located::new(
            elab::Expression::CApp(Box::new(cons_expression), field_type.clone()),
            span.clone(),
        );
        witness = Located::new(
            elab::Expression::App(Box::new(cons_expression), Box::new(witness)),
            span.clone(),
        );
        accumulated_fields.insert(0, (field_name.clone(), field_type.clone()));
    }

    Some(witness)
}

struct FolderModuleRef {
    structure_id: usize,
    path: Vec<String>,
}

fn resolve_folder_module(elaboration_environment: &Env) -> Option<FolderModuleRef> {
    match elaboration_environment.lookup_str("Folder") {
        Some((structure_id, _)) => Some(FolderModuleRef {
            structure_id: *structure_id,
            path: Vec::new(),
        }),
        None => match elaboration_environment.lookup_str("Top") {
            Some((top_id, _)) => Some(FolderModuleRef {
                structure_id: *top_id,
                path: vec!["Folder".to_string()],
            }),
            None => None,
        },
    }
}

fn try_match_class(
    elaboration_environment: &Env,
    class: &elab::LocatedConstructor,
    head: &elab::LocatedConstructor,
    _num_quantifiers: usize,
) -> bool {
    let normalized_class = hnorm_con_expression_head(elaboration_environment, class.clone());
    let normalized_head = hnorm_con_expression_head(elaboration_environment, head.clone());
    unify_cons_inner(
        &mut ElabCtx::new(),
        elaboration_environment,
        &class.span,
        &normalized_class,
        &normalized_head,
        0,
    )
    .is_ok()
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
        elaboration_environment = new_env; // Step: env after `elab_decl` on this AST node.
        disjointness_environment = new_denv; // Step: parallel disjointness state.
        solve_constraints(&mut elaboration_context, &elaboration_environment);
        all_decls.extend(ds); // Accumulate elaborated declarations.

        // Mirror SML `elabFile` `dopen` on `Basis` / `Top` once those structures exist.
        match &decl.node {
            crate::source::Decl::FfiStr(structure_name, _, _) if structure_name == "Basis" => {
                // `FfiStr("Basis", ...)` ⇒ implicit `open Basis` for prelude names.
                let auto_open_span = decl.span.clone();
                let (open_declarations, opened_env, opened_disjointness) = elab_open(
                    &mut elaboration_context,
                    &elaboration_environment,
                    &disjointness_environment,
                    &["Basis".to_string()],
                    &auto_open_span,
                );
                elaboration_environment = opened_env; // Bind `unit`, `transaction`, …
                disjointness_environment = opened_disjointness;
                all_decls.extend(open_declarations); // Surface generated open decls if any.
            }
            crate::source::Decl::Str(structure_name, _, _, _, _) if structure_name == "Top" => {
                // `structure Top` (from lib) ⇒ implicit `open Top` for standard helpers.
                let auto_open_span = decl.span.clone();
                let (open_declarations, opened_env, opened_disjointness) = elab_open(
                    &mut elaboration_context,
                    &elaboration_environment,
                    &disjointness_environment,
                    &["Top".to_string()],
                    &auto_open_span,
                );
                elaboration_environment = opened_env;
                disjointness_environment = opened_disjointness;
                all_decls.extend(open_declarations);
            }
            _ => {
                // Other declaration forms do not trigger auto-open here.
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
    use std::path::PathBuf;

    /// Surface `@@x` is [`source::Exp::Var`] with [`source::Inference::DontInfer`] (no `TDisjoint` check).
    #[test]
    fn dont_infer_var_does_not_force_tdisjoint_check() {
        let span = crate::error_types::Span::dummy();
        let x_ty = Located::new(elab::Constructor::Unit, span.clone());
        let elaboration_environment = Env::empty().push_e_rel("x".into(), x_ty);
        let exp = Located::new(
            source::Exp::Var(vec![], "x".into(), source::Inference::DontInfer),
            span.clone(),
        );
        let mut elaboration_context = ElabCtx::new();
        let disjointness_environment = disjoint::empty_env();
        let (ee, et) = elab_exp(
            &mut elaboration_context,
            &elaboration_environment,
            &disjointness_environment,
            &exp,
        );
        assert!(
            !elaboration_context.errors.iter().any(|(sp, _)| sp == &span),
            "@@x-style var should not record errors at dummy span"
        );
        assert!(matches!(ee.node, elab::Expression::Rel(0)));
        assert!(matches!(et.node, elab::Constructor::Unit));
    }

    #[test]
    fn unify_cons_treats_all_unit_kind_constructors_as_equal() {
        let span = crate::error_types::Span::dummy();
        let unit_kind = Located::new(elab::Kind::Unit, span.clone());
        let left_constructor = Located::new(elab::Constructor::Rel(0), span.clone());
        let right_constructor = Located::new(elab::Constructor::Unit, span.clone());
        let elaboration_environment = Env::empty().push_c_rel("u".into(), unit_kind);
        let mut elaboration_context = ElabCtx::new();
        let result = unify_cons(
            &mut elaboration_context,
            &elaboration_environment,
            &span,
            &left_constructor,
            &right_constructor,
        );
        assert!(
            result.is_ok(),
            "Unit-kinded constructors should unify extensionally, got {:?}",
            result
        );
    }

    #[test]
    fn unify_kinds_treats_rel_and_unit_as_compatible() {
        let span = crate::error_types::Span::dummy();
        let left_kind = Located::new(elab::Kind::Rel(0), span.clone());
        let right_kind = Located::new(elab::Kind::Unit, span.clone());
        let elaboration_environment = Env::empty();
        let result = unify_kinds(&elaboration_environment, &left_kind, &right_kind);
        assert!(
            result.is_ok(),
            "kind variable and Unit should unify for folder parity, got {:?}",
            result
        );
    }

    #[test]
    fn unify_cons_treats_closed_numeric_records_as_tuples() {
        let span = crate::error_types::Span::dummy();
        let type_kind = Located::new(elab::Kind::Type, span.clone());
        let row_kind = Located::new(
            elab::Kind::Record(Box::new(type_kind.clone())),
            span.clone(),
        );
        let record_row = Located::new(
            elab::Constructor::Record(
                Box::new(row_kind),
                vec![
                    (
                        Located::new(elab::Constructor::Name("1".into()), span.clone()),
                        Located::new(elab::Constructor::Rel(0), span.clone()),
                    ),
                    (
                        Located::new(elab::Constructor::Name("2".into()), span.clone()),
                        Located::new(elab::Constructor::Rel(1), span.clone()),
                    ),
                ],
            ),
            span.clone(),
        );
        let left_constructor = Located::new(
            elab::Constructor::TRecord(Box::new(record_row)),
            span.clone(),
        );
        let right_constructor = Located::new(
            elab::Constructor::Tuple(vec![
                Located::new(elab::Constructor::Rel(0), span.clone()),
                Located::new(elab::Constructor::Rel(1), span.clone()),
            ]),
            span.clone(),
        );
        let elaboration_environment = Env::empty()
            .push_c_rel("b".into(), type_kind.clone())
            .push_c_rel("a".into(), type_kind);
        let mut elaboration_context = ElabCtx::new();
        let result = unify_cons(
            &mut elaboration_context,
            &elaboration_environment,
            &span,
            &left_constructor,
            &right_constructor,
        );
        assert!(
            result.is_ok(),
            "closed numeric records should unify with tuples, got {:?}",
            result
        );
    }

    #[test]
    fn unify_cons_unifies_map_constructors_by_kind() {
        let span = crate::error_types::Span::dummy();
        let type_kind = Located::new(elab::Kind::Type, span.clone());
        let row_kind = Located::new(
            elab::Kind::Record(Box::new(type_kind.clone())),
            span.clone(),
        );
        let left_constructor = Located::new(
            elab::Constructor::Map(Box::new(type_kind.clone()), Box::new(row_kind.clone())),
            span.clone(),
        );
        let right_constructor = Located::new(
            elab::Constructor::Map(Box::new(type_kind), Box::new(row_kind)),
            span.clone(),
        );
        let elaboration_environment = Env::empty();
        let mut elaboration_context = ElabCtx::new();
        let result = unify_cons(
            &mut elaboration_context,
            &elaboration_environment,
            &span,
            &left_constructor,
            &right_constructor,
        );
        assert!(
            result.is_ok(),
            "map constructors with equal domain/range kinds should unify, got {:?}",
            result
        );
    }

    #[test]
    fn unify_cons_treats_abstract_folder_application_extensionally() {
        let span = crate::error_types::Span::dummy();
        let type_kind = Located::new(elab::Kind::Type, span.clone());
        let row_kind = Located::new(
            elab::Kind::Record(Box::new(type_kind.clone())),
            span.clone(),
        );
        let row_constructor = Located::new(
            elab::Constructor::Record(Box::new(row_kind.clone()), Vec::new()),
            span.clone(),
        );
        let folder_kind = Located::new(
            elab::Kind::Arrow(Box::new(row_kind), Box::new(type_kind)),
            span.clone(),
        );
        let (elaboration_environment, folder_id) =
            Env::empty().push_c_named("folder".into(), folder_kind, None);
        let abstract_folder_application = Located::new(
            elab::Constructor::App(
                Box::new(Located::new(
                    elab::Constructor::Named(folder_id),
                    span.clone(),
                )),
                Box::new(row_constructor),
            ),
            span.clone(),
        );
        let mut elaboration_context = ElabCtx::new();
        let extensional_folder = expand_folder_constructor_application(
            &mut elaboration_context,
            &elaboration_environment,
            &abstract_folder_application,
        )
        .expect("folder application should expand extensionally");

        let result = unify_cons(
            &mut elaboration_context,
            &elaboration_environment,
            &span,
            &abstract_folder_application,
            &extensional_folder,
        );
        assert!(
            result.is_ok(),
            "abstract folder applications should unify with their extensional shape, got {:?}",
            result
        );
    }

    #[test]
    fn unify_cons_treats_kind_polymorphic_folder_application_extensionally() {
        let span = crate::error_types::Span::dummy();
        let kind_rel = Located::new(elab::Kind::Rel(0), span.clone());
        let row_kind = Located::new(elab::Kind::Record(Box::new(kind_rel.clone())), span.clone());
        let folder_result_kind = Located::new(elab::Kind::Type, span.clone());
        let folder_kind = Located::new(
            elab::Kind::Fun(
                "K".into(),
                Box::new(Located::new(
                    elab::Kind::Arrow(
                        Box::new(row_kind.clone()),
                        Box::new(folder_result_kind.clone()),
                    ),
                    span.clone(),
                )),
            ),
            span.clone(),
        );
        let (elaboration_environment, folder_id) =
            Env::empty().push_c_named("folder".into(), folder_kind, None);
        let row_constructor = Located::new(
            elab::Constructor::Record(Box::new(row_kind.clone()), Vec::new()),
            span.clone(),
        );
        let abstract_folder_body = Located::new(
            elab::Constructor::App(
                Box::new(Located::new(
                    elab::Constructor::KApp(
                        Box::new(Located::new(
                            elab::Constructor::Named(folder_id),
                            span.clone(),
                        )),
                        Box::new(kind_rel.clone()),
                    ),
                    span.clone(),
                )),
                Box::new(row_constructor),
            ),
            span.clone(),
        );
        let mut elaboration_context = ElabCtx::new();
        let extensional_folder_body = expand_folder_constructor_application(
            &mut elaboration_context,
            &elaboration_environment,
            &abstract_folder_body,
        )
        .expect("kind-polymorphic folder application should expand extensionally");
        let abstract_folder = Located::new(
            elab::Constructor::KAbs("K".into(), Box::new(abstract_folder_body)),
            span.clone(),
        );
        let extensional_folder = Located::new(
            elab::Constructor::KAbs("K".into(), Box::new(extensional_folder_body)),
            span.clone(),
        );

        let result = unify_cons(
            &mut elaboration_context,
            &elaboration_environment,
            &span,
            &abstract_folder,
            &extensional_folder,
        );
        assert!(
            result.is_ok(),
            "kind-polymorphic abstract folder applications should unify extensionally, got {:?}",
            result
        );
    }

    #[test]
    fn unify_rows_solves_unknown_tail_to_empty_row() {
        let span = crate::error_types::Span::dummy();
        let type_kind = Located::new(elab::Kind::Type, span.clone());
        let row_kind = Located::new(elab::Kind::Record(Box::new(type_kind)), span.clone());
        let elaboration_environment = Env::empty();
        let mut elaboration_context = ElabCtx::new();
        let unknown_tail = fresh_cunif(
            &elaboration_environment,
            span.clone(),
            row_kind.clone(),
            "tail",
        );
        let empty_row = Located::new(
            elab::Constructor::Record(Box::new(row_kind), Vec::new()),
            span.clone(),
        );

        let result = unify_rows(
            &mut elaboration_context,
            &elaboration_environment,
            &span,
            &unknown_tail,
            &empty_row,
            0,
        );
        assert!(
            result.is_ok(),
            "empty-row tail solve should succeed: {:?}",
            result
        );

        let solved = hnorm_con(unknown_tail);
        assert!(
            cons_eq_simple(&solved, &empty_row),
            "unknown tail should normalize to the empty row, got {}",
            crate::elaborated::type_display::format_constructor(&solved)
        );
    }

    #[test]
    fn unify_rows_solves_rigid_row_against_unknown_concat_tails() {
        let span = crate::error_types::Span::dummy();
        let type_kind = Located::new(elab::Kind::Type, span.clone());
        let row_kind = Located::new(
            elab::Kind::Record(Box::new(type_kind.clone())),
            span.clone(),
        );
        let elaboration_environment = Env::empty().push_c_rel("inp".into(), row_kind.clone());
        let mut elaboration_context = ElabCtx::new();
        let first_tail = fresh_cunif(
            &elaboration_environment,
            span.clone(),
            row_kind.clone(),
            "use",
        );
        let second_tail = fresh_cunif(
            &elaboration_environment,
            span.clone(),
            row_kind.clone(),
            "bind",
        );
        let rigid_row = Located::new(elab::Constructor::Rel(0), span.clone());
        let unknown_concat = Located::new(
            elab::Constructor::Concat(Box::new(first_tail.clone()), Box::new(second_tail.clone())),
            span.clone(),
        );

        let result = unify_rows(
            &mut elaboration_context,
            &elaboration_environment,
            &span,
            &rigid_row,
            &unknown_concat,
            0,
        );
        assert!(
            result.is_ok(),
            "rigid-row/unknown-concat solve should succeed: {:?}",
            result
        );

        let solved_first_tail = hnorm_con(first_tail);
        let solved_second_tail = hnorm_con(second_tail);
        assert!(
            matches!(solved_first_tail.node, elab::Constructor::Rel(0)),
            "first tail should normalize to the rigid row, got {}",
            crate::elaborated::type_display::format_constructor(&solved_first_tail)
        );
        assert!(
            matches!(solved_second_tail.node, elab::Constructor::Record(_, ref fields) if fields.is_empty()),
            "second tail should normalize to the empty row, got {}",
            crate::elaborated::type_display::format_constructor(&solved_second_tail)
        );
    }

    #[test]
    fn sub_sgn_realizes_expected_abstract_constructor_ids_through_actual_items() {
        let span = crate::error_types::Span::dummy();
        let type_kind = Located::new(elab::Kind::Type, span.clone());
        let unary_type_kind = Located::new(
            elab::Kind::Arrow(Box::new(type_kind.clone()), Box::new(type_kind.clone())),
            span.clone(),
        );
        let empty_row = Located::new(
            elab::Constructor::Record(
                Box::new(Located::new(
                    elab::Kind::Record(Box::new(type_kind.clone())),
                    span.clone(),
                )),
                Vec::new(),
            ),
            span.clone(),
        );
        let unit_type = Located::new(
            elab::Constructor::TRecord(Box::new(empty_row)),
            span.clone(),
        );
        let actual_constructor_id = 1000;
        let expected_constructor_id = 1001;
        let actual_constructor_definition = Located::new(
            elab::Constructor::Abs(
                "t".into(),
                Box::new(type_kind.clone()),
                Box::new(Located::new(elab::Constructor::Rel(0), span.clone())),
            ),
            span.clone(),
        );
        let actual_value_type = Located::new(
            elab::Constructor::App(
                Box::new(actual_constructor_definition.clone()),
                Box::new(unit_type.clone()),
            ),
            span.clone(),
        );
        let expected_value_type = Located::new(
            elab::Constructor::App(
                Box::new(Located::new(
                    elab::Constructor::Named(expected_constructor_id),
                    span.clone(),
                )),
                Box::new(unit_type),
            ),
            span.clone(),
        );
        let actual_signature = Located::new(
            elab::Signature::Const(vec![
                Located::new(
                    elab::SignatureItem::Constructor(
                        "Wrap".into(),
                        actual_constructor_id,
                        unary_type_kind.clone(),
                        actual_constructor_definition,
                    ),
                    span.clone(),
                ),
                Located::new(
                    elab::SignatureItem::Val("x".into(), 2000, actual_value_type),
                    span.clone(),
                ),
            ]),
            span.clone(),
        );
        let expected_signature = Located::new(
            elab::Signature::Const(vec![
                Located::new(
                    elab::SignatureItem::ConAbs(
                        "Wrap".into(),
                        expected_constructor_id,
                        unary_type_kind,
                    ),
                    span.clone(),
                ),
                Located::new(
                    elab::SignatureItem::Val("x".into(), 2001, expected_value_type),
                    span.clone(),
                ),
            ]),
            span.clone(),
        );

        let elaboration_environment = Env::empty();
        let disjointness_environment = disjoint::empty_env();
        let mut elaboration_context = ElabCtx::new();
        sub_sgn(
            &mut elaboration_context,
            &elaboration_environment,
            &disjointness_environment,
            &actual_signature,
            &expected_signature,
            &span,
        );
        assert!(
            elaboration_context.errors.is_empty(),
            "expected abstract constructor ids should realize through matching actual items: {:?}",
            elaboration_context.errors
        );
    }

    #[test]
    fn sub_sgn_realizes_outer_abstract_constructor_ids_inside_nested_structures() {
        let span = crate::error_types::Span::dummy();
        let type_kind = Located::new(elab::Kind::Type, span.clone());
        let unary_type_kind = Located::new(
            elab::Kind::Arrow(Box::new(type_kind.clone()), Box::new(type_kind.clone())),
            span.clone(),
        );
        let unit_row = Located::new(
            elab::Constructor::Record(
                Box::new(Located::new(
                    elab::Kind::Record(Box::new(type_kind.clone())),
                    span.clone(),
                )),
                Vec::new(),
            ),
            span.clone(),
        );
        let unit_type = Located::new(elab::Constructor::TRecord(Box::new(unit_row)), span.clone());
        let actual_constructor_id = 3000;
        let expected_constructor_id = 3001;
        let actual_constructor_definition = Located::new(
            elab::Constructor::Abs(
                "t".into(),
                Box::new(type_kind.clone()),
                Box::new(Located::new(elab::Constructor::Rel(0), span.clone())),
            ),
            span.clone(),
        );
        let actual_nested_value_type = Located::new(
            elab::Constructor::App(
                Box::new(actual_constructor_definition.clone()),
                Box::new(unit_type.clone()),
            ),
            span.clone(),
        );
        let expected_nested_value_type = Located::new(
            elab::Constructor::App(
                Box::new(Located::new(
                    elab::Constructor::Named(expected_constructor_id),
                    span.clone(),
                )),
                Box::new(unit_type),
            ),
            span.clone(),
        );
        let actual_nested_signature = Located::new(
            elab::Signature::Const(vec![Located::new(
                elab::SignatureItem::Val("x".into(), 4000, actual_nested_value_type),
                span.clone(),
            )]),
            span.clone(),
        );
        let expected_nested_signature = Located::new(
            elab::Signature::Const(vec![Located::new(
                elab::SignatureItem::Val("x".into(), 4001, expected_nested_value_type),
                span.clone(),
            )]),
            span.clone(),
        );
        let actual_signature = Located::new(
            elab::Signature::Const(vec![
                Located::new(
                    elab::SignatureItem::Constructor(
                        "Wrap".into(),
                        actual_constructor_id,
                        unary_type_kind.clone(),
                        actual_constructor_definition,
                    ),
                    span.clone(),
                ),
                Located::new(
                    elab::SignatureItem::Structure(
                        elab::ImportMode::Skip,
                        "Inner".into(),
                        5000,
                        actual_nested_signature,
                    ),
                    span.clone(),
                ),
            ]),
            span.clone(),
        );
        let expected_signature = Located::new(
            elab::Signature::Const(vec![
                Located::new(
                    elab::SignatureItem::ConAbs(
                        "Wrap".into(),
                        expected_constructor_id,
                        unary_type_kind,
                    ),
                    span.clone(),
                ),
                Located::new(
                    elab::SignatureItem::Structure(
                        elab::ImportMode::Skip,
                        "Inner".into(),
                        5001,
                        expected_nested_signature,
                    ),
                    span.clone(),
                ),
            ]),
            span.clone(),
        );

        let elaboration_environment = Env::empty();
        let disjointness_environment = disjoint::empty_env();
        let mut elaboration_context = ElabCtx::new();
        sub_sgn(
            &mut elaboration_context,
            &elaboration_environment,
            &disjointness_environment,
            &actual_signature,
            &expected_signature,
            &span,
        );
        assert!(
            elaboration_context.errors.is_empty(),
            "outer abstract constructor ids should realize inside nested structures: {:?}",
            elaboration_context.errors
        );
    }

    #[test]
    fn deep_normalize_constructor_reduces_rebuilt_kapp_then_app_redex() {
        let span = crate::error_types::Span::dummy();
        let type_kind = Located::new(elab::Kind::Type, span.clone());
        let identity_constructor = Located::new(
            elab::Constructor::KAbs(
                "K".into(),
                Box::new(Located::new(
                    elab::Constructor::Abs(
                        "t".into(),
                        Box::new(Located::new(elab::Kind::Rel(0), span.clone())),
                        Box::new(Located::new(elab::Constructor::Rel(0), span.clone())),
                    ),
                    span.clone(),
                )),
            ),
            span.clone(),
        );
        let unit_type = Located::new(
            elab::Constructor::TRecord(Box::new(Located::new(
                elab::Constructor::Record(
                    Box::new(Located::new(
                        elab::Kind::Record(Box::new(type_kind.clone())),
                        span.clone(),
                    )),
                    Vec::new(),
                ),
                span.clone(),
            ))),
            span.clone(),
        );
        let redex = Located::new(
            elab::Constructor::App(
                Box::new(Located::new(
                    elab::Constructor::KApp(Box::new(identity_constructor), Box::new(type_kind)),
                    span.clone(),
                )),
                Box::new(unit_type.clone()),
            ),
            span.clone(),
        );

        let normalized = deep_normalize_constructor(&Env::empty(), redex);
        assert!(
            cons_eq_simple(&normalized, &unit_type),
            "deep normalization should contract rebuilt kind/app redexes, got {}",
            crate::elaborated::type_display::format_constructor(&normalized)
        );
    }

    /// After `open Basis`, datatype constructors (`True`, `False`, …) must appear in
    /// [`Env::lookup_constructor`] so patterns and some expression forms resolve.
    #[test]
    fn basis_open_registers_bool_pattern_constructors() {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let lib_dir = manifest_dir.join("lib/ur");
        if !lib_dir.join("basis.urs").is_file() {
            return;
        }
        let job = crate::compiler::Job {
            sources: vec![],
            basis_lib_dir: Some(lib_dir),
            ..Default::default()
        };
        let settings = Settings::new();
        let mut parse_errors = ErrorReporter::new_silent();
        let Some(source_file) = crate::compiler::parse_sources(&job, &settings, &mut parse_errors)
        else {
            return;
        };
        let basis_decl = source_file
            .first()
            .filter(|located_decl| {
                matches!(&located_decl.node, crate::source::Decl::FfiStr(name, _, _) if name == "Basis")
            })
            .expect("parse_sources boot job must start with Basis FfiStr");
        let mut elaboration_context = ElabCtx::new();
        let mut elaboration_environment = Env::empty();
        let mut disjointness_environment = disjoint::empty_env();
        let (_decls, env_after_basis, denv_after_basis) = elab_decl(
            &mut elaboration_context,
            &elaboration_environment,
            &disjointness_environment,
            basis_decl,
        );
        elaboration_environment = env_after_basis;
        disjointness_environment = denv_after_basis;
        let (_open_decls, env_open, _d_open) = elab_open(
            &mut elaboration_context,
            &elaboration_environment,
            &disjointness_environment,
            &["Basis".to_string()],
            &basis_decl.span,
        );
        assert!(
            env_open.lookup_constructor("True").is_some(),
            "open Basis must register True for pattern/expression lookup"
        );
        assert!(
            env_open.lookup_constructor("False").is_some(),
            "open Basis must register False for pattern/expression lookup"
        );
    }

    /// Parser-desugared `if` uses `Pat::Con(["Basis"], True|False, _)`; those patterns must elaborate like `Basis.True` in expressions.
    #[test]
    fn basis_qualified_bool_patterns_in_case_elaborate() {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let lib_dir = manifest_dir.join("lib/ur");
        if !lib_dir.join("basis.urs").is_file() {
            return;
        }
        let job = crate::compiler::Job {
            sources: vec![],
            basis_lib_dir: Some(lib_dir),
            ..Default::default()
        };
        let settings = Settings::new();
        let mut parse_errors = ErrorReporter::new_silent();
        let Some(source_file) = crate::compiler::parse_sources(&job, &settings, &mut parse_errors)
        else {
            return;
        };
        let basis_decl = source_file
            .first()
            .filter(|located_decl| {
                matches!(&located_decl.node, crate::source::Decl::FfiStr(name, _, _) if name == "Basis")
            })
            .expect("parse_sources boot job must start with Basis FfiStr");
        let mut elaboration_context = ElabCtx::new();
        let mut elaboration_environment = Env::empty();
        let disjointness_environment = disjoint::empty_env();
        let (_decls, env_after_basis, denv_after_basis) = elab_decl(
            &mut elaboration_context,
            &elaboration_environment,
            &disjointness_environment,
            basis_decl,
        );
        elaboration_environment = env_after_basis;
        let (_open_decls, env_open, d_open) = elab_open(
            &mut elaboration_context,
            &elaboration_environment,
            &denv_after_basis,
            &["Basis".to_string()],
            &basis_decl.span,
        );
        let span = basis_decl.span.clone();
        let bool_ty = match env_open.lookup_c("bool") {
            VarLookup::Named(id, _) => Located::new(elab::Constructor::Named(id), span.clone()),
            _ => panic!("expected bool in env after open Basis"),
        };
        let env_b = env_open.push_e_rel("b".into(), bool_ty);
        let cond = Located::new(
            source::Exp::Var(vec![], "b".into(), source::Inference::Infer),
            span.clone(),
        );
        let arm_true = (
            Located::dummy(source::Pat::Con(vec!["Basis".into()], "True".into(), None)),
            Located::new(
                source::Exp::Var(vec![], "False".into(), source::Inference::Infer),
                span.clone(),
            ),
        );
        let arm_false = (
            Located::dummy(source::Pat::Con(vec!["Basis".into()], "False".into(), None)),
            Located::new(
                source::Exp::Var(vec![], "True".into(), source::Inference::Infer),
                span.clone(),
            ),
        );
        let case_exp = Located::new(
            source::Exp::Case(Box::new(cond), vec![arm_true, arm_false]),
            span.clone(),
        );
        let mut ctx2 = ElabCtx::new();
        let (_e, _t) = elab_exp(&mut ctx2, &env_b, &d_open, &case_exp);
        assert!(
            !ctx2
                .errors
                .iter()
                .any(|(_, p)| { matches!(p.id, DiagnosticId::ElabUnboundConstructor) }),
            "Basis.True/Basis.False case arms must elaborate: {:?}",
            ctx2.errors
        );
    }

    #[test]
    fn basis_open_resolves_fieldsof_table_rule_for_unknown_table() {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let lib_dir = manifest_dir.join("lib/ur");
        if !lib_dir.join("basis.urs").is_file() {
            return;
        }
        let job = crate::compiler::Job {
            sources: vec![],
            basis_lib_dir: Some(lib_dir),
            ..Default::default()
        };
        let settings = Settings::new();
        let mut parse_errors = ErrorReporter::new_silent();
        let Some(source_file) = crate::compiler::parse_sources(&job, &settings, &mut parse_errors)
        else {
            return;
        };
        let basis_decl = source_file
            .first()
            .filter(|located_decl| {
                matches!(&located_decl.node, crate::source::Decl::FfiStr(name, _, _) if name == "Basis")
            })
            .expect("parse_sources boot job must start with Basis FfiStr");
        let mut elaboration_context = ElabCtx::new();
        let mut elaboration_environment = Env::empty();
        let disjointness_environment = disjoint::empty_env();
        let (_decls, env_after_basis, denv_after_basis) = elab_decl(
            &mut elaboration_context,
            &elaboration_environment,
            &disjointness_environment,
            basis_decl,
        );
        elaboration_environment = env_after_basis;
        let (_open_decls, env_open, _d_open) = elab_open(
            &mut elaboration_context,
            &elaboration_environment,
            &denv_after_basis,
            &["Basis".to_string()],
            &basis_decl.span,
        );

        let span = basis_decl.span.clone();
        let fields_of_id = match env_open.lookup_c("fieldsOf") {
            VarLookup::Named(id, _) => id,
            _ => panic!("expected fieldsOf class in env after open Basis"),
        };
        let table_type = fresh_cunif(
            &env_open,
            span.clone(),
            Located::new(elab::Kind::Type, span.clone()),
            "table_type",
        );
        let row_type = fresh_cunif(
            &env_open,
            span.clone(),
            Located::new(
                elab::Kind::Record(Box::new(Located::new(elab::Kind::Type, span.clone()))),
                span.clone(),
            ),
            "row_type",
        );
        let class_goal = Located::new(
            elab::Constructor::App(
                Box::new(Located::new(
                    elab::Constructor::App(
                        Box::new(Located::new(
                            elab::Constructor::Named(fields_of_id),
                            span.clone(),
                        )),
                        Box::new(table_type),
                    ),
                    span.clone(),
                )),
                Box::new(row_type),
            ),
            span.clone(),
        );

        assert!(
            resolve_class(&env_open, &class_goal, &span).is_some(),
            "fieldsOf_table should resolve fieldsOf ?t ?fs after open Basis"
        );
    }

    #[test]
    fn basis_open_fields_of_resolution_keeps_matched_unifier_bindings() {
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let lib_dir = manifest_dir.join("lib/ur");
        if !lib_dir.join("basis.urs").is_file() {
            return;
        }

        let job = crate::compiler::Job {
            sources: vec![],
            basis_lib_dir: Some(lib_dir),
            ..Default::default()
        };
        let settings = Settings::new();
        let mut parse_errors = ErrorReporter::new_silent();
        let Some(source_file) = crate::compiler::parse_sources(&job, &settings, &mut parse_errors)
        else {
            return;
        };
        let basis_decl = source_file
            .first()
            .filter(|located_decl| {
                matches!(&located_decl.node, crate::source::Decl::FfiStr(name, _, _) if name == "Basis")
            })
            .expect("parse_sources boot job must start with Basis FfiStr");
        let mut elaboration_context = ElabCtx::new();
        let elaboration_environment = Env::empty();
        let disjointness_environment = disjoint::empty_env();
        let (_decls, env_after_basis, denv_after_basis) = elab_decl(
            &mut elaboration_context,
            &elaboration_environment,
            &disjointness_environment,
            basis_decl,
        );
        let (_open_decls, env_open, _d_open) = elab_open(
            &mut elaboration_context,
            &env_after_basis,
            &denv_after_basis,
            &["Basis".to_string()],
            &basis_decl.span,
        );

        let span = basis_decl.span.clone();
        let fields_of_id = match env_open.lookup_c("fieldsOf") {
            VarLookup::Named(id, _) => id,
            _ => panic!("expected fieldsOf class in env after open Basis"),
        };
        let table_type = fresh_cunif(
            &env_open,
            span.clone(),
            Located::new(elab::Kind::Type, span.clone()),
            "table_type",
        );
        let table_type_cell = match &table_type.node {
            elab::Constructor::Unif(_, _, _, _, cell) => cell.clone(),
            _ => panic!("fresh_cunif should return a constructor unifier"),
        };
        let row_type = fresh_cunif(
            &env_open,
            span.clone(),
            Located::new(
                elab::Kind::Record(Box::new(Located::new(elab::Kind::Type, span.clone()))),
                span.clone(),
            ),
            "row_type",
        );
        let row_type_cell = match &row_type.node {
            elab::Constructor::Unif(_, _, _, _, cell) => cell.clone(),
            _ => panic!("fresh_cunif should return a constructor unifier"),
        };
        let class_goal = Located::new(
            elab::Constructor::App(
                Box::new(Located::new(
                    elab::Constructor::App(
                        Box::new(Located::new(
                            elab::Constructor::Named(fields_of_id),
                            span.clone(),
                        )),
                        Box::new(table_type),
                    ),
                    span.clone(),
                )),
                Box::new(row_type),
            ),
            span.clone(),
        );

        let resolved = resolve_class(&env_open, &class_goal, &span);
        assert!(
            resolved.is_some(),
            "fieldsOf_table should resolve fieldsOf ?t ?fs"
        );
        assert!(
            matches!(
                *crate::compiler_diagnostics::lock_for_compile(
                    table_type_cell.as_ref(),
                    "fieldsOf table_type regression",
                ),
                elab::CUnif::Known(_)
            ),
            "successful fieldsOf resolution should keep the solved table constructor binding",
        );
        assert!(
            matches!(
                *crate::compiler_diagnostics::lock_for_compile(
                    row_type_cell.as_ref(),
                    "fieldsOf row_type regression",
                ),
                elab::CUnif::Known(_)
            ),
            "successful fieldsOf resolution should keep the solved row constructor binding",
        );
    }

    #[test]
    fn basis_open_fields_of_resolution_survives_outer_constructor_binders() {
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let lib_dir = manifest_dir.join("lib/ur");
        if !lib_dir.join("basis.urs").is_file() {
            return;
        }

        let job = crate::compiler::Job {
            sources: vec![],
            basis_lib_dir: Some(lib_dir),
            ..Default::default()
        };
        let settings = Settings::new();
        let mut parse_errors = ErrorReporter::new_silent();
        let Some(source_file) = crate::compiler::parse_sources(&job, &settings, &mut parse_errors)
        else {
            return;
        };
        let basis_decl = source_file
            .first()
            .filter(|located_decl| {
                matches!(&located_decl.node, crate::source::Decl::FfiStr(name, _, _) if name == "Basis")
            })
            .expect("parse_sources boot job must start with Basis FfiStr");
        let mut elaboration_context = ElabCtx::new();
        let elaboration_environment = Env::empty();
        let disjointness_environment = disjoint::empty_env();
        let (_decls, env_after_basis, denv_after_basis) = elab_decl(
            &mut elaboration_context,
            &elaboration_environment,
            &disjointness_environment,
            basis_decl,
        );
        let (_open_decls, env_open, _d_open) = elab_open(
            &mut elaboration_context,
            &env_after_basis,
            &denv_after_basis,
            &["Basis".to_string()],
            &basis_decl.span,
        );

        let span = basis_decl.span.clone();
        let row_kind = Located::new(
            elab::Kind::Record(Box::new(Located::new(elab::Kind::Type, span.clone()))),
            span.clone(),
        );
        let key_row_kind = Located::new(
            elab::Kind::Record(Box::new(Located::new(
                elab::Kind::Record(Box::new(Located::new(elab::Kind::Unit, span.clone()))),
                span.clone(),
            ))),
            span.clone(),
        );
        let env_with_fs = env_open
            .clone()
            .push_c_rel("fs".to_string(), row_kind.clone());
        let env_with_binders = env_with_fs.push_c_rel("us".to_string(), key_row_kind);

        let table_type = Located::new(
            elab::Constructor::App(
                Box::new(Located::new(
                    elab::Constructor::App(
                        Box::new(match env_with_binders.lookup_c("sql_table") {
                            crate::elaborated::environment::VarLookup::Named(id, _) => {
                                Located::new(elab::Constructor::Named(id), span.clone())
                            }
                            other_lookup => panic!(
                                "expected sql_table constructor after open Basis, got {:?}",
                                other_lookup
                            ),
                        }),
                        Box::new(Located::new(elab::Constructor::Rel(1), span.clone())),
                    ),
                    span.clone(),
                )),
                Box::new(Located::new(elab::Constructor::Rel(0), span.clone())),
            ),
            span.clone(),
        );
        let env_with_table = env_with_binders.push_e_rel("t".to_string(), table_type.clone());
        let fields_of_id = match env_with_table.lookup_c("fieldsOf") {
            crate::elaborated::environment::VarLookup::Named(id, _) => id,
            other_lookup => panic!(
                "expected fieldsOf class in env after open Basis, got {:?}",
                other_lookup
            ),
        };
        let table_type_unif = fresh_cunif(
            &env_with_table,
            span.clone(),
            Located::new(elab::Kind::Type, span.clone()),
            "table_type",
        );
        let row_type_unif = fresh_cunif(&env_with_table, span.clone(), row_kind, "row_type");
        let class_goal = Located::new(
            elab::Constructor::App(
                Box::new(Located::new(
                    elab::Constructor::App(
                        Box::new(Located::new(
                            elab::Constructor::Named(fields_of_id),
                            span.clone(),
                        )),
                        Box::new(table_type_unif.clone()),
                    ),
                    span.clone(),
                )),
                Box::new(row_type_unif.clone()),
            ),
            span.clone(),
        );

        unify_cons(
            &mut elaboration_context,
            &env_with_table,
            &span,
            &table_type_unif,
            &table_type,
        )
        .expect("table type should unify with sql_table fs us");
        unify_cons(
            &mut elaboration_context,
            &env_with_table,
            &span,
            &row_type_unif,
            &Located::new(elab::Constructor::Rel(1), span.clone()),
        )
        .expect("row type should unify with outer fs binder");

        let fields_rules = env_with_table
            .classes()
            .get(&crate::elaborated::environment::ClassName::Named(
                fields_of_id,
            ))
            .expect("fieldsOf class should exist");
        let all_closed_heads: Vec<String> = fields_rules
            .closed_rules
            .iter()
            .map(|(quantifier_kinds, hypotheses, head, _)| {
                let (inst_head, _inst_hyps) =
                    instantiate_rule(&env_with_table, quantifier_kinds, hypotheses, head, &span);
                crate::elaborated::type_display::format_constructor(&inst_head)
            })
            .collect();
        let matched_closed_heads: Vec<String> = fields_rules
            .closed_rules
            .iter()
            .filter_map(|(quantifier_kinds, hypotheses, head, _)| {
                let (inst_head, _inst_hyps) =
                    instantiate_rule(&env_with_table, quantifier_kinds, hypotheses, head, &span);
                if try_match_class(
                    &env_with_table,
                    &class_goal,
                    &inst_head,
                    quantifier_kinds.len(),
                ) {
                    Some(crate::elaborated::type_display::format_constructor(
                        &inst_head,
                    ))
                } else {
                    None
                }
            })
            .collect();
        let first_head_unify_debug =
            fields_rules
                .closed_rules
                .first()
                .map(|(quantifier_kinds, hypotheses, head, _)| {
                    let (inst_head, _inst_hyps) = instantiate_rule(
                        &env_with_table,
                        quantifier_kinds,
                        hypotheses,
                        head,
                        &span,
                    );
                    match unify_cons(
                        &mut ElabCtx::new(),
                        &env_with_table,
                        &span,
                        &class_goal,
                        &inst_head,
                    ) {
                        Ok(()) => "ok".to_string(),
                        Err(unify_error) => format!("{unify_error:?}"),
                    }
                });
        assert!(
            resolve_class(&env_with_table, &class_goal, &span).is_some(),
            "fieldsOf_table should still resolve under outer constructor binders; class_goal={} all_closed_heads={all_closed_heads:?} matched_closed_heads={matched_closed_heads:?} first_head_unify_debug={first_head_unify_debug:?}",
            crate::elaborated::type_display::format_constructor(&class_goal),
        );
    }

    #[test]
    fn debug_boot_named_constructor_669_definition_shape() {
        const DEBUG_BOOT_NAMED_STACK_BYTES: usize = 32 * 1024 * 1024;
        let worker = std::thread::Builder::new()
            .name("debug_boot_named_constructor_669".into())
            .stack_size(DEBUG_BOOT_NAMED_STACK_BYTES);
        let handle = worker
            .spawn(debug_boot_named_constructor_669_definition_shape_body)
            .expect("spawn named-constructor debug worker");
        handle
            .join()
            .expect("named-constructor debug worker should not panic");
    }

    fn debug_boot_named_constructor_669_definition_shape_body() {
        if std::env::var("URWEB_DEBUG_BOOT_NAMED_669").ok().as_deref() != Some("1") {
            return;
        }

        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let lib_dir = manifest_dir.join("lib/ur");
        if !lib_dir.join("basis.urs").is_file() || !lib_dir.join("top.urs").is_file() {
            return;
        }

        let job = crate::compiler::Job {
            sources: vec![],
            basis_lib_dir: Some(lib_dir),
            ..Default::default()
        };
        let settings = crate::settings::Settings::default();
        let mut parse_errors = ErrorReporter::new_silent();
        let Some(source_file) = crate::compiler::parse_sources(&job, &settings, &mut parse_errors)
        else {
            panic!("boot parse should succeed for named-constructor debug");
        };
        let mut elaboration_context = ElabCtx::new();
        let mut elaboration_environment = Env::empty();
        let mut disjointness_environment = disjoint::empty_env();

        for decl in &source_file {
            let (_decls, new_env, new_denv) = elab_decl(
                &mut elaboration_context,
                &elaboration_environment,
                &disjointness_environment,
                decl,
            );
            elaboration_environment = new_env;
            disjointness_environment = new_denv;
            solve_constraints(&mut elaboration_context, &elaboration_environment);

            match &decl.node {
                crate::source::Decl::FfiStr(structure_name, _, _) if structure_name == "Basis" => {
                    let (_open_decls, opened_env, opened_denv) = elab_open(
                        &mut elaboration_context,
                        &elaboration_environment,
                        &disjointness_environment,
                        &["Basis".to_string()],
                        &decl.span,
                    );
                    elaboration_environment = opened_env;
                    disjointness_environment = opened_denv;
                }
                crate::source::Decl::Str(structure_name, ..)
                    if structure_name == "Top" || structure_name == "Folder" =>
                {
                    let (_open_decls, opened_env, opened_denv) = elab_open(
                        &mut elaboration_context,
                        &elaboration_environment,
                        &disjointness_environment,
                        &[structure_name.clone()],
                        &decl.span,
                    );
                    elaboration_environment = opened_env;
                    disjointness_environment = opened_denv;
                }
                _ => {}
            }
        }

        match elaboration_environment.lookup_c_named(669) {
            Ok((name, kind, definition)) => {
                eprintln!(
                    "boot named 669 name={} kind={} def={}",
                    name,
                    crate::elaborated::type_display::format_kind(kind),
                    definition
                        .as_ref()
                        .map(crate::elaborated::type_display::format_constructor)
                        .unwrap_or_else(|| "<none>".to_string()),
                );
            }
            Err(error) => {
                eprintln!("boot named 669 lookup error: {:?}", error);
            }
        }
    }

    /// Elaborate the real `lib/ur/basis.urs` + `lib/ur/top.urs` + `lib/ur/top.ur` and assert
    /// that no `ElabKindMismatch` diagnostics are emitted.
    ///
    /// **Note:** This does **not** mean the boot library fully typechecks — `elab_file` can still
    /// return `None` with many other elaboration errors until ML/Rust parity is complete. It only
    /// guards the specific kind-ascribing bug described below.
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

    /// Histogram of boot-only elaboration [`DiagnosticId`] counts (ratchet helper for ML parity).
    ///
    /// **Snapshot (full `lib/ur` boot):** counts drift with elaboration changes elsewhere in the tree;
    /// always re-measure with `URWEB_TEST_BOOT_HIST=1`. One recent baseline showed ~193 type errors with
    /// top ids `ElabTypeMismatch` (~170), `ElabApplicationNonFunction` (~12), `ElabUnresolvedDisjointness` (~8),
    /// `ElabUnboundVariable` (~3); metavariable `_` / `kindof`(`TCFun`) fixes removed the former `ElabUnboundTypeConstructor` cluster.
    /// `Exp::CApp` uses [`crate::elaborated::environment::hnorm_con_constructor_abstraction`].
    ///
    /// Large stack avoids overflow during elaboration. Set `URWEB_TEST_BOOT_HIST=1` to print the
    /// top buckets to stderr (never uses `Debug` on full error values — avoids stack overflow).
    /// Set `URWEB_TEST_BOOT_ERRORS=1` to print a short sample of `(DiagnosticId, line, column)` rows
    /// (paths and lines come from [`crate::parse::parse_ur`] / [`crate::parse::parse_urs`] span repair).
    /// Set `URWEB_TEST_BOOT_ELAB_MAX_ERRORS=N` to assert the boot type-error count stays ≤ `N` (ratchet).
    #[test]
    fn boot_elab_diagnostic_id_histogram() {
        const STACK: usize = 32 * 1024 * 1024;
        std::thread::Builder::new()
            .name("boot_elab_histogram".into())
            .stack_size(STACK)
            .spawn(boot_elab_diagnostic_id_histogram_body)
            .expect("spawn boot_elab_diagnostic_id_histogram")
            .join()
            .expect("boot_elab_diagnostic_id_histogram join");
    }

    /// Body of [`boot_elab_diagnostic_id_histogram`]: elaborates `lib/ur` boot with an empty user program,
    /// optionally prints histograms / samples to stderr from environment flags, and optionally asserts a type-error cap.
    ///
    /// # Environment
    ///
    /// * `URWEB_TEST_BOOT_HIST=1` — print sorted `DiagnosticId` buckets.
    /// * `URWEB_TEST_BOOT_ERRORS=1` — print the first 50 type errors with template `args`.
    /// * `URWEB_TEST_BOOT_APP_ERRORS=1` — print every `ElabApplicationNonFunction`, `ElabUnboundTypeConstructor`,
    ///   `ElabUnboundVariable`, and `ElabTypeMismatch` row (full boot list; can be long).
    /// * `URWEB_TEST_BOOT_ELAB_MAX_ERRORS=N` — assert the boot type-error count stays ≤ `N`.
    fn boot_elab_diagnostic_id_histogram_body() {
        use std::collections::HashMap;
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let lib_dir = manifest_dir.join("lib/ur");
        if !lib_dir.join("basis.urs").is_file() {
            return;
        }
        let job = crate::compiler::Job {
            sources: vec![],
            basis_lib_dir: Some(lib_dir),
            ..Default::default()
        };
        let settings = Settings::new();
        let mut parse_errors = ErrorReporter::new_silent();
        let Some(source_file) = crate::compiler::parse_sources(&job, &settings, &mut parse_errors)
        else {
            return;
        };
        if std::env::var("URWEB_TEST_BOOT_INCREMENTAL").ok().as_deref() == Some("1") {
            if let Some(crate::error_types::Located {
                node: crate::source::Decl::Str(_, _, _, top_body, _),
                ..
            }) = source_file
                .iter()
                .find(|decl| matches!(&decl.node, crate::source::Decl::Str(name, _, _, _, _) if name == "Top"))
            {
                let mut ctx = ElabCtx::new();
                let mut env = Env::empty();
                let mut denv = disjoint::empty_env();
                if let Some(basis_decl) = source_file.iter().find(|decl| {
                    matches!(&decl.node, crate::source::Decl::FfiStr(name, _, _) if name == "Basis")
                }) {
                    let (_basis_decls, basis_env, basis_denv) =
                        elab_decl(&mut ctx, &env, &denv, basis_decl);
                    env = basis_env;
                    denv = basis_denv;
                    let (_open_decls, open_env, open_denv) =
                        elab_open(&mut ctx, &env, &denv, &["Basis".to_string()], &basis_decl.span);
                    env = open_env;
                    denv = open_denv;
                }
                if let crate::source::Str::Const(top_decls) = &top_body.node {
                    let mut previous_error_count = ctx.errors.len();
                    for (decl_index, decl) in top_decls.iter().enumerate() {
                        if std::env::var("URWEB_TEST_BOOT_INCREMENTAL_DEBUG").ok().as_deref()
                            == Some("1")
                            && matches!(decl_index, 16 | 55 | 56 | 57 | 58 | 59 | 60)
                        {
                            let one_or_no_rows_type = match env.lookup_e("oneOrNoRows") {
                                crate::elaborated::environment::VarLookup::NotBound => {
                                    String::from("<not-bound>")
                                }
                                crate::elaborated::environment::VarLookup::Rel(_, type_constructor)
                                | crate::elaborated::environment::VarLookup::Named(
                                    _,
                                    type_constructor,
                                ) => crate::elaborated::type_display::format_constructor(
                                    &type_constructor,
                                ),
                            };
                            eprintln!(
                                "boot debug decl_index={decl_index} return_e={:?} query_e={:?} oneOrNoRows_e={:?} oneOrNoRows_ty={} show_c={:?} show_e={:?} mkShow={:?} read_e={:?} none_ctor={} some_ctor={}",
                                env.lookup_e("return"),
                                env.lookup_e("query"),
                                env.lookup_e("oneOrNoRows"),
                                one_or_no_rows_type,
                                env.lookup_c("show"),
                                env.lookup_e("show"),
                                env.lookup_e("mkShow"),
                                env.lookup_e("read"),
                                env.lookup_constructor("None").is_some(),
                                env.lookup_constructor("Some").is_some(),
                            );
                        }
                        let (_decls, new_env, new_denv) = elab_decl(&mut ctx, &env, &denv, decl);
                        env = new_env;
                        denv = new_denv;
                        let next_error_count = ctx.errors.len();
                        if next_error_count > previous_error_count {
                            eprintln!(
                                "boot incremental: decl_index={decl_index} line={} col={} new_errors={}",
                                decl.span.first.line,
                                decl.span.first.col,
                                next_error_count - previous_error_count
                            );
                            for (span, payload) in ctx.errors[previous_error_count..next_error_count].iter() {
                                eprintln!(
                                    "  {:?} {}:{}-{} args={:?}",
                                    payload.id, span.file, span.first.line, span.first.col, payload.args
                                );
                            }
                            previous_error_count = next_error_count;
                        }
                    }
                }
            }
        }
        let mut elab_errors = ErrorReporter::new_silent();
        let _elaborated_file = elab_file(source_file.clone(), &settings, &mut elab_errors);
        if std::env::var("URWEB_TEST_BOOT_ID_DEBUG").ok().as_deref() == Some("1") {
            let mut boot_env = Env::empty();
            let mut boot_denv = disjoint::empty_env();
            let mut boot_ctx = ElabCtx::new();
            if let Some(basis_decl) = source_file.iter().find(|decl| {
                matches!(&decl.node, crate::source::Decl::FfiStr(name, _, _) if name == "Basis")
            }) {
                let (_basis_decls, basis_env, basis_denv) =
                    elab_decl(&mut boot_ctx, &boot_env, &boot_denv, basis_decl);
                boot_env = basis_env;
                boot_denv = basis_denv;
                let (_open_decls, open_env, open_denv) = elab_open(
                    &mut boot_ctx,
                    &boot_env,
                    &boot_denv,
                    &["Basis".to_string()],
                    &basis_decl.span,
                );
                boot_env = open_env;
                boot_denv = open_denv;
            }
            for decl in &source_file {
                if matches!(&decl.node, crate::source::Decl::FfiStr(name, _, _) if name == "Basis")
                {
                    continue;
                }
                let (_decls, new_env, new_denv) =
                    elab_decl(&mut boot_ctx, &boot_env, &boot_denv, decl);
                boot_env = new_env;
                boot_denv = new_denv;
            }
            for target_id in [12_usize, 15, 113, 420, 669] {
                match boot_env.lookup_c_named(target_id) {
                    Ok((name, kind, definition)) => {
                        eprintln!(
                            "boot id debug constructor #{target_id}: name={name} kind={:?} has_def={}",
                            kind,
                            definition.is_some()
                        );
                    }
                    Err(_) => eprintln!("boot id debug constructor #{target_id}: <missing>"),
                }
                match boot_env.lookup_e_named(target_id) {
                    Ok((name, type_con)) => {
                        eprintln!(
                            "boot id debug expression #{target_id}: name={name} type={:?}",
                            type_con
                        );
                    }
                    Err(_) => eprintln!("boot id debug expression #{target_id}: <missing>"),
                }
            }
        }
        let mut histogram: HashMap<DiagnosticId, usize> = HashMap::new();
        for error in &elab_errors.errors {
            if let CompileError::TypeError { payload, .. } = error {
                *histogram.entry(payload.id).or_insert(0) += 1;
            }
        }
        if std::env::var("URWEB_TEST_BOOT_HIST").ok().as_deref() == Some("1") {
            let mut pairs: Vec<(usize, DiagnosticId)> =
                histogram.iter().map(|(id, count)| (*count, *id)).collect();
            pairs.sort_by(|a, b| b.0.cmp(&a.0));
            eprintln!(
                "boot-only elaboration: {} errors, {} distinct type diagnostic ids",
                elab_errors.errors.len(),
                histogram.len()
            );
            for (count, diagnostic_id) in pairs.iter().take(20) {
                eprintln!("  {count:5}  {diagnostic_id:?}");
            }
        }
        if std::env::var("URWEB_TEST_BOOT_ERRORS").ok().as_deref() == Some("1") {
            for err in elab_errors.errors.iter().take(50) {
                if let CompileError::TypeError { span, payload } = err {
                    eprintln!(
                        "  {:?}  {}:{}-{}  args={:?}",
                        payload.id, span.file, span.first.line, span.first.col, payload.args
                    );
                }
            }
        }
        if std::env::var("URWEB_TEST_BOOT_APP_ERRORS").ok().as_deref() == Some("1") {
            for err in elab_errors.errors.iter() {
                if let CompileError::TypeError { span, payload } = err {
                    let is_application_non_function =
                        payload.id == DiagnosticId::ElabApplicationNonFunction;
                    let is_unbound_type_constructor =
                        payload.id == DiagnosticId::ElabUnboundTypeConstructor;
                    let is_unbound_variable = payload.id == DiagnosticId::ElabUnboundVariable;
                    let is_type_mismatch = payload.id == DiagnosticId::ElabTypeMismatch;
                    if is_application_non_function
                        || is_unbound_type_constructor
                        || is_unbound_variable
                        || is_type_mismatch
                    {
                        eprintln!(
                            "  {:?}  {}:{}-{}  args={:?}",
                            payload.id, span.file, span.first.line, span.first.col, payload.args
                        );
                    }
                }
            }
        }
        if let Ok(raw) = std::env::var("URWEB_TEST_BOOT_ELAB_MAX_ERRORS") {
            if let Ok(max_errors) = raw.parse::<usize>() {
                let type_error_count = elab_errors
                    .errors
                    .iter()
                    .filter(|e| matches!(e, CompileError::TypeError { .. }))
                    .count();
                assert!(
                    type_error_count <= max_errors,
                    "boot-only elaboration: {type_error_count} type errors exceed URWEB_TEST_BOOT_ELAB_MAX_ERRORS={max_errors} \
                     (use URWEB_TEST_BOOT_HIST=1 to refresh buckets; lower the cap only when parity improves)",
                );
            }
        }
    }

    #[test]
    fn boot_top_prefix_through_show_option_decl_elaborates_without_errors() {
        const STACK: usize = 32 * 1024 * 1024;
        std::thread::Builder::new()
            .name("boot_top_prefix_show_option".into())
            .stack_size(STACK)
            .spawn(|| {
                let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
                let lib_dir = manifest_dir.join("lib/ur");
                if !lib_dir.join("basis.urs").is_file() {
                    return;
                }
                let job = crate::compiler::Job {
                    sources: vec![],
                    basis_lib_dir: Some(lib_dir),
                    ..Default::default()
                };
                let settings = Settings::new();
                let mut parse_errors = ErrorReporter::new_silent();
                let Some(source_file) =
                    crate::compiler::parse_sources(&job, &settings, &mut parse_errors)
                else {
                    return;
                };
                let Some(crate::error_types::Located {
                    node: crate::source::Decl::Str(_, _, _, top_body, _),
                    ..
                }) = source_file.iter().find(|decl| {
                    matches!(&decl.node, crate::source::Decl::Str(name, _, _, _, _) if name == "Top")
                }) else {
                    return;
                };

                let mut elaboration_context = ElabCtx::new();
                let mut elaboration_environment = Env::empty();
                let mut disjointness_environment = disjoint::empty_env();
                if let Some(basis_decl) = source_file.iter().find(|decl| {
                    matches!(&decl.node, crate::source::Decl::FfiStr(name, _, _) if name == "Basis")
                }) {
                    let (_basis_decls, basis_env, basis_denv) = elab_decl(
                        &mut elaboration_context,
                        &elaboration_environment,
                        &disjointness_environment,
                        basis_decl,
                    );
                    elaboration_environment = basis_env;
                    disjointness_environment = basis_denv;
                    let (_open_decls, open_env, open_denv) = elab_open(
                        &mut elaboration_context,
                        &elaboration_environment,
                        &disjointness_environment,
                        &["Basis".to_string()],
                        &basis_decl.span,
                    );
                    elaboration_environment = open_env;
                    disjointness_environment = open_denv;
                }

                let crate::source::Str::Const(top_decls) = &top_body.node else {
                    return;
                };
                for decl in top_decls.iter().take(17) {
                    let (_decls, new_env, new_denv) = elab_decl(
                        &mut elaboration_context,
                        &elaboration_environment,
                        &disjointness_environment,
                        decl,
                    );
                    elaboration_environment = new_env;
                    disjointness_environment = new_denv;
                }

                assert!(
                    elaboration_context.errors.is_empty(),
                    "boot Top prefix through show_option recorded errors: {:?}",
                    elaboration_context.errors
                );
            })
            .expect("spawn boot_top_prefix_through_show_option_decl_elaborates_without_errors")
            .join()
            .expect("boot_top_prefix_through_show_option_decl_elaborates_without_errors join");
    }

    #[test]
    fn boot_top_prefix_through_read_option_decl_elaborates_without_errors() {
        const STACK: usize = 32 * 1024 * 1024;
        std::thread::Builder::new()
            .name("boot_top_prefix_read_option".into())
            .stack_size(STACK)
            .spawn(|| {
                let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
                let lib_dir = manifest_dir.join("lib/ur");
                if !lib_dir.join("basis.urs").is_file() {
                    return;
                }
                let job = crate::compiler::Job {
                    sources: vec![],
                    basis_lib_dir: Some(lib_dir),
                    ..Default::default()
                };
                let settings = Settings::new();
                let mut parse_errors = ErrorReporter::new_silent();
                let Some(source_file) =
                    crate::compiler::parse_sources(&job, &settings, &mut parse_errors)
                else {
                    return;
                };
                let Some(crate::error_types::Located {
                    node: crate::source::Decl::Str(_, _, _, top_body, _),
                    ..
                }) = source_file.iter().find(|decl| {
                    matches!(&decl.node, crate::source::Decl::Str(name, _, _, _, _) if name == "Top")
                }) else {
                    return;
                };

                let mut elaboration_context = ElabCtx::new();
                let mut elaboration_environment = Env::empty();
                let mut disjointness_environment = disjoint::empty_env();
                if let Some(basis_decl) = source_file.iter().find(|decl| {
                    matches!(&decl.node, crate::source::Decl::FfiStr(name, _, _) if name == "Basis")
                }) {
                    let (_basis_decls, basis_env, basis_denv) = elab_decl(
                        &mut elaboration_context,
                        &elaboration_environment,
                        &disjointness_environment,
                        basis_decl,
                    );
                    elaboration_environment = basis_env;
                    disjointness_environment = basis_denv;
                    let (_open_decls, open_env, open_denv) = elab_open(
                        &mut elaboration_context,
                        &elaboration_environment,
                        &disjointness_environment,
                        &["Basis".to_string()],
                        &basis_decl.span,
                    );
                    elaboration_environment = open_env;
                    disjointness_environment = open_denv;
                }

                let crate::source::Str::Const(top_decls) = &top_body.node else {
                    return;
                };
                for decl in top_decls.iter().take(18) {
                    let (_decls, new_env, new_denv) = elab_decl(
                        &mut elaboration_context,
                        &elaboration_environment,
                        &disjointness_environment,
                        decl,
                    );
                    elaboration_environment = new_env;
                    disjointness_environment = new_denv;
                }

                assert!(
                    elaboration_context.errors.is_empty(),
                    "boot Top prefix through read_option recorded errors: {:?}",
                    elaboration_context.errors
                );
            })
            .expect("spawn boot_top_prefix_through_read_option_decl_elaborates_without_errors")
            .join()
            .expect("boot_top_prefix_through_read_option_decl_elaborates_without_errors join");
    }

    #[test]
    fn parse_fun_argument_annotation_keeps_constructor_application() {
        let mut errors = ErrorReporter::new_silent();
        let Some(file) = crate::parse::parse_ur(
            "parse_fun_argument_annotation_keeps_constructor_application.ur",
            "fun demo [t ::: Type] = fn opt : option t => opt\n",
            &mut errors,
            crate::dbms::ProjectDb::default(),
        ) else {
            panic!("parse_ur failed: {:?}", errors.errors);
        };
        let Some(crate::error_types::Located {
            node: crate::source::Decl::ValRec(bindings),
            ..
        }) = file.first()
        else {
            panic!("expected top-level fun desugared to valrec, got {:?}", file);
        };
        let (_, _, body) = bindings
            .first()
            .unwrap_or_else(|| panic!("expected one valrec binding, got {:?}", bindings));
        let crate::source::Exp::CAbs(_, _, _, inner_exp) = &body.node else {
            panic!("expected outer constructor abstraction, got {:?}", body);
        };
        let crate::source::Exp::Abs(_, None, case_body) = &inner_exp.node else {
            panic!(
                "expected parser-desugared lambda under fun body, got {:?}",
                inner_exp
            );
        };
        let crate::source::Exp::Case(_, branches) = &case_body.node else {
            panic!(
                "expected parser-desugared case under lambda body, got {:?}",
                case_body
            );
        };
        let Some((pattern, branch_expression)) = branches.first() else {
            panic!(
                "expected one parser-desugared case branch, got {:?}",
                branches
            );
        };
        let crate::source::Pat::Annot(_, annotation) = &pattern.node else {
            panic!(
                "expected annotated pattern under parser-desugared case, got {:?}",
                pattern
            );
        };
        assert!(
            matches!(&annotation.node, crate::source::Con::App(_, _)),
            "expected lambda annotation `option t` to parse as constructor application, got {:?}",
            annotation
        );
        assert!(
            !matches!(&branch_expression.node, crate::source::Exp::Abs(_, None, _)),
            "expected parser repair to remove bogus nested lambda, got {:?}",
            branch_expression
        );
    }

    #[test]
    fn parse_nested_case_branch_belongs_to_inner_case() {
        let mut errors = ErrorReporter::new_silent();
        let Some(file) = crate::parse::parse_ur(
            "parse_nested_case_branch_belongs_to_inner_case.ur",
            concat!(
                "fun demo [t ::: Type] (_ : read t) = fn s =>\n",
                "    case s of\n",
                "        \"\" => Some None\n",
                "      | _ => case read s of\n",
                "                 None => None\n",
                "               | v => Some v\n",
            ),
            &mut errors,
            crate::dbms::ProjectDb::default(),
        ) else {
            panic!("parse_ur failed: {:?}", errors.errors);
        };
        let Some(crate::error_types::Located {
            node: crate::source::Decl::ValRec(bindings),
            ..
        }) = file.first()
        else {
            panic!("expected top-level fun desugared to valrec, got {:?}", file);
        };
        let (_, _, body) = bindings
            .first()
            .unwrap_or_else(|| panic!("expected one valrec binding, got {:?}", bindings));
        let crate::source::Exp::CAbs(_, _, _, outer_exp) = &body.node else {
            panic!("expected outer constructor abstraction, got {:?}", body);
        };
        let crate::source::Exp::Abs(_, _, argument_case) = &outer_exp.node else {
            panic!(
                "expected outer value lambda under fun body, got {:?}",
                outer_exp
            );
        };
        let crate::source::Exp::Case(_, argument_branches) = &argument_case.node else {
            panic!(
                "expected parser-desugared annotated argument case under fun body, got {:?}",
                argument_case
            );
        };
        let Some((_, inner_exp)) = argument_branches.first() else {
            panic!(
                "expected one parser-desugared annotated argument branch, got {:?}",
                argument_branches
            );
        };
        let crate::source::Exp::Abs(_, _, case_exp) = &inner_exp.node else {
            panic!("expected value lambda under fun body, got {:?}", inner_exp);
        };
        let crate::source::Exp::Case(_, outer_branches) = &case_exp.node else {
            panic!("expected outer case under fun body, got {:?}", case_exp);
        };
        assert_eq!(
            outer_branches.len(),
            2,
            "expected outer case to keep two branches, got {:?}",
            outer_branches
        );
        let Some((_, inner_case_expression)) = outer_branches.get(1) else {
            panic!("expected second outer branch, got {:?}", outer_branches);
        };
        let crate::source::Exp::Case(_, inner_branches) = &inner_case_expression.node else {
            panic!(
                "expected second outer branch expression to remain an inner case, got {:?}",
                inner_case_expression
            );
        };
        assert_eq!(
            inner_branches.len(),
            2,
            "expected trailing branch to stay with inner case, got {:?}",
            inner_branches
        );
    }

    #[test]
    fn parse_field_postfix_binds_tighter_than_application() {
        let mut errors = ErrorReporter::new_silent();
        let Some(file) = crate::parse::parse_ur(
            "parse_field_postfix_binds_tighter_than_application.ur",
            "val _ = f r.nm\n",
            &mut errors,
            crate::db::ProjectDb::default(),
        ) else {
            panic!("parse_ur failed: {:?}", errors.errors);
        };
        let Some(crate::error_types::Located {
            node: crate::source::Decl::Val(_, expression),
            ..
        }) = file.first()
        else {
            panic!("expected val declaration, got {:?}", file);
        };
        let crate::source::Exp::App(function_expression, argument_expression) = &expression.node
        else {
            panic!("expected application expression, got {:?}", expression);
        };
        assert!(
            matches!(&function_expression.node, crate::source::Exp::Var(_, _, _)),
            "expected function head to stay as variable, got {:?}",
            function_expression
        );
        let crate::source::Exp::Field(field_base, _) = &argument_expression.node else {
            panic!(
                "expected field postfix to attach to application argument, got {:?}",
                argument_expression
            );
        };
        assert!(
            matches!(&field_base.node, crate::source::Exp::Var(_, _, _)),
            "expected field base to stay as variable, got {:?}",
            field_base
        );
    }

    #[test]
    fn local_mapu_constructor_decl_elaborates_without_boot() {
        let mut parse_errors = ErrorReporter::new_silent();
        let Some(file) = crate::parse::parse_ur(
            "local_mapu_constructor_decl_elaborates_without_boot.ur",
            concat!(
                "con mapU = K ==> fn f :: K => map (fn _ :: Unit => f)\n",
                "con localMap = fn tf1 :: Type => mapU tf1\n",
            ),
            &mut parse_errors,
            crate::db::ProjectDb::default(),
        ) else {
            panic!("parse_ur failed: {:?}", parse_errors.errors);
        };

        let mut elaboration_context = ElabCtx::new();
        let mut elaboration_environment = Env::empty();
        let mut disjointness_environment = disjoint::empty_env();
        for declaration in &file {
            let (_elaborated_decls, new_environment, new_disjointness_environment) = elab_decl(
                &mut elaboration_context,
                &elaboration_environment,
                &disjointness_environment,
                declaration,
            );
            elaboration_environment = new_environment;
            disjointness_environment = new_disjointness_environment;
        }

        assert!(
            elaboration_context.errors.is_empty(),
            "local mapU constructor elaboration recorded errors: {:?}",
            elaboration_context.errors
        );
    }

    #[test]
    fn local_mapu_module_signature_pair_elaborates_without_boot() {
        let temp_directory = tempfile::tempdir().expect("tempdir");
        let project_root = temp_directory.path();
        std::fs::write(project_root.join("app.urp"), "CoreMod\n").expect("write urp");
        std::fs::write(
            project_root.join("CoreMod.ur"),
            concat!(
                "con mapU = K ==> fn f :: K => map (fn _ :: Unit => f)\n",
                "con localMap = fn tf1 :: Type => mapU tf1\n",
            ),
        )
        .expect("write ur");
        std::fs::write(
            project_root.join("CoreMod.urs"),
            concat!(
                "con mapU = K ==> fn f :: K => map (fn _ :: Unit => f)\n",
                "con localMap = fn tf1 :: Type => mapU tf1\n",
            ),
        )
        .expect("write urs");

        let urp_path = project_root.join("app.urp");
        let mut settings = Settings::new();
        settings.boot_linking = false;
        let mut errors = ErrorReporter::new_silent();
        let mut job = crate::compiler::parse_urp(&urp_path).expect("parse urp");
        job.basis_lib_dir = None;
        let Some(source_file) = crate::compiler::parse_sources(&job, &settings, &mut errors) else {
            panic!("parse_sources failed: {errors:?}");
        };
        let elaborated_file = crate::compiler::elaborate(source_file, &settings, &mut errors);
        assert!(
            elaborated_file.is_some() && !errors.has_hard_errors(),
            "local mapU module/signature pair elaboration failed: {errors:?}"
        );
    }
}
