//! Ur/Web type checker — elaboration pass.
//!
//! Translates source AST (`source::`) to elaborated AST (`elaborated::`)
//! performing kind inference, type inference, module type-checking,
//! typeclass resolution, and disjointness constraint solving.
//!
//! Mirrors `elaborate.sml` (5264 lines).

#![allow(dead_code, unused_variables, unused_mut, unused_imports, clippy::all)]

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use crate::elaborated as elab;
use crate::elaborated::disjointness_analysis as disjoint;
use crate::elaborated::environment::{
    self as env_mod, edecl_binds, hnorm_sgn, new_named_id, pat_binds, pat_binds_n, ClassName,
    ClassRule, ClassRules, ConstructorInfo, DatatypeInfo, Env, VarLookup,
};
use crate::elaborated::type_operations::{
    self as type_ops, cons_eq_simple, hnorm_con, lift_con_in_con, lift_kind_in_con,
    lift_kind_in_kind, mlift_con_in_con, reduce_con, sub_con_in_con, sub_kind_in_con,
    sub_kind_in_kind,
};
use crate::error_types::{ErrorReporter, Located, Span};
use crate::primitives::Prim;
use crate::settings::Settings;
use crate::source::{self, FfiMode};

// ---------------------------------------------------------------------------
// Global state (mirrors SML refs)
// ---------------------------------------------------------------------------

/// Counter for fresh kind unification variables.
static KUNIF_COUNT: AtomicUsize = AtomicUsize::new(0);
/// Counter for fresh constructor unification variables.
static CUNIF_COUNT: AtomicUsize = AtomicUsize::new(0);

fn fresh_kunif_id() -> usize {
    KUNIF_COUNT.fetch_add(1, Ordering::Relaxed)
}

fn fresh_cunif_id() -> usize {
    CUNIF_COUNT.fetch_add(1, Ordering::Relaxed)
}

// ---------------------------------------------------------------------------
// Sentinel error values
// ---------------------------------------------------------------------------

fn kerror(span: Span) -> elab::LocatedKind {
    Located::new(elab::Kind::Error, span)
}

fn cerror(span: Span) -> elab::LocatedConstructor {
    Located::new(elab::Constructor::Error, span)
}

fn eerror(span: Span) -> elab::LocatedExpression {
    Located::new(elab::Expression::Error, span)
}

fn sgn_error(span: Span) -> elab::LocatedSignature {
    Located::new(elab::Signature::Error, span)
}

fn str_error(span: Span) -> elab::LocatedStructure {
    Located::new(elab::Structure::Error, span)
}

fn dummy_span() -> Span {
    Span::dummy()
}

// ---------------------------------------------------------------------------
// Fresh unification variables
// ---------------------------------------------------------------------------

fn fresh_kunif(span: Span, name: &str) -> elab::LocatedKind {
    let r = Arc::new(Mutex::new(elab::KUnif::Unknown));
    Located::new(elab::Kind::Unif(span.clone(), name.to_string(), r), span)
}

fn fresh_cunif(
    env: &Env,
    span: Span,
    kind: elab::LocatedKind,
    name: &str,
) -> elab::LocatedConstructor {
    let id = fresh_cunif_id();
    // nesting_level = number of relative constructor binders in env
    let nl = env.rel_c_len();
    let r = Arc::new(Mutex::new(elab::CUnif::Unknown));
    Located::new(
        elab::Constructor::Unif(nl, span.clone(), Box::new(kind), name.to_string(), r),
        span,
    )
}

// ---------------------------------------------------------------------------
// Kind occurs-check
// ---------------------------------------------------------------------------

fn occurs_kind(r: &elab::KUnifRef, k: &elab::LocatedKind) -> bool {
    match &k.node {
        elab::Kind::Unif(_, _, r2) => Arc::ptr_eq(r, r2),
        elab::Kind::TupleUnif(_, _, r2) => Arc::ptr_eq(r, r2),
        elab::Kind::Arrow(k1, k2) => occurs_kind(r, k1) || occurs_kind(r, k2),
        elab::Kind::Record(k1) => occurs_kind(r, k1),
        elab::Kind::Tuple(ks) => ks.iter().any(|ki| occurs_kind(r, ki)),
        elab::Kind::Fun(_, k1) => occurs_kind(r, k1),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Kind unification
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum KUnifyError {
    Incompatible(elab::LocatedKind, elab::LocatedKind),
    OccursCheck(elab::LocatedKind, elab::LocatedKind),
}

/// Unify two kinds, mutating unification variables in place.
/// Returns Ok(()) on success, Err on failure.
pub fn unify_kinds(
    env: &Env,
    k1: &elab::LocatedKind,
    k2: &elab::LocatedKind,
) -> Result<(), KUnifyError> {
    // Chase known unif vars first
    if let elab::Kind::Unif(_, _, r) = &k1.node {
        let guard = r.lock().unwrap();
        if let elab::KUnif::Known(inner) = &*guard {
            let inner = *inner.clone();
            drop(guard);
            return unify_kinds(env, &inner, k2);
        }
        drop(guard);
    }
    if let elab::Kind::Unif(_, _, r) = &k2.node {
        let guard = r.lock().unwrap();
        if let elab::KUnif::Known(inner) = &*guard {
            let inner = *inner.clone();
            drop(guard);
            return unify_kinds(env, k1, &inner);
        }
        drop(guard);
    }
    if let elab::Kind::TupleUnif(_, _, r) = &k1.node {
        let guard = r.lock().unwrap();
        if let elab::KUnif::Known(inner) = &*guard {
            let inner = *inner.clone();
            drop(guard);
            return unify_kinds(env, &inner, k2);
        }
        drop(guard);
    }
    if let elab::Kind::TupleUnif(_, _, r) = &k2.node {
        let guard = r.lock().unwrap();
        if let elab::KUnif::Known(inner) = &*guard {
            let inner = *inner.clone();
            drop(guard);
            return unify_kinds(env, k1, &inner);
        }
        drop(guard);
    }

    match (&k1.node, &k2.node) {
        (elab::Kind::Type, elab::Kind::Type) => Ok(()),
        (elab::Kind::Unit, elab::Kind::Unit) => Ok(()),
        (elab::Kind::Name, elab::Kind::Name) => Ok(()),
        (elab::Kind::Error, _) | (_, elab::Kind::Error) => Ok(()),

        (elab::Kind::Arrow(d1, r1), elab::Kind::Arrow(d2, r2)) => {
            unify_kinds(env, d1, d2)?;
            unify_kinds(env, r1, r2)
        }
        (elab::Kind::Record(k1i), elab::Kind::Record(k2i)) => unify_kinds(env, k1i, k2i),
        (elab::Kind::Tuple(ks1), elab::Kind::Tuple(ks2)) => {
            if ks1.len() != ks2.len() {
                return Err(KUnifyError::Incompatible(k1.clone(), k2.clone()));
            }
            for (ki1, ki2) in ks1.iter().zip(ks2.iter()) {
                unify_kinds(env, ki1, ki2)?;
            }
            Ok(())
        }
        (elab::Kind::Rel(n1), elab::Kind::Rel(n2)) => {
            if n1 == n2 {
                Ok(())
            } else {
                Err(KUnifyError::Incompatible(k1.clone(), k2.clone()))
            }
        }
        (elab::Kind::Fun(x, body1), elab::Kind::Fun(_, body2)) => {
            let env2 = env.clone().push_k_rel(x.clone());
            unify_kinds(&env2, body1, body2)
        }

        // Unif(r1) ~ Unif(r2): merge
        (elab::Kind::Unif(_, _, r1), elab::Kind::Unif(_, _, r2)) => {
            if Arc::ptr_eq(r1, r2) {
                return Ok(());
            }
            if occurs_kind(r1, k2) {
                return Err(KUnifyError::OccursCheck(k1.clone(), k2.clone()));
            }
            *r1.lock().unwrap() = elab::KUnif::Known(Box::new(k2.clone()));
            Ok(())
        }
        // Unif(r) ~ k2: solve
        (elab::Kind::Unif(_, _, r), _) => {
            if occurs_kind(r, k2) {
                return Err(KUnifyError::OccursCheck(k1.clone(), k2.clone()));
            }
            *r.lock().unwrap() = elab::KUnif::Known(Box::new(k2.clone()));
            Ok(())
        }
        // k1 ~ Unif(r): solve
        (_, elab::Kind::Unif(_, _, r)) => {
            if occurs_kind(r, k1) {
                return Err(KUnifyError::OccursCheck(k1.clone(), k2.clone()));
            }
            *r.lock().unwrap() = elab::KUnif::Known(Box::new(k1.clone()));
            Ok(())
        }

        // TupleUnif ~ Tuple: solve component-wise
        (elab::Kind::TupleUnif(_, nks, r), elab::Kind::Tuple(ks)) => {
            for (n, ki) in nks {
                let idx = n
                    .checked_sub(1)
                    .ok_or_else(|| KUnifyError::Incompatible(k1.clone(), k2.clone()))?;
                let target = ks
                    .get(idx)
                    .ok_or_else(|| KUnifyError::Incompatible(k1.clone(), k2.clone()))?;
                unify_kinds(env, ki, target)?;
            }
            *r.lock().unwrap() = elab::KUnif::Known(Box::new(k2.clone()));
            Ok(())
        }
        (elab::Kind::Tuple(ks), elab::Kind::TupleUnif(_, nks, r)) => {
            for (n, ki) in nks {
                let idx = n
                    .checked_sub(1)
                    .ok_or_else(|| KUnifyError::Incompatible(k1.clone(), k2.clone()))?;
                let target = ks
                    .get(idx)
                    .ok_or_else(|| KUnifyError::Incompatible(k1.clone(), k2.clone()))?;
                unify_kinds(env, target, ki)?;
            }
            *r.lock().unwrap() = elab::KUnif::Known(Box::new(k1.clone()));
            Ok(())
        }
        // TupleUnif ~ TupleUnif: merge
        (elab::Kind::TupleUnif(loc, nks1, r1), elab::Kind::TupleUnif(_, nks2, r2)) => {
            if Arc::ptr_eq(r1, r2) {
                return Ok(());
            }
            // Merge nks1 and nks2
            let mut merged: Vec<(usize, elab::LocatedKind)> = nks1.clone();
            for (n, ki2) in nks2 {
                if let Some((_, ki1)) = merged.iter_mut().find(|(m, _)| m == n) {
                    unify_kinds(env, ki1, ki2)?;
                } else {
                    merged.push((*n, ki2.clone()));
                }
            }
            let new_r = Arc::new(Mutex::new(elab::KUnif::Unknown));
            let new_k = Located::new(
                elab::Kind::TupleUnif(loc.clone(), merged, new_r),
                loc.clone(),
            );
            *r1.lock().unwrap() = elab::KUnif::Known(Box::new(new_k.clone()));
            *r2.lock().unwrap() = elab::KUnif::Known(Box::new(new_k));
            Ok(())
        }

        _ => Err(KUnifyError::Incompatible(k1.clone(), k2.clone())),
    }
}

fn check_kind(
    ctx: &mut ElabCtx,
    env: &Env,
    span: &Span,
    con: &elab::LocatedConstructor,
    got: &elab::LocatedKind,
    expected: &elab::LocatedKind,
) {
    if let Err(e) = unify_kinds(env, got, expected) {
        ctx.error(span.clone(), format!("Kind mismatch: {:?}", e));
    }
}

// ---------------------------------------------------------------------------
// Kind head-normalization
// ---------------------------------------------------------------------------

fn hnorm_kind(k: elab::LocatedKind) -> elab::LocatedKind {
    match &k.node {
        elab::Kind::Unif(_, _, r) => {
            let guard = r.lock().unwrap();
            if let elab::KUnif::Known(inner) = &*guard {
                let inner = *inner.clone();
                drop(guard);
                hnorm_kind(inner)
            } else {
                drop(guard);
                k
            }
        }
        elab::Kind::TupleUnif(_, _, r) => {
            let guard = r.lock().unwrap();
            if let elab::KUnif::Known(inner) = &*guard {
                let inner = *inner.clone();
                drop(guard);
                hnorm_kind(inner)
            } else {
                drop(guard);
                k
            }
        }
        _ => k,
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
        env: Env,
        goal: disjoint::Goal,
    },
    TypeClass {
        span: Span,
        env: Env,
        class: elab::LocatedConstructor,
        /// Where to write the resolved witness expression.
        result: Arc<Mutex<Option<elab::LocatedExpression>>>,
    },
}

/// Mutable state threaded through elaboration.
pub struct ElabCtx {
    /// Errors collected so far.
    pub errors: Vec<(Span, String)>,
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

    pub fn error(&mut self, span: Span, msg: String) {
        self.errors.push((span, msg));
    }

    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Look up a Basis type by name (e.g. "int", "float").
    fn basis_con(&self, env: &Env, name: &str, span: &Span) -> elab::LocatedConstructor {
        // Try to find Basis.name in the environment
        if let Some((str_id, _)) = env.lookup_str("Basis") {
            // project_con from the Basis structure
            if let Some(c) = project_con_from_str(env, *str_id, &[], name, span) {
                return c;
            }
        }
        cerror(span.clone())
    }
}

// ---------------------------------------------------------------------------
// Project a constructor/value/etc. from a named structure's signature
// ---------------------------------------------------------------------------

/// Project a constructor from a structure by name. Returns the constructor
/// application `ModProj(str_id, path, name)` if the sig contains it.
fn project_con_from_str(
    env: &Env,
    str_id: usize,
    path: &[String],
    name: &str,
    span: &Span,
) -> Option<elab::LocatedConstructor> {
    // Build ModProj constructor
    Some(Located::new(
        elab::Constructor::ModProj(str_id, path.to_vec(), name.to_string()),
        span.clone(),
    ))
}

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

fn sgi_find_sgn<'a>(
    sgis: &'a [elab::LocatedSignatureItem],
    x: &str,
) -> Option<&'a elab::SignatureItem> {
    for sgi in sgis {
        if let elab::SignatureItem::Signature(name, _, _) = &sgi.node {
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
        match &sgi.node {
            elab::SignatureItem::Datatype(dts) => {
                for dt in dts {
                    if dt.name == x {
                        return Some(dt);
                    }
                }
            }
            _ => {}
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Kind elaboration
// ---------------------------------------------------------------------------

pub fn elab_kind(ctx: &mut ElabCtx, env: &Env, k: &source::LocKind) -> elab::LocatedKind {
    let span = k.span.clone();
    match &k.node {
        source::Kind::Type => Located::new(elab::Kind::Type, span),
        source::Kind::Name => Located::new(elab::Kind::Name, span),
        source::Kind::Unit => Located::new(elab::Kind::Unit, span),
        source::Kind::Wild => fresh_kunif(span, "_"),
        source::Kind::Var(x) => {
            if let Some(idx) = env.lookup_k(x) {
                Located::new(elab::Kind::Rel(idx), span)
            } else {
                ctx.error(span.clone(), format!("Unbound kind variable `{}`", x));
                kerror(span)
            }
        }
        source::Kind::Arrow(k1, k2) => {
            let k1e = elab_kind(ctx, env, k1);
            let k2e = elab_kind(ctx, env, k2);
            Located::new(elab::Kind::Arrow(Box::new(k1e), Box::new(k2e)), span)
        }
        source::Kind::Record(k1) => {
            let k1e = elab_kind(ctx, env, k1);
            Located::new(elab::Kind::Record(Box::new(k1e)), span)
        }
        source::Kind::Tuple(ks) => {
            let kse: Vec<_> = ks.iter().map(|ki| elab_kind(ctx, env, ki)).collect();
            Located::new(elab::Kind::Tuple(kse), span)
        }
        source::Kind::Fun(x, body) => {
            let env2 = env.clone().push_k_rel(x.clone());
            let bodye = elab_kind(ctx, &env2, body);
            Located::new(elab::Kind::Fun(x.clone(), Box::new(bodye)), span)
        }
    }
}

// ---------------------------------------------------------------------------
// Constructor head elaboration (for implicit kind args)
// ---------------------------------------------------------------------------

/// Insert implicit kind applications at the head of a constructor.
/// Mirrors `elabConHead`.
fn elab_con_head(
    ctx: &mut ElabCtx,
    env: &Env,
    c: elab::LocatedConstructor,
    k: &elab::LocatedKind,
) -> (elab::LocatedConstructor, elab::LocatedKind) {
    let span = c.span.clone();
    let kn = hnorm_kind(k.clone());
    match &kn.node {
        elab::Kind::Fun(x, body) => {
            let ku = fresh_kunif(span.clone(), x);
            let new_c = Located::new(
                elab::Constructor::KApp(Box::new(c), Box::new(ku.clone())),
                span.clone(),
            );
            // substitute ku for Rel(0) in body
            let body_subst = sub_kind_in_kind(0, &ku, *body.clone());
            elab_con_head(ctx, env, new_c, &body_subst)
        }
        _ => (c, kn),
    }
}

// ---------------------------------------------------------------------------
// Constructor elaboration
// ---------------------------------------------------------------------------

pub fn elab_con(
    ctx: &mut ElabCtx,
    env: &Env,
    c: &source::LocCon,
) -> (elab::LocatedConstructor, elab::LocatedKind) {
    let span = c.span.clone();
    match &c.node {
        source::Con::Annot(c1, k) => {
            let ke = elab_kind(ctx, env, k);
            let (ce, ck) = elab_con(ctx, env, c1);
            check_kind(ctx, env, &span, &ce, &ck, &ke);
            (ce, ke)
        }
        source::Con::Wild(k) => {
            let ke = elab_kind(ctx, env, k);
            let cu = fresh_cunif(env, span.clone(), ke.clone(), "_");
            (cu, ke)
        }
        source::Con::Var(ms, x) => elab_con_var(ctx, env, ms, x, &span),
        source::Con::App(c1, c2) => {
            let (c1e, k1) = elab_con(ctx, env, c1);
            let kn = hnorm_kind(k1);
            match kn.node {
                elab::Kind::Arrow(kd, kr) => {
                    let (c2e, k2) = elab_con(ctx, env, c2);
                    check_kind(ctx, env, &c2.span, &c2e, &k2, &kd);
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
                    *r.lock().unwrap() = elab::KUnif::Known(Box::new(karrow));
                    let (c2e, k2) = elab_con(ctx, env, c2);
                    check_kind(ctx, env, &c2.span, &c2e, &k2, &kd);
                    let result =
                        Located::new(elab::Constructor::App(Box::new(c1e), Box::new(c2e)), span);
                    (result, kr)
                }
                _ => {
                    ctx.error(
                        span.clone(),
                        "Constructor application to non-arrow kind".to_string(),
                    );
                    (cerror(span.clone()), kerror(span))
                }
            }
        }
        source::Con::TFun(c1, c2) => {
            let (c1e, k1) = elab_con(ctx, env, c1);
            let (c2e, k2) = elab_con(ctx, env, c2);
            let ktype = Located::new(elab::Kind::Type, span.clone());
            check_kind(ctx, env, &c1.span, &c1e, &k1, &ktype);
            check_kind(ctx, env, &c2.span, &c2e, &k2, &ktype);
            let result = Located::new(elab::Constructor::TFun(Box::new(c1e), Box::new(c2e)), span);
            (result, ktype)
        }
        source::Con::TCFun(exp, x, k, body) => {
            let ke = elab_kind(ctx, env, k);
            let env2 = env.clone().push_c_rel(x.clone(), ke.clone());
            let (bodye, bodyke) = elab_con(ctx, &env2, body);
            let ktype = Located::new(elab::Kind::Type, span.clone());
            check_kind(ctx, env, &body.span, &bodye, &bodyke, &ktype);
            let exp_e = elab_explicitness(*exp);
            let result = Located::new(
                elab::Constructor::TCFun(exp_e, x.clone(), Box::new(ke), Box::new(bodye)),
                span,
            );
            (result, ktype)
        }
        source::Con::TRecord(r) => {
            let (re, rk) = elab_con(ctx, env, r);
            let kname = Located::new(elab::Kind::Name, span.clone());
            let ktype = Located::new(elab::Kind::Type, span.clone());
            let krow = Located::new(elab::Kind::Record(Box::new(ktype)), span.clone());
            check_kind(ctx, env, &r.span, &re, &rk, &krow);
            let result = Located::new(elab::Constructor::TRecord(Box::new(re)), span.clone());
            (result, Located::new(elab::Kind::Type, span))
        }
        source::Con::TDisjoint(c1, c2, body) => {
            let (c1e, k1) = elab_con(ctx, env, c1);
            let (c2e, k2) = elab_con(ctx, env, c2);
            let (bodye, bodyk) = elab_con(ctx, env, body);
            // c1 and c2 should each be rows; disjointness is about key sets
            // so their element kinds may differ independently.
            let ku1 = fresh_kunif(span.clone(), "_");
            let krow1 = Located::new(elab::Kind::Record(Box::new(ku1)), span.clone());
            check_kind(ctx, env, &c1.span, &c1e, &k1, &krow1);
            let ku2 = fresh_kunif(span.clone(), "_");
            let krow2 = Located::new(elab::Kind::Record(Box::new(ku2)), span.clone());
            check_kind(ctx, env, &c2.span, &c2e, &k2, &krow2);
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
                let (nce, nck) = elab_con(ctx, env, nc);
                let kname = Located::new(elab::Kind::Name, span.clone());
                check_kind(ctx, env, &nc.span, &nce, &nck, &kname);
                let (vce, vck) = elab_con(ctx, env, vc);
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
                check_kind(ctx, env, &vc.span, &vce, &vck, &ku);
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
            let (c1e, k1) = elab_con(ctx, env, c1);
            let (c2e, k2) = elab_con(ctx, env, c2);
            check_kind(ctx, env, &c2.span, &c2e, &k2, &k1);
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
                let (ce, ke) = elab_con(ctx, env, ci);
                ces.push(ce);
                ks.push(ke);
            }
            let kt = Located::new(elab::Kind::Tuple(ks), span.clone());
            let result = Located::new(elab::Constructor::Tuple(ces), span);
            (result, kt)
        }
        source::Con::Proj(c1, n) => {
            let (c1e, k1) = elab_con(ctx, env, c1);
            let kn = hnorm_kind(k1.clone());
            match &kn.node {
                elab::Kind::Tuple(ks) => {
                    let idx = n.checked_sub(1).unwrap_or(0);
                    let ki = ks.get(idx).cloned().unwrap_or_else(|| {
                        ctx.error(
                            span.clone(),
                            format!("Tuple projection out of bounds: {}", n),
                        );
                        kerror(span.clone())
                    });
                    let result = Located::new(elab::Constructor::Proj(Box::new(c1e), *n), span);
                    (result, ki)
                }
                elab::Kind::TupleUnif(_, nks, r) => {
                    // Create a fresh component for index n
                    let ku = fresh_kunif(span.clone(), &format!("_{}", n));
                    let mut new_nks = nks.clone();
                    new_nks.push((*n, ku.clone()));
                    let new_r = r.clone();
                    // Update the TupleUnif to record this projection
                    // (simplified: just return ku)
                    let result = Located::new(elab::Constructor::Proj(Box::new(c1e), *n), span);
                    (result, ku)
                }
                elab::Kind::Unif(_, _, r) => {
                    let ku = fresh_kunif(span.clone(), &format!("_{}", n));
                    // Solve the unif to a TupleUnif with this one component
                    let new_r2 = Arc::new(Mutex::new(elab::KUnif::Unknown));
                    let tku = Located::new(
                        elab::Kind::TupleUnif(span.clone(), vec![(*n, ku.clone())], new_r2),
                        span.clone(),
                    );
                    *r.lock().unwrap() = elab::KUnif::Known(Box::new(tku));
                    let result = Located::new(elab::Constructor::Proj(Box::new(c1e), *n), span);
                    (result, ku)
                }
                _ => {
                    ctx.error(
                        span.clone(),
                        "Tuple projection from non-tuple kind".to_string(),
                    );
                    (cerror(span.clone()), kerror(span))
                }
            }
        }
        source::Con::Abs(x, opt_k, body) => {
            let ke = match opt_k {
                Some(k) => elab_kind(ctx, env, k),
                None => fresh_kunif(span.clone(), x),
            };
            let env2 = env.clone().push_c_rel(x.clone(), ke.clone());
            let (bodye, bodyke) = elab_con(ctx, &env2, body);
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
            let env2 = env.clone().push_k_rel(x.clone());
            let (bodye, bodyke) = elab_con(ctx, &env2, body);
            let result = Located::new(
                elab::Constructor::KAbs(x.clone(), Box::new(bodye)),
                span.clone(),
            );
            // kind is Fun(x, bodyke)
            let rk = Located::new(elab::Kind::Fun(x.clone(), Box::new(bodyke)), span);
            (result, rk)
        }
        source::Con::TKFun(x, body) => {
            let env2 = env.clone().push_k_rel(x.clone());
            let (bodye, bodyke) = elab_con(ctx, &env2, body);
            let ktype = Located::new(elab::Kind::Type, span.clone());
            check_kind(ctx, env, &body.span, &bodye, &bodyke, &ktype);
            let result = Located::new(elab::Constructor::TKFun(x.clone(), Box::new(bodye)), span);
            (result, ktype)
        }
    }
}

fn elab_con_var(
    ctx: &mut ElabCtx,
    env: &Env,
    ms: &[String],
    x: &str,
    span: &Span,
) -> (elab::LocatedConstructor, elab::LocatedKind) {
    if ms.is_empty() {
        match env.lookup_c(x) {
            VarLookup::Rel(idx, k) => {
                let c = Located::new(elab::Constructor::Rel(idx), span.clone());
                let (c2, k2) = elab_con_head(ctx, env, c, &k);
                return (c2, k2);
            }
            VarLookup::Named(id, k) => {
                let c = Located::new(elab::Constructor::Named(id), span.clone());
                let (c2, k2) = elab_con_head(ctx, env, c, &k);
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
                ctx.error(span.clone(), format!("Unbound type constructor `{}`", x));
                return (cerror(span.clone()), kerror(span.clone()));
            }
        }
    }

    // Qualified: Ms.x
    // Chase the module path
    let (str_id, mut sgn_items) = match resolve_module_path(ctx, env, ms, span) {
        Some(x) => x,
        None => return (cerror(span.clone()), kerror(span.clone())),
    };

    // Now find x in the signature items
    if let Some(sgi) = sgi_find_con(&sgn_items, x) {
        match sgi {
            elab::SignatureItem::Constructor(_, id, k, _)
            | elab::SignatureItem::ConAbs(_, id, k) => {
                // Project with remaining path empty since we're done
                let c = Located::new(
                    elab::Constructor::ModProj(str_id, ms[..ms.len()].to_vec(), x.to_string()),
                    span.clone(),
                );
                let (c2, k2) = elab_con_head(ctx, env, c, k);
                return (c2, k2);
            }
            elab::SignatureItem::ClassAbs(_, id, k) | elab::SignatureItem::Class(_, id, k, _) => {
                let c = Located::new(
                    elab::Constructor::ModProj(str_id, ms[..ms.len()].to_vec(), x.to_string()),
                    span.clone(),
                );
                // Class kind: k -> Type
                let ktype = Located::new(elab::Kind::Type, span.clone());
                let class_k = Located::new(
                    elab::Kind::Arrow(Box::new(k.clone()), Box::new(ktype)),
                    span.clone(),
                );
                let (c2, k2) = elab_con_head(ctx, env, c, &class_k);
                return (c2, k2);
            }
            _ => {}
        }
    }

    ctx.error(span.clone(), format!("Unbound type constructor `{}`", x));
    (cerror(span.clone()), kerror(span.clone()))
}

/// Resolve a module path `[M1, M2, ...]` to `(str_id, sig_items)`.
fn resolve_module_path(
    ctx: &mut ElabCtx,
    env: &Env,
    ms: &[String],
    span: &Span,
) -> Option<(usize, Vec<elab::LocatedSignatureItem>)> {
    if ms.is_empty() {
        return None;
    }
    let first = &ms[0];
    let (mut str_id, mut sgn) = match env.lookup_str(first) {
        Some((sid, s)) => (*sid, s.clone()),
        None => {
            ctx.error(span.clone(), format!("Unbound module `{}`", first));
            return None;
        }
    };

    // Chase remaining path components
    let hsgn = hnorm_sgn(env, &sgn);
    let mut items = match &hsgn.node {
        elab::Signature::Const(sgis) => sgis.clone(),
        _ => {
            ctx.error(
                span.clone(),
                format!("Module `{}` has non-const signature", first),
            );
            return None;
        }
    };

    for m in &ms[1..] {
        if let Some(sgi) = sgi_find_str(&items, m) {
            match sgi {
                elab::SignatureItem::Structure(_, _, id, inner_sgn) => {
                    str_id = *id;
                    sgn = inner_sgn.clone();
                    let hn = hnorm_sgn(env, &sgn);
                    items = match &hn.node {
                        elab::Signature::Const(sgis) => sgis.clone(),
                        _ => {
                            ctx.error(
                                span.clone(),
                                format!("Sub-module `{}` has non-const signature", m),
                            );
                            return None;
                        }
                    };
                }
                _ => {
                    ctx.error(span.clone(), format!("`{}` is not a structure", m));
                    return None;
                }
            }
        } else {
            ctx.error(span.clone(), format!("Unbound module `{}`", m));
            return None;
        }
    }

    Some((str_id, items))
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

pub fn kindof(ctx: &mut ElabCtx, env: &Env, c: &elab::LocatedConstructor) -> elab::LocatedKind {
    let span = c.span.clone();
    match &c.node {
        elab::Constructor::TFun(_, _)
        | elab::Constructor::TRecord(_)
        | elab::Constructor::TDisjoint(_, _, _)
        | elab::Constructor::TKFun(_, _) => Located::new(elab::Kind::Type, span),
        elab::Constructor::TCFun(_, _, k, body) => {
            let env2 = env.clone().push_c_rel("_".to_string(), *k.clone());
            let bodyke = kindof(ctx, &env2, body);
            Located::new(elab::Kind::Type, span)
        }
        elab::Constructor::Rel(n) => match env.lookup_c_rel(*n) {
            Ok((_, k)) => k.clone(),
            Err(_) => {
                ctx.error(span.clone(), format!("Unbound constructor Rel({})", n));
                kerror(span)
            }
        },
        elab::Constructor::Named(id) => match env.lookup_c_named(*id) {
            Ok((_, k, _)) => k.clone(),
            Err(_) => {
                ctx.error(span.clone(), format!("Unbound named constructor {}", id));
                kerror(span)
            }
        },
        elab::Constructor::ModProj(str_id, path, name) => {
            // Look up in the structure's signature
            if let Ok((_, sgn)) = env.lookup_str_named(*str_id) {
                let items = get_sgn_const_items(env, &sgn);
                if let Some(sgi) = sgi_find_con(&items, name) {
                    match sgi {
                        elab::SignatureItem::ConAbs(_, _, k)
                        | elab::SignatureItem::Constructor(_, _, k, _) => return k.clone(),
                        elab::SignatureItem::ClassAbs(_, _, k)
                        | elab::SignatureItem::Class(_, _, k, _) => {
                            let ktype = Located::new(elab::Kind::Type, span.clone());
                            return Located::new(
                                elab::Kind::Arrow(Box::new(k.clone()), Box::new(ktype)),
                                span,
                            );
                        }
                        _ => {}
                    }
                }
            }
            fresh_kunif(span, name)
        }
        elab::Constructor::App(f, arg) => {
            let kf = kindof(ctx, env, f);
            let kfn = hnorm_kind(kf);
            match kfn.node {
                elab::Kind::Arrow(_, kr) => *kr,
                _ => {
                    ctx.error(span.clone(), "Application to non-arrow kind".to_string());
                    kerror(span)
                }
            }
        }
        elab::Constructor::Abs(x, k, body) => {
            let env2 = env.clone().push_c_rel(x.clone(), *k.clone());
            let bodyke = kindof(ctx, &env2, body);
            Located::new(elab::Kind::Arrow(k.clone(), Box::new(bodyke)), span)
        }
        elab::Constructor::KAbs(x, body) => {
            let env2 = env.clone().push_k_rel(x.clone());
            let bodyke = kindof(ctx, &env2, body);
            Located::new(elab::Kind::Fun(x.clone(), Box::new(bodyke)), span)
        }
        elab::Constructor::KApp(f, k) => {
            let kf = kindof(ctx, env, f);
            let kfn = hnorm_kind(kf);
            match kfn.node {
                elab::Kind::Fun(_, body) => sub_kind_in_kind(0, k, *body),
                _ => {
                    ctx.error(span.clone(), "KApp to non-KFun kind".to_string());
                    kerror(span)
                }
            }
        }
        elab::Constructor::Name(_) => Located::new(elab::Kind::Name, span),
        elab::Constructor::Record(k, _) => Located::new(elab::Kind::Record(k.clone()), span),
        elab::Constructor::Concat(c1, _) => kindof(ctx, env, c1),
        elab::Constructor::Map(k1, k2) => {
            let ktype = Located::new(elab::Kind::Type, span.clone());
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
            let ks: Vec<_> = cs.iter().map(|ci| kindof(ctx, env, ci)).collect();
            Located::new(elab::Kind::Tuple(ks), span)
        }
        elab::Constructor::Proj(c, n) => {
            let kc = kindof(ctx, env, c);
            let kcn = hnorm_kind(kc);
            match kcn.node {
                elab::Kind::Tuple(ks) => {
                    let idx = n.checked_sub(1).unwrap_or(0);
                    ks.get(idx).cloned().unwrap_or_else(|| kerror(span))
                }
                _ => kerror(span),
            }
        }
        elab::Constructor::Error => kerror(span),
        elab::Constructor::Unif(_, _, k, _, _) => *k.clone(),
    }
}

fn get_sgn_const_items(env: &Env, sgn: &elab::LocatedSignature) -> Vec<elab::LocatedSignatureItem> {
    let hn = hnorm_sgn(env, sgn);
    match hn.node {
        elab::Signature::Const(items) => items,
        _ => vec![],
    }
}

// ---------------------------------------------------------------------------
// Constructor unification (unifyCons)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum CUnifyError {
    Incompatible(elab::LocatedConstructor, elab::LocatedConstructor),
    OccursCheck,
    KindMismatch(KUnifyError),
    Undetermined,
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
fn record_summary(c: elab::LocatedConstructor) -> RecordSummary {
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
            let mut s1 = record_summary(*c1);
            let s2 = record_summary(*c2);
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
        _ => RecordSummary {
            fields: vec![],
            unifs: vec![],
            others: vec![cn],
        },
    }
}

/// Try to unify two constructors, mutating unification variables in place.
pub fn unify_cons(
    ctx: &mut ElabCtx,
    env: &Env,
    span: &Span,
    c1: &elab::LocatedConstructor,
    c2: &elab::LocatedConstructor,
) -> Result<(), CUnifyError> {
    unify_cons_inner(ctx, env, span, c1, c2, 0)
}

fn unify_cons_inner(
    ctx: &mut ElabCtx,
    env: &Env,
    span: &Span,
    c1: &elab::LocatedConstructor,
    c2: &elab::LocatedConstructor,
    depth: usize,
) -> Result<(), CUnifyError> {
    if depth > 100 {
        return Err(CUnifyError::Undetermined);
    }

    // Chase known unif vars first
    let c1n = hnorm_con(c1.clone());
    let c2n = hnorm_con(c2.clone());

    // Quick structural equality check
    if cons_eq_simple(&c1n, &c2n) {
        return Ok(());
    }

    match (&c1n.node, &c2n.node) {
        (elab::Constructor::Error, _) | (_, elab::Constructor::Error) => return Ok(()),

        (elab::Constructor::Rel(n1), elab::Constructor::Rel(n2)) => {
            if n1 == n2 {
                return Ok(());
            }
            return Err(CUnifyError::Incompatible(c1n, c2n));
        }
        (elab::Constructor::Named(n1), elab::Constructor::Named(n2)) => {
            if n1 == n2 {
                return Ok(());
            }
            // Try to unfold named constructors
            if let Ok((_, _, Some(def1))) = env.lookup_c_named(*n1) {
                return unify_cons_inner(ctx, env, span, &def1.clone(), c2, depth + 1);
            }
            if let Ok((_, _, Some(def2))) = env.lookup_c_named(*n2) {
                return unify_cons_inner(ctx, env, span, c1, &def2.clone(), depth + 1);
            }
            return Err(CUnifyError::Incompatible(c1n, c2n));
        }
        (elab::Constructor::Named(n1), _) => {
            if let Ok((_, _, Some(def1))) = env.lookup_c_named(*n1) {
                return unify_cons_inner(ctx, env, span, &def1.clone(), c2, depth + 1);
            }
            // Try reducing
            let rc1 = reduce_con(c1n.clone());
            if !cons_eq_simple(&rc1, &c1n) {
                return unify_cons_inner(ctx, env, span, &rc1, c2, depth + 1);
            }
            return Err(CUnifyError::Incompatible(c1n, c2n));
        }
        (_, elab::Constructor::Named(n2)) => {
            if let Ok((_, _, Some(def2))) = env.lookup_c_named(*n2) {
                return unify_cons_inner(ctx, env, span, c1, &def2.clone(), depth + 1);
            }
            let rc2 = reduce_con(c2n.clone());
            if !cons_eq_simple(&rc2, &c2n) {
                return unify_cons_inner(ctx, env, span, c1, &rc2, depth + 1);
            }
            return Err(CUnifyError::Incompatible(c1n, c2n));
        }

        // Unification variable solving
        (
            elab::Constructor::Unif(nl1, _, k1, _, r1),
            elab::Constructor::Unif(nl2, _, k2, _, r2),
        ) => {
            if Arc::ptr_eq(r1, r2) {
                return Ok(());
            }
            // Solve r1 := c2n (adjusted for nesting)
            let adjusted = mlift_con_in_con(*nl1, c2n.clone());
            *r1.lock().unwrap() = elab::CUnif::Known(Box::new(adjusted));
            return Ok(());
        }
        (elab::Constructor::Unif(nl, _, k, _, r), _) => {
            let adjusted = mlift_con_in_con(*nl, c2n.clone());
            *r.lock().unwrap() = elab::CUnif::Known(Box::new(adjusted));
            return Ok(());
        }
        (_, elab::Constructor::Unif(nl, _, k, _, r)) => {
            let adjusted = mlift_con_in_con(*nl, c1n.clone());
            *r.lock().unwrap() = elab::CUnif::Known(Box::new(adjusted));
            return Ok(());
        }

        // Structural cases
        (elab::Constructor::TFun(d1, r1), elab::Constructor::TFun(d2, r2)) => {
            unify_cons_inner(ctx, env, span, d1, d2, depth + 1)?;
            unify_cons_inner(ctx, env, span, r1, r2, depth + 1)
        }
        (elab::Constructor::TCFun(e1, x1, k1, b1), elab::Constructor::TCFun(e2, _, k2, b2)) => {
            if e1 != e2 {
                return Err(CUnifyError::Incompatible(c1n, c2n));
            }
            unify_kinds(env, k1, k2).map_err(CUnifyError::KindMismatch)?;
            let env2 = env.clone().push_c_rel(x1.clone(), *k1.clone());
            unify_cons_inner(ctx, &env2, span, b1, b2, depth + 1)
        }
        (elab::Constructor::TRecord(r1), elab::Constructor::TRecord(r2)) => {
            unify_cons_inner(ctx, env, span, r1, r2, depth + 1)
        }
        (elab::Constructor::TDisjoint(_, _, b1), _) => {
            unify_cons_inner(ctx, env, span, b1, c2, depth + 1)
        }
        (_, elab::Constructor::TDisjoint(_, _, b2)) => {
            unify_cons_inner(ctx, env, span, c1, b2, depth + 1)
        }
        (elab::Constructor::App(f1, a1), elab::Constructor::App(f2, a2)) => {
            unify_cons_inner(ctx, env, span, f1, f2, depth + 1)?;
            unify_cons_inner(ctx, env, span, a1, a2, depth + 1)
        }
        (elab::Constructor::Abs(x1, k1, b1), elab::Constructor::Abs(_, k2, b2)) => {
            unify_kinds(env, k1, k2).map_err(CUnifyError::KindMismatch)?;
            let env2 = env.clone().push_c_rel(x1.clone(), *k1.clone());
            unify_cons_inner(ctx, &env2, span, b1, b2, depth + 1)
        }
        (elab::Constructor::KAbs(x1, b1), elab::Constructor::KAbs(_, b2)) => {
            let env2 = env.clone().push_k_rel(x1.clone());
            unify_cons_inner(ctx, &env2, span, b1, b2, depth + 1)
        }
        (elab::Constructor::KApp(f1, k1), elab::Constructor::KApp(f2, k2)) => {
            unify_cons_inner(ctx, env, span, f1, f2, depth + 1)?;
            unify_kinds(env, k1, k2).map_err(CUnifyError::KindMismatch)
        }
        (elab::Constructor::Name(s1), elab::Constructor::Name(s2)) => {
            if s1.to_lowercase() == s2.to_lowercase() {
                Ok(())
            } else {
                Err(CUnifyError::Incompatible(c1n, c2n))
            }
        }
        (elab::Constructor::Unit, elab::Constructor::Unit) => Ok(()),
        (elab::Constructor::Tuple(cs1), elab::Constructor::Tuple(cs2)) => {
            if cs1.len() != cs2.len() {
                return Err(CUnifyError::Incompatible(c1n, c2n));
            }
            for (ci1, ci2) in cs1.iter().zip(cs2.iter()) {
                unify_cons_inner(ctx, env, span, ci1, ci2, depth + 1)?;
            }
            Ok(())
        }
        (elab::Constructor::Proj(c1i, n1), elab::Constructor::Proj(c2i, n2)) => {
            if n1 != n2 {
                return Err(CUnifyError::Incompatible(c1n, c2n));
            }
            unify_cons_inner(ctx, env, span, c1i, c2i, depth + 1)
        }
        // Row constructors: try record summary unification
        _ => {
            // Try reduction before giving up
            let rc1 = reduce_con(c1n.clone());
            let rc2 = reduce_con(c2n.clone());
            if !cons_eq_simple(&rc1, &c1n) || !cons_eq_simple(&rc2, &c2n) {
                return unify_cons_inner(ctx, env, span, &rc1, &rc2, depth + 1);
            }
            // Row unification via summaries
            unify_rows(ctx, env, span, &c1n, &c2n, depth)
        }
    }
}

/// Row-specific unification (for Record / Concat / Unif tails).
fn unify_rows(
    ctx: &mut ElabCtx,
    env: &Env,
    span: &Span,
    c1: &elab::LocatedConstructor,
    c2: &elab::LocatedConstructor,
    depth: usize,
) -> Result<(), CUnifyError> {
    let s1 = record_summary(c1.clone());
    let s2 = record_summary(c2.clone());

    // If both are fully known (no unifs), check field by field
    if s1.unifs.is_empty() && s2.unifs.is_empty() && s1.others.is_empty() && s2.others.is_empty() {
        if s1.fields.len() != s2.fields.len() {
            return Err(CUnifyError::Incompatible(c1.clone(), c2.clone()));
        }
        let mut fields2 = s2.fields.clone();
        for (f1, v1) in &s1.fields {
            if let Some(pos) = fields2
                .iter()
                .position(|(f2, _)| f1.to_lowercase() == f2.to_lowercase())
            {
                let (_, v2) = fields2.remove(pos);
                unify_cons_inner(ctx, env, span, v1, &v2, depth + 1)?;
            } else {
                return Err(CUnifyError::Incompatible(c1.clone(), c2.clone()));
            }
        }
        return Ok(());
    }

    // If either side has exactly one unif and no others, solve it
    if s1.unifs.len() == 1 && s1.others.is_empty() && s2.unifs.is_empty() && s2.others.is_empty() {
        let (r, nl) = &s1.unifs[0];
        // Build the solution: c2 minus s1.fields
        let mut remaining = s2.fields.clone();
        for (f, _) in &s1.fields {
            remaining.retain(|(f2, _)| f.to_lowercase() != f2.to_lowercase());
        }
        let solution = fields_to_row(&remaining, span, &c2.span);
        let adjusted = mlift_con_in_con(*nl, solution);
        *r.lock().unwrap() = elab::CUnif::Known(Box::new(adjusted));
        return Ok(());
    }
    if s2.unifs.len() == 1 && s2.others.is_empty() && s1.unifs.is_empty() && s1.others.is_empty() {
        let (r, nl) = &s2.unifs[0];
        let mut remaining = s1.fields.clone();
        for (f, _) in &s2.fields {
            remaining.retain(|(f2, _)| f.to_lowercase() != f2.to_lowercase());
        }
        let solution = fields_to_row(&remaining, span, &c1.span);
        let adjusted = mlift_con_in_con(*nl, solution);
        *r.lock().unwrap() = elab::CUnif::Known(Box::new(adjusted));
        return Ok(());
    }

    // Otherwise, delay if mayDelay is set, else fail
    if ctx.may_delay {
        // Leave for later constraint solving
        return Ok(());
    }
    Err(CUnifyError::Incompatible(c1.clone(), c2.clone()))
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
    ctx: &mut ElabCtx,
    env: &Env,
    span: &Span,
    got: &elab::LocatedConstructor,
    expected: &elab::LocatedConstructor,
) {
    if let Err(e) = unify_cons(ctx, env, span, got, expected) {
        ctx.error(span.clone(), format!("Type mismatch: {:?}", e));
    }
}

// ---------------------------------------------------------------------------
// Pattern elaboration
// ---------------------------------------------------------------------------

pub fn elab_pat(
    ctx: &mut ElabCtx,
    env: &Env,
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
            let new_env = env.clone().push_e_rel(x.clone(), expected_type.clone());
            (pat, new_env)
        }
        source::Pat::Prim(prim) => {
            let prim_type = prim_con(ctx, env, prim, &span);
            check_con(ctx, env, &span, &prim_type, expected_type);
            let pat = Located::new(elab::Pattern::Prim(prim.clone()), span);
            (pat, env.clone())
        }
        source::Pat::Con(ms, x, arg_opt) => {
            elab_pat_con(ctx, env, ms, x, arg_opt.as_deref(), expected_type, &span)
        }
        source::Pat::Record(fields, is_open) => {
            elab_pat_record(ctx, env, fields, *is_open, expected_type, &span)
        }
        source::Pat::Annot(inner_p, annot_con) => {
            let (annot_ce, _) = elab_con(ctx, env, annot_con);
            check_con(ctx, env, &span, &annot_ce, expected_type);
            elab_pat(ctx, env, inner_p, &annot_ce)
        }
    }
}

fn elab_pat_con(
    ctx: &mut ElabCtx,
    env: &Env,
    ms: &[String],
    x: &str,
    arg_opt: Option<&source::LocPat>,
    expected_type: &elab::LocatedConstructor,
    span: &Span,
) -> (elab::LocatedPattern, Env) {
    // Look up the constructor
    let constr_info = if ms.is_empty() {
        env.lookup_constructor(x).cloned()
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
            .map(|_| fresh_cunif(env, span.clone(), ktype.clone(), "_"))
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

        check_con(ctx, env, span, &dt_con, expected_type);

        // If constructor takes an argument, elaborate it
        let (arg_pat_opt, new_env) = if let Some(at) = arg_type_opt {
            // Substitute type_args into at
            let mut at2 = at;
            for (i, ta) in type_args.iter().enumerate() {
                let idx = type_params.len() - 1 - i;
                at2 = match sub_con_in_con(idx, ta, at2) {
                    Ok(c) => c,
                    Err(_) => cerror(span.clone()),
                };
            }
            if let Some(ap) = arg_opt {
                let (ap_e, new_env) = elab_pat(ctx, env, ap, &at2);
                (Some(Box::new(ap_e)), new_env)
            } else {
                ctx.error(
                    span.clone(),
                    format!("Constructor `{}` expects an argument", x),
                );
                (None, env.clone())
            }
        } else {
            if arg_opt.is_some() {
                ctx.error(
                    span.clone(),
                    format!("Constructor `{}` does not take an argument", x),
                );
            }
            (None, env.clone())
        };

        let pat_con = elab::PatternConstructor::Var(con_id);
        let pat = Located::new(
            elab::Pattern::Constructor(dk, pat_con, type_args, arg_pat_opt),
            span.clone(),
        );
        (pat, new_env)
    } else {
        ctx.error(span.clone(), format!("Unbound constructor `{}`", x));
        let pat = Located::new(
            elab::Pattern::Var("_".to_string(), expected_type.clone()),
            span.clone(),
        );
        (pat, env.clone())
    }
}

fn elab_pat_record(
    ctx: &mut ElabCtx,
    env: &Env,
    fields: &[(String, source::LocPat)],
    is_open: bool,
    expected_type: &elab::LocatedConstructor,
    span: &Span,
) -> (elab::LocatedPattern, Env) {
    // Build a record type from the fields, then unify
    let mut result_fields: Vec<(String, elab::LocatedPattern, elab::LocatedConstructor)> =
        Vec::new();
    let mut cur_env = env.clone();
    let mut row_fields: Vec<(elab::LocatedConstructor, elab::LocatedConstructor)> = Vec::new();
    let ktype = Located::new(elab::Kind::Type, span.clone());
    let krow = Located::new(elab::Kind::Record(Box::new(ktype.clone())), span.clone());

    for (fname, fpat) in fields {
        let ftype = fresh_cunif(env, span.clone(), ktype.clone(), fname);
        let (fpatl, new_env) = elab_pat(ctx, &cur_env, fpat, &ftype);
        cur_env = new_env;
        result_fields.push((fname.clone(), fpatl, ftype.clone()));
        row_fields.push((
            Located::new(elab::Constructor::Name(fname.clone()), span.clone()),
            ftype,
        ));
    }

    // If open pattern, allow extra fields
    let row_con = if is_open {
        let rest = fresh_cunif(env, span.clone(), krow.clone(), "_rest");
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
    check_con(ctx, env, span, &record_type, expected_type);

    let pat = Located::new(elab::Pattern::Record(result_fields), span.clone());
    (pat, cur_env)
}

fn prim_con(ctx: &mut ElabCtx, env: &Env, prim: &Prim, span: &Span) -> elab::LocatedConstructor {
    match prim {
        Prim::Int(_) => basis_named_con(env, span, "int"),
        Prim::Float(_) => basis_named_con(env, span, "float"),
        Prim::String(_, _) => basis_named_con(env, span, "string"),
        Prim::Char(_) => basis_named_con(env, span, "char"),
    }
}

fn basis_named_con(env: &Env, span: &Span, name: &str) -> elab::LocatedConstructor {
    // After opening Basis, look up by name directly (returns Named(id)).
    match env.lookup_c(name) {
        VarLookup::Named(id, _) => {
            return Located::new(elab::Constructor::Named(id), span.clone());
        }
        VarLookup::Rel(_, _) => {}
        VarLookup::NotBound => {}
    }
    // Fallback: resolve via ModProj from the Basis structure.
    if let Some((str_id, _)) = env.lookup_str("Basis") {
        return Located::new(
            elab::Constructor::ModProj(*str_id, vec![], name.to_string()),
            span.clone(),
        );
    }
    cerror(span.clone())
}

// ---------------------------------------------------------------------------
// Expression elaboration
// ---------------------------------------------------------------------------

/// Elaborate an expression, returning (elaborated_exp, inferred_type).
pub fn elab_exp(
    ctx: &mut ElabCtx,
    env: &Env,
    denv: &disjoint::DisjointEnv,
    e: &source::LocExp,
) -> (elab::LocatedExpression, elab::LocatedConstructor) {
    let span = e.span.clone();
    match &e.node {
        source::Exp::Prim(prim) => {
            let t = prim_con(ctx, env, prim, &span);
            (Located::new(elab::Expression::Prim(prim.clone()), span), t)
        }

        source::Exp::Annot(inner, con) => {
            let (ce, _) = elab_con(ctx, env, con);
            let (ee, et) = elab_exp(ctx, env, denv, inner);
            check_con(ctx, env, &span, &et, &ce);
            (ee, ce)
        }

        source::Exp::Var(ms, x, _inf) => elab_exp_var(ctx, env, ms, x, &span),

        source::Exp::App(f, arg) => {
            let (fe, ft) = elab_exp(ctx, env, denv, f);
            let (fe2, ft2) = elab_head(ctx, env, denv, fe, ft, &f.span);
            let ftn = hnorm_con(ft2);
            match ftn.node {
                elab::Constructor::TFun(dom, ran) => {
                    let (ae, at) = elab_exp(ctx, env, denv, arg);
                    check_con(ctx, env, &arg.span, &at, &dom);
                    let result =
                        Located::new(elab::Expression::App(Box::new(fe2), Box::new(ae)), span);
                    (result, *ran)
                }
                elab::Constructor::Unif(_, _, k, _, r) => {
                    let dom = fresh_cunif(
                        env,
                        span.clone(),
                        Located::new(elab::Kind::Type, span.clone()),
                        "_dom",
                    );
                    let ran = fresh_cunif(
                        env,
                        span.clone(),
                        Located::new(elab::Kind::Type, span.clone()),
                        "_ran",
                    );
                    let tfun = Located::new(
                        elab::Constructor::TFun(Box::new(dom.clone()), Box::new(ran.clone())),
                        span.clone(),
                    );
                    *r.lock().unwrap() = elab::CUnif::Known(Box::new(tfun));
                    let (ae, at) = elab_exp(ctx, env, denv, arg);
                    check_con(ctx, env, &arg.span, &at, &dom);
                    let result =
                        Located::new(elab::Expression::App(Box::new(fe2), Box::new(ae)), span);
                    (result, ran)
                }
                _ => {
                    ctx.error(
                        f.span.clone(),
                        "Application to non-function type".to_string(),
                    );
                    (eerror(span.clone()), cerror(span))
                }
            }
        }

        source::Exp::Abs(x, opt_ann, body) => {
            let dom = match opt_ann {
                Some(ann) => {
                    let (ce, _) = elab_con(ctx, env, ann);
                    ce
                }
                None => fresh_cunif(
                    env,
                    span.clone(),
                    Located::new(elab::Kind::Type, span.clone()),
                    x,
                ),
            };
            let env2 = env.clone().push_e_rel(x.clone(), dom.clone());
            let (bodye, bodytype) = elab_exp(ctx, &env2, denv, body);
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
            let (e1e, e1t) = elab_exp(ctx, env, denv, e1);
            let (ce, ck) = elab_con(ctx, env, c);
            let e1tn = hnorm_con(e1t);
            match e1tn.node {
                elab::Constructor::TCFun(_, x, k, body) => {
                    check_kind(ctx, env, &c.span, &ce, &ck, &k);
                    let result_type = match sub_con_in_con(0, &ce, *body) {
                        Ok(t) => t,
                        Err(_) => cerror(span.clone()),
                    };
                    let result = Located::new(elab::Expression::CApp(Box::new(e1e), ce), span);
                    (result, result_type)
                }
                _ => {
                    ctx.error(
                        e1.span.clone(),
                        "Constructor application to non-TCFun type".to_string(),
                    );
                    (eerror(span.clone()), cerror(span))
                }
            }
        }

        source::Exp::CAbs(exp, x, k, body) => {
            let ke = elab_kind(ctx, env, k);
            let env2 = env.clone().push_c_rel(x.clone(), ke.clone());
            let new_denv = disjoint::enter(denv.clone());
            let (bodye, bodytype) = elab_exp(ctx, &env2, &new_denv, body);
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
            let env2 = env.clone().push_k_rel(x.clone());
            let (bodye, bodytype) = elab_exp(ctx, &env2, denv, body);
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
            let (c1e, k1) = elab_con(ctx, env, c1);
            let (c2e, k2) = elab_con(ctx, env, c2);
            // Check they're row constructors
            let ku = fresh_kunif(span.clone(), "_");
            let krow = Located::new(elab::Kind::Record(Box::new(ku)), span.clone());
            check_kind(ctx, env, &c1.span, &c1e, &k1, &krow);
            // Add disjointness to denv
            let new_denv = disjoint::assert(c1e.clone(), c2e.clone(), denv.clone());
            // Check c1 ~ c2 holds
            let goals = disjoint::prove(span.clone(), &new_denv, c1e.clone(), c2e.clone());
            if !goals.is_empty() {
                // Defer as constraint
                for g in goals {
                    ctx.constraints.push(Constraint::Disjoint {
                        span: span.clone(),
                        env: env.clone(),
                        goal: g,
                    });
                }
            }
            let (bodye, bodytype) = elab_exp(ctx, env, &new_denv, body);
            (bodye, bodytype)
        }

        source::Exp::DisjointApp(body) => {
            // Used for implicit disjointness arg: just elaborate body
            elab_exp(ctx, env, denv, body)
        }

        source::Exp::Record(xes, _spread) => elab_exp_record(ctx, env, denv, xes, &span),

        source::Exp::Field(e1, field_con) => {
            // If this looks like a module-qualified variable `M.x` (where e1 is
            // Var([], M) and M is a module in scope), treat it as module projection
            // rather than record field access.
            if let source::Exp::Var(ref ms, ref m, _) = e1.node {
                if ms.is_empty() {
                    if let source::Con::Name(ref fname) = field_con.node {
                        // Build the full module path: [M, ...field components?]
                        // Check if M is a module in scope
                        if env.lookup_str(m).is_some() {
                            let path: Vec<String> = vec![m.clone()];
                            return elab_exp_var(ctx, env, &path, fname, &span);
                        }
                    }
                } else if let source::Con::Name(ref fname) = field_con.node {
                    // ms.x — also module projection when ms is non-empty
                    if env.lookup_str(&ms[0]).is_some() {
                        let mut path = ms.clone();
                        path.push(m.clone());
                        return elab_exp_var(ctx, env, &path, fname, &span);
                    }
                }
            }
            let (e1e, e1t) = elab_exp(ctx, env, denv, e1);
            let (fce, fck) = elab_con(ctx, env, field_con);
            let kname = Located::new(elab::Kind::Name, span.clone());
            check_kind(ctx, env, &field_con.span, &fce, &fck, &kname);
            // e1t should be TRecord { field_name = field_type, ... }
            let field_type = fresh_cunif(
                env,
                span.clone(),
                Located::new(elab::Kind::Type, span.clone()),
                "_field",
            );
            let rest_type = fresh_cunif(
                env,
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
            check_con(ctx, env, &e1.span, &e1t, &expected_e1t);
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
            let (e1e, e1t) = elab_exp(ctx, env, denv, e1);
            let (e2e, e2t) = elab_exp(ctx, env, denv, e2);
            // Both must be records; concat their rows
            let ktype = Located::new(elab::Kind::Type, span.clone());
            let krow = Located::new(elab::Kind::Record(Box::new(ktype.clone())), span.clone());
            let r1 = fresh_cunif(env, span.clone(), krow.clone(), "_r1");
            let r2 = fresh_cunif(env, span.clone(), krow.clone(), "_r2");
            let t1 = Located::new(
                elab::Constructor::TRecord(Box::new(r1.clone())),
                span.clone(),
            );
            let t2 = Located::new(
                elab::Constructor::TRecord(Box::new(r2.clone())),
                span.clone(),
            );
            check_con(ctx, env, &e1.span, &e1t, &t1);
            check_con(ctx, env, &e2.span, &e2t, &t2);
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
            let (e1e, e1t) = elab_exp(ctx, env, denv, e1);
            let (fce, fck) = elab_con(ctx, env, field_con);
            let kname = Located::new(elab::Kind::Name, span.clone());
            check_kind(ctx, env, &field_con.span, &fce, &fck, &kname);
            let field_type = fresh_cunif(
                env,
                span.clone(),
                Located::new(elab::Kind::Type, span.clone()),
                "_f",
            );
            let rest = fresh_cunif(
                env,
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
            check_con(ctx, env, &e1.span, &e1t, &expected_e1t);
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
                        rest: rest,
                    },
                ),
                span,
            );
            (result, result_type)
        }

        source::Exp::CutMulti(e1, fields_con) => {
            let (e1e, e1t) = elab_exp(ctx, env, denv, e1);
            let (fce, _fck) = elab_con(ctx, env, fields_con);
            let ktype = Located::new(elab::Kind::Type, span.clone());
            let rest = fresh_cunif(
                env,
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
            check_con(ctx, env, &e1.span, &e1t, &expected);
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
                env,
                span.clone(),
                Located::new(elab::Kind::Type, span.clone()),
                "_",
            );
            let r = Arc::new(Mutex::new(None::<elab::LocatedExpression>));
            (Located::new(elab::Expression::Unif(r), span), t)
        }

        source::Exp::Hole => {
            let t = fresh_cunif(
                env,
                span.clone(),
                Located::new(elab::Kind::Type, span.clone()),
                "_",
            );
            let r = Arc::new(Mutex::new(elab::CUnif::Unknown));
            (Located::new(elab::Expression::Hole(r), span), t)
        }

        source::Exp::Case(scrutinee, branches) => {
            let (scre, scrt) = elab_exp(ctx, env, denv, scrutinee);
            let result_type = fresh_cunif(
                env,
                span.clone(),
                Located::new(elab::Kind::Type, span.clone()),
                "_case",
            );
            let mut elab_branches = Vec::new();
            for (pat, branch_exp) in branches {
                let (pate, pat_env) = elab_pat(ctx, env, pat, &scrt);
                let (branche, brancht) = elab_exp(ctx, &pat_env, denv, branch_exp);
                check_con(ctx, env, &branch_exp.span, &brancht, &result_type);
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
            let mut cur_env = env.clone();
            let mut elab_decls: Vec<elab::LocatedElaboratedDeclaration> = Vec::new();
            for ed in edecls {
                let (elab_decl, new_env) = elab_edecl(ctx, &cur_env, denv, ed);
                if let Some(d) = elab_decl {
                    elab_decls.push(d);
                }
                cur_env = new_env;
            }
            let (bodye, bodytype) = elab_exp(ctx, &cur_env, denv, body);
            let result = Located::new(
                elab::Expression::Let(elab_decls, Box::new(bodye), bodytype.clone()),
                span,
            );
            (result, bodytype)
        }
    }
}

fn elab_exp_var(
    ctx: &mut ElabCtx,
    env: &Env,
    ms: &[String],
    x: &str,
    span: &Span,
) -> (elab::LocatedExpression, elab::LocatedConstructor) {
    if ms.is_empty() {
        match env.lookup_e(x) {
            VarLookup::Rel(idx, t) => {
                return (Located::new(elab::Expression::Rel(idx), span.clone()), t);
            }
            VarLookup::Named(id, t) => {
                return (Located::new(elab::Expression::Named(id), span.clone()), t);
            }
            VarLookup::NotBound => {
                // Check if it's a constructor
                if let Some(info) = env.lookup_constructor(x) {
                    return make_con_exp(info, env, span);
                }
                ctx.error(span.clone(), format!("Unbound variable `{}`", x));
                return (eerror(span.clone()), cerror(span.clone()));
            }
        }
    }

    // Qualified
    let (str_id, items) = match resolve_module_path(ctx, env, ms, span) {
        Some(x) => x,
        None => return (eerror(span.clone()), cerror(span.clone())),
    };

    if let Some(sgi) = sgi_find_val(&items, x) {
        if let elab::SignatureItem::Val(_, id, t) = sgi {
            let e = Located::new(
                elab::Expression::ModProj(str_id, ms[..ms.len()].to_vec(), x.to_string()),
                span.clone(),
            );
            return (e, t.clone());
        }
    }
    // Check for constructor
    if let Some(sgi) = sgi_find_datatype_con(&items, x) {
        let e = Located::new(
            elab::Expression::ModProj(str_id, ms[..ms.len()].to_vec(), x.to_string()),
            span.clone(),
        );
        return (e, cerror(span.clone())); // simplified
    }

    ctx.error(span.clone(), format!("Unbound variable `{}`", x));
    (eerror(span.clone()), cerror(span.clone()))
}

fn sgi_find_datatype_con<'a>(
    sgis: &'a [elab::LocatedSignatureItem],
    x: &str,
) -> Option<&'a elab::SignatureItem> {
    for sgi in sgis {
        if let elab::SignatureItem::Datatype(dts) = &sgi.node {
            for dt in dts {
                for (cname, _, _) in &dt.constrs {
                    if cname == x {
                        return Some(&sgi.node);
                    }
                }
            }
        }
    }
    None
}

fn make_con_exp(
    info: &ConstructorInfo,
    env: &Env,
    span: &Span,
) -> (elab::LocatedExpression, elab::LocatedConstructor) {
    // Build a lambda that constructs the datatype value
    let ktype = Located::new(elab::Kind::Type, span.clone());
    let type_args: Vec<elab::LocatedConstructor> = info
        .type_params
        .iter()
        .map(|_| fresh_cunif(env, span.clone(), ktype.clone(), "_"))
        .collect();

    let dt_con = {
        let base = Located::new(elab::Constructor::Named(info.datatype_id), span.clone());
        type_args.iter().fold(base, |acc, arg| {
            Located::new(
                elab::Constructor::App(Box::new(acc), Box::new(arg.clone())),
                span.clone(),
            )
        })
    };

    let e = Located::new(elab::Expression::Named(info.constructor_id), span.clone());
    // Return type is the datatype applied to type_args
    (e, dt_con)
}

fn elab_exp_record(
    ctx: &mut ElabCtx,
    env: &Env,
    denv: &disjoint::DisjointEnv,
    xes: &[(source::LocCon, source::LocExp)],
    span: &Span,
) -> (elab::LocatedExpression, elab::LocatedConstructor) {
    let ktype = Located::new(elab::Kind::Type, span.clone());
    let krow = Located::new(elab::Kind::Record(Box::new(ktype.clone())), span.clone());
    let mut fields = Vec::new(); // (name_con, value_exp, field_type)
    let mut row_fields = Vec::new();

    for (nc, ve) in xes {
        let (nce, nck) = elab_con(ctx, env, nc);
        let kname = Located::new(elab::Kind::Name, span.clone());
        check_kind(ctx, env, &nc.span, &nce, &nck, &kname);
        let (vee, vet) = elab_exp(ctx, env, denv, ve);
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
    ctx: &mut ElabCtx,
    env: &Env,
    denv: &disjoint::DisjointEnv,
    e: elab::LocatedExpression,
    t: elab::LocatedConstructor,
    span: &Span,
) -> (elab::LocatedExpression, elab::LocatedConstructor) {
    let tn = hnorm_con(t.clone());
    match &tn.node {
        elab::Constructor::TKFun(x, body) => {
            let ku = fresh_kunif(span.clone(), x);
            let body_subst = sub_kind_in_con(0, &ku, *body.clone());
            let new_e = Located::new(
                elab::Expression::KApp(Box::new(e), Box::new(ku)),
                span.clone(),
            );
            elab_head(ctx, env, denv, new_e, body_subst, span)
        }
        elab::Constructor::TCFun(elab::Explicitness::Implicit, x, k, body) => {
            // Insert implicit constructor argument
            let cu = fresh_cunif(env, span.clone(), *k.clone(), x);
            let body_subst = match sub_con_in_con(0, &cu, *body.clone()) {
                Ok(t) => t,
                Err(_) => cerror(span.clone()),
            };
            let new_e = Located::new(elab::Expression::CApp(Box::new(e), cu), span.clone());
            elab_head(ctx, env, denv, new_e, body_subst, span)
        }
        elab::Constructor::TDisjoint(c1, c2, body) => {
            // Insert disjointness witness
            let goals = disjoint::prove(span.clone(), denv, *c1.clone(), *c2.clone());
            if !goals.is_empty() {
                for g in goals {
                    ctx.constraints.push(Constraint::Disjoint {
                        span: span.clone(),
                        env: env.clone(),
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
            elab_head(ctx, env, denv, new_e, *body.clone(), span)
        }
        elab::Constructor::TFun(dom, _) if env.is_class(dom) => {
            // Typeclass argument — insert implicit resolution
            let result_ref: Arc<Mutex<Option<elab::LocatedExpression>>> =
                Arc::new(Mutex::new(None));
            ctx.constraints.push(Constraint::TypeClass {
                span: span.clone(),
                env: env.clone(),
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
                elab::Constructor::TFun(_, ran) => elab_head(ctx, env, denv, new_e, *ran, span),
                _ => (new_e, t),
            }
        }
        _ => (e, t),
    }
}

// ---------------------------------------------------------------------------
// Expression-level declaration elaboration
// ---------------------------------------------------------------------------

fn elab_edecl(
    ctx: &mut ElabCtx,
    env: &Env,
    denv: &disjoint::DisjointEnv,
    ed: &source::LocEDecl,
) -> (Option<elab::LocatedElaboratedDeclaration>, Env) {
    let span = ed.span.clone();
    match &ed.node {
        source::EDecl::Val(pat, e) => {
            let t = fresh_cunif(
                env,
                span.clone(),
                Located::new(elab::Kind::Type, span.clone()),
                "_",
            );
            let (ee, et) = elab_exp(ctx, env, denv, e);
            let (pate, new_env) = elab_pat(ctx, env, pat, &et);
            check_con(ctx, env, &span, &et, &t);
            let decl = Located::new(elab::ElaboratedDeclaration::Val(pate, et, ee), span);
            (Some(decl), new_env)
        }
        source::EDecl::ValRec(bindings) => {
            // Mutual recursion: add all names to env first
            let mut pre_env = env.clone();
            let mut annot_types: Vec<elab::LocatedConstructor> = Vec::new();
            for (x, opt_ann, _) in bindings {
                let t = match opt_ann {
                    Some(ann) => {
                        let (ce, _) = elab_con(ctx, &pre_env, ann);
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
                let (ee, et) = elab_exp(ctx, &pre_env, denv, e);
                check_con(ctx, &pre_env, &span, &et, &annot_types[i]);
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

pub fn elab_sgn_item(
    ctx: &mut ElabCtx,
    env: &Env,
    denv: &disjoint::DisjointEnv,
    sgi: &source::LocSgnItem,
) -> (Option<elab::LocatedSignatureItem>, Env) {
    let span = sgi.span.clone();
    match &sgi.node {
        source::SgnItem::ConAbs(x, k) => {
            let ke = elab_kind(ctx, env, k);
            let (new_env, id) = env.clone().push_c_named(x.clone(), ke.clone(), None);
            let result = Located::new(elab::SignatureItem::ConAbs(x.clone(), id, ke), span);
            (Some(result), new_env)
        }
        source::SgnItem::Con(x, opt_k, c) => {
            let (ce, ck) = elab_con(ctx, env, c);
            let ke = match opt_k {
                Some(k) => {
                    let ke2 = elab_kind(ctx, env, k);
                    check_kind(ctx, env, &span, &ce, &ck, &ke2);
                    ke2
                }
                None => ck,
            };
            let (new_env, id) = env
                .clone()
                .push_c_named(x.clone(), ke.clone(), Some(ce.clone()));
            let result = Located::new(
                elab::SignatureItem::Constructor(x.clone(), id, ke, ce),
                span,
            );
            (Some(result), new_env)
        }
        source::SgnItem::Val(x, t) => {
            let (te, _) = elab_con(ctx, env, t);
            let (new_env, id) = env.clone().push_e_named(x.clone(), te.clone());
            let result = Located::new(elab::SignatureItem::Val(x.clone(), id, te), span);
            (Some(result), new_env)
        }
        source::SgnItem::Str(x, sgn) => {
            let prev_in_sig = ctx.in_signature;
            ctx.in_signature = true;
            let sgne = elab_sgn(ctx, env, denv, sgn);
            ctx.in_signature = prev_in_sig;
            let (new_env, id) = env.clone().push_str_named(x.clone(), sgne.clone());
            let result = Located::new(
                elab::SignatureItem::Structure(elab::ImportMode::Import, x.clone(), id, sgne),
                span,
            );
            (Some(result), new_env)
        }
        source::SgnItem::Sgn(x, sgn) => {
            let sgne = elab_sgn(ctx, env, denv, sgn);
            let (new_env, id) = env.clone().push_sgn_named(x.clone(), sgne.clone());
            let result = Located::new(elab::SignatureItem::Signature(x.clone(), id, sgne), span);
            (Some(result), new_env)
        }
        source::SgnItem::Include(sgn) => {
            // Include expands the signature items
            let sgne = elab_sgn(ctx, env, denv, sgn);
            // We return None and handle include by returning the sgn's items
            // For simplicity, wrap in a Structure with a fresh name
            (None, env.clone())
        }
        source::SgnItem::Constraint(c1, c2) => {
            let (c1e, _) = elab_con(ctx, env, c1);
            let (c2e, _) = elab_con(ctx, env, c2);
            let result = Located::new(elab::SignatureItem::Constraint(c1e, c2e), span);
            (Some(result), env.clone())
        }
        source::SgnItem::Datatype(dts) => elab_datatype_sig(ctx, env, dts, &span),
        source::SgnItem::DatatypeImp(x, ms, y) => elab_datatype_imp_sig(ctx, env, x, ms, y, &span),
        source::SgnItem::ClassAbs(x, k) => {
            let ke = elab_kind(ctx, env, k);
            let (mut new_env, id) = env.clone().push_c_named(x.clone(), ke.clone(), None);
            new_env = new_env.push_class(id);
            let result = Located::new(elab::SignatureItem::ClassAbs(x.clone(), id, ke), span);
            (Some(result), new_env)
        }
        source::SgnItem::Class(x, k, c) => {
            let ke = elab_kind(ctx, env, k);
            let (ce, _) = elab_con(ctx, env, c);
            let (mut new_env, id) =
                env.clone()
                    .push_c_named(x.clone(), ke.clone(), Some(ce.clone()));
            new_env = new_env.push_class(id);
            let result = Located::new(elab::SignatureItem::Class(x.clone(), id, ke, ce), span);
            (Some(result), new_env)
        }
        source::SgnItem::Table(x, c, pk_e, unique_e) => {
            // Table in signature: like Val
            let (ce, _) = elab_con(ctx, env, c);
            let (new_env, id) = env.clone().push_e_named(x.clone(), ce.clone());
            let result = Located::new(elab::SignatureItem::Val(x.clone(), id, ce), span);
            (Some(result), new_env)
        }
    }
}

fn elab_datatype_sig(
    ctx: &mut ElabCtx,
    env: &Env,
    dts: &[source::DatatypeDecl],
    span: &Span,
) -> (Option<elab::LocatedSignatureItem>, Env) {
    let mut cur_env = env.clone();
    let mut elab_dts: Vec<elab::DatatypeDecl> = Vec::new();

    for dt in dts {
        let (elab_dt, new_env) = elab_single_datatype(ctx, &cur_env, dt, span);
        cur_env = new_env;
        elab_dts.push(elab_dt);
    }

    let result = Located::new(elab::SignatureItem::Datatype(elab_dts), span.clone());
    (Some(result), cur_env)
}

fn elab_single_datatype(
    ctx: &mut ElabCtx,
    env: &Env,
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

    let (env_with_dt, dt_id) = env.clone().push_c_named(dt.name.clone(), dt_kind, None);

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
            let (ce, _) = elab_con(ctx, &param_env, at);
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
    ctx: &mut ElabCtx,
    env: &Env,
    x: &str,
    ms: &[String],
    y: &str,
    span: &Span,
) -> (Option<elab::LocatedSignatureItem>, Env) {
    // DatatypeImp: x = M.Y (datatype alias)
    let (str_id, items) = match resolve_module_path(ctx, env, ms, span) {
        Some(v) => v,
        None => return (None, env.clone()),
    };

    if let Some(dt) = sgi_find_datatype(&items, y) {
        let id = new_named_id();
        let constrs = dt.constrs.clone();
        let new_env = env.clone().push_c_named_as(
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

    ctx.error(span.clone(), format!("Unbound datatype `{}`", y));
    (None, env.clone())
}

// ---------------------------------------------------------------------------
// Signature elaboration
// ---------------------------------------------------------------------------

pub fn elab_sgn(
    ctx: &mut ElabCtx,
    env: &Env,
    denv: &disjoint::DisjointEnv,
    sgn: &source::LocSgn,
) -> elab::LocatedSignature {
    let span = sgn.span.clone();
    match &sgn.node {
        source::Sgn::Const(sgis) => {
            let mut cur_env = env.clone();
            let mut elab_sgis: Vec<elab::LocatedSignatureItem> = Vec::new();
            for sgi in sgis {
                let (sgi_opt, new_env) = elab_sgn_item(ctx, &cur_env, denv, sgi);
                cur_env = new_env;
                if let Some(s) = sgi_opt {
                    elab_sgis.push(s);
                }
            }
            Located::new(elab::Signature::Const(elab_sgis), span)
        }
        source::Sgn::Var(x) => match env.lookup_sgn(x) {
            Some((id, _)) => Located::new(elab::Signature::Var(*id), span),
            None => {
                ctx.error(span.clone(), format!("Unbound signature `{}`", x));
                sgn_error(span)
            }
        },
        source::Sgn::Fun(x, dom, ran) => {
            let dome = elab_sgn(ctx, env, denv, dom);
            // Bind x in env for ran
            let (env2, id) = env.clone().push_str_named(x.clone(), dome.clone());
            let rane = elab_sgn(ctx, &env2, denv, ran);
            Located::new(
                elab::Signature::Fun(x.clone(), id, Box::new(dome), Box::new(rane)),
                span,
            )
        }
        source::Sgn::Where(sgn1, ms, x, c) => {
            let sgn1e = elab_sgn(ctx, env, denv, sgn1);
            let (ce, _) = elab_con(ctx, env, c);
            Located::new(
                elab::Signature::Where(Box::new(sgn1e), ms.clone(), x.clone(), ce),
                span,
            )
        }
        source::Sgn::Proj(m, ms, x) => match env.lookup_str(m) {
            Some((id, _)) => Located::new(elab::Signature::Proj(*id, ms.clone(), x.clone()), span),
            None => {
                ctx.error(span.clone(), format!("Unbound module `{}`", m));
                sgn_error(span)
            }
        },
    }
}

// ---------------------------------------------------------------------------
// subSgn: signature subtyping
// ---------------------------------------------------------------------------

pub fn sub_sgn(
    ctx: &mut ElabCtx,
    env: &Env,
    denv: &disjoint::DisjointEnv,
    actual: &elab::LocatedSignature,
    expected: &elab::LocatedSignature,
    span: &Span,
) {
    let actual_n = hnorm_sgn(env, actual);
    let expected_n = hnorm_sgn(env, expected);

    match (&actual_n.node, &expected_n.node) {
        (elab::Signature::Error, _) | (_, elab::Signature::Error) => {}

        (elab::Signature::Const(sgis1), elab::Signature::Const(sgis2)) => {
            // For each item in sgis2 (the expected/spec), find it in sgis1
            for sgi2 in sgis2 {
                sub_sgi(ctx, env, denv, sgis1, &sgi2.node, span);
            }
        }

        (elab::Signature::Fun(_, id1, dom1, ran1), elab::Signature::Fun(_, id2, dom2, ran2)) => {
            // Contravariant in domain
            sub_sgn(ctx, env, denv, dom2, dom1, span);
            // Covariant in range: bind the module param
            let env2 = env
                .clone()
                .push_str_named_as("_".to_string(), *id1, *dom1.clone());
            sub_sgn(ctx, &env2, denv, ran1, ran2, span);
        }

        _ => {
            ctx.error(span.clone(), format!("Signature mismatch"));
        }
    }
}

fn sub_sgi(
    ctx: &mut ElabCtx,
    env: &Env,
    denv: &disjoint::DisjointEnv,
    actual_sgis: &[elab::LocatedSignatureItem],
    expected: &elab::SignatureItem,
    span: &Span,
) {
    match expected {
        elab::SignatureItem::Val(x, _, t2) => {
            if let Some(sgi1) = sgi_find_val(actual_sgis, x) {
                if let elab::SignatureItem::Val(_, _, t1) = sgi1 {
                    check_con(ctx, env, span, t1, t2);
                }
            } else {
                ctx.error(span.clone(), format!("Signature missing value `{}`", x));
            }
        }
        elab::SignatureItem::ConAbs(x, _, k2) => {
            if let Some(sgi1) = sgi_find_con(actual_sgis, x) {
                match sgi1 {
                    elab::SignatureItem::ConAbs(_, _, k1)
                    | elab::SignatureItem::Constructor(_, _, k1, _) => {
                        if let Err(e) = unify_kinds(env, k1, k2) {
                            ctx.error(span.clone(), format!("Kind mismatch for `{}`: {:?}", x, e));
                        }
                    }
                    _ => ctx.error(span.clone(), format!("Wrong constructor kind for `{}`", x)),
                }
            } else {
                ctx.error(span.clone(), format!("Signature missing type `{}`", x));
            }
        }
        elab::SignatureItem::Constructor(x, _, k2, c2) => {
            if let Some(sgi1) = sgi_find_con(actual_sgis, x) {
                match sgi1 {
                    elab::SignatureItem::Constructor(_, _, k1, c1) => {
                        if let Err(e) = unify_kinds(env, k1, k2) {
                            ctx.error(span.clone(), format!("Kind mismatch for `{}`: {:?}", x, e));
                        }
                        check_con(ctx, env, span, c1, c2);
                    }
                    _ => ctx.error(span.clone(), format!("Wrong type for `{}`", x)),
                }
            } else {
                ctx.error(span.clone(), format!("Signature missing type `{}`", x));
            }
        }
        elab::SignatureItem::Structure(_, x, _, sgn2) => {
            if let Some(sgi1) = sgi_find_str(actual_sgis, x) {
                if let elab::SignatureItem::Structure(_, _, _, sgn1) = sgi1 {
                    sub_sgn(ctx, env, denv, sgn1, sgn2, span);
                }
            } else {
                ctx.error(span.clone(), format!("Signature missing structure `{}`", x));
            }
        }
        elab::SignatureItem::Constraint(c1, c2) => {
            // Check that the constraint holds in actual
            let goals = disjoint::prove(span.clone(), denv, c1.clone(), c2.clone());
            if !goals.is_empty() {
                for g in goals {
                    ctx.constraints.push(Constraint::Disjoint {
                        span: span.clone(),
                        env: env.clone(),
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
// selfify: make a structure's signature self-referential
// ---------------------------------------------------------------------------

fn selfify(env: &Env, str_id: usize, sgn: &elab::LocatedSignature) -> elab::LocatedSignature {
    // Returns the signature with all abstract types made concrete
    // via ModProj references to the actual structure.
    // Simplified: just return the signature as-is for now.
    sgn.clone()
}

// ---------------------------------------------------------------------------
// Top-level declaration elaboration
// ---------------------------------------------------------------------------

pub fn elab_decl(
    ctx: &mut ElabCtx,
    env: &Env,
    denv: &disjoint::DisjointEnv,
    decl: &source::LocDecl,
) -> (Vec<elab::LocatedDeclaration>, Env, disjoint::DisjointEnv) {
    let span = decl.span.clone();
    match &decl.node {
        source::Decl::Con(x, opt_k, c) => {
            let (ce, ck) = elab_con(ctx, env, c);
            let ke = match opt_k {
                Some(k) => {
                    let ke2 = elab_kind(ctx, env, k);
                    check_kind(ctx, env, &span, &ce, &ck, &ke2);
                    ke2
                }
                None => ck,
            };
            let (new_env, id) = env
                .clone()
                .push_c_named(x.clone(), ke.clone(), Some(ce.clone()));
            let decl_out =
                Located::new(elab::Declaration::Constructor(x.clone(), id, ke, ce), span);
            (vec![decl_out], new_env, denv.clone())
        }

        source::Decl::Datatype(dts) => {
            let mut cur_env = env.clone();
            let mut elab_dts: Vec<elab::DatatypeDecl> = Vec::new();
            for dt in dts {
                let (elab_dt, new_env) = elab_single_datatype(ctx, &cur_env, dt, &span);
                cur_env = new_env;
                elab_dts.push(elab_dt);
            }
            let decl_out = Located::new(elab::Declaration::Datatype(elab_dts), span);
            (vec![decl_out], cur_env, denv.clone())
        }

        source::Decl::DatatypeImp(x, ms, y) => {
            let (opt_sgi, new_env) = elab_datatype_imp_sig(ctx, env, x, ms, y, &span);
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
                    return (vec![decl_out], new_env, denv.clone());
                }
            }
            (vec![], new_env, denv.clone())
        }

        source::Decl::Val(pat, e) => {
            let t = fresh_cunif(
                env,
                span.clone(),
                Located::new(elab::Kind::Type, span.clone()),
                "_",
            );
            let (ee, et) = elab_exp(ctx, env, denv, e);
            let (pate, new_env) = elab_pat(ctx, env, pat, &et);
            // Collect declared bindings
            let mut decls = Vec::new();
            collect_val_decls(&pate, &ee, &et, &span, &mut decls, &mut new_env.clone());
            // Solve constraints
            solve_constraints(ctx, &new_env);
            (decls, new_env, denv.clone())
        }

        source::Decl::ValRec(bindings) => {
            let mut pre_env = env.clone();
            let mut annot_types: Vec<elab::LocatedConstructor> = Vec::new();
            let mut ids: Vec<usize> = Vec::new();

            for (x, opt_ann, _) in bindings {
                let t = match opt_ann {
                    Some(ann) => {
                        let (ce, _) = elab_con(ctx, &pre_env, ann);
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
                let (ee, et) = elab_exp(ctx, &pre_env, denv, e);
                check_con(ctx, &pre_env, &span, &et, &annot_types[i]);
                elab_recs.push((x.clone(), ids[i], annot_types[i].clone(), ee));
            }

            solve_constraints(ctx, &pre_env);
            let decl_out = Located::new(elab::Declaration::ValRec(elab_recs), span);
            (vec![decl_out], pre_env, denv.clone())
        }

        source::Decl::Sgn(x, sgn) => {
            let sgne = elab_sgn(ctx, env, denv, sgn);
            let (new_env, id) = env.clone().push_sgn_named(x.clone(), sgne.clone());
            let decl_out = Located::new(elab::Declaration::Signature(x.clone(), id, sgne), span);
            (vec![decl_out], new_env, denv.clone())
        }

        source::Decl::Str(x, opt_sgn, _mtime, str_body, _from_root) => {
            elab_str_decl(ctx, env, denv, x, opt_sgn.as_ref(), str_body, &span)
        }

        source::Decl::FfiStr(x, sgn, _mtime) => {
            let sgne = elab_sgn(ctx, env, denv, sgn);
            let (new_env, id) = env.clone().push_str_named(x.clone(), sgne.clone());
            let decl_out = Located::new(elab::Declaration::FfiStr(x.clone(), id, sgne), span);
            (vec![decl_out], new_env, denv.clone())
        }

        source::Decl::Open(m, ms) => {
            // Open M: bring all bindings from M into scope
            let all_ms: Vec<String> = std::iter::once(m.clone())
                .chain(ms.iter().cloned())
                .collect();
            elab_open(ctx, env, denv, &all_ms, &span)
        }

        source::Decl::Constraint(c1, c2) => {
            let (c1e, _) = elab_con(ctx, env, c1);
            let (c2e, _) = elab_con(ctx, env, c2);
            let new_denv = disjoint::assert(c1e.clone(), c2e.clone(), denv.clone());
            let decl_out = Located::new(elab::Declaration::Constraint(c1e, c2e), span);
            (vec![decl_out], env.clone(), new_denv)
        }

        source::Decl::OpenConstraints(m, ms) => {
            // Simplified: no-op for now
            (vec![], env.clone(), denv.clone())
        }

        source::Decl::Export(str_body) => {
            let (str_e, str_sgn) = elab_str(ctx, env, denv, str_body, None);
            let (new_env, id) = env
                .clone()
                .push_str_named("_export".to_string(), str_sgn.clone());
            let decl_out = Located::new(elab::Declaration::Export(id, str_sgn, str_e), span);
            (vec![decl_out], new_env, denv.clone())
        }

        source::Decl::Table(x, c, pk_e, unique_e) => {
            elab_table_decl(ctx, env, denv, x, c, pk_e, unique_e, &span)
        }

        source::Decl::Sequence(x) => {
            let nt = new_named_id();
            let (new_env, id) = env
                .clone()
                .push_e_named(x.clone(), basis_named_con(env, &span, "int"));
            let decl_out = Located::new(elab::Declaration::Sequence(nt, x.clone(), id), span);
            (vec![decl_out], new_env, denv.clone())
        }

        source::Decl::View(x, e) => {
            let (ee, et) = elab_exp(ctx, env, denv, e);
            let nt = new_named_id();
            let (new_env, id) = env.clone().push_e_named(x.clone(), et.clone());
            let decl_out = Located::new(elab::Declaration::View(nt, x.clone(), id, ee, et), span);
            (vec![decl_out], new_env, denv.clone())
        }

        source::Decl::Index(e1, e2, _opt_c) => {
            let (e1e, _) = elab_exp(ctx, env, denv, e1);
            let (e2e, _) = elab_exp(ctx, env, denv, e2);
            let decl_out = Located::new(elab::Declaration::Index(e1e, e2e), span);
            (vec![decl_out], env.clone(), denv.clone())
        }

        source::Decl::Database(x) => {
            let decl_out = Located::new(elab::Declaration::Database(x.clone()), span);
            (vec![decl_out], env.clone(), denv.clone())
        }

        source::Decl::Cookie(x, c) => {
            let (ce, _) = elab_con(ctx, env, c);
            let nt = new_named_id();
            let (new_env, id) = env.clone().push_e_named(x.clone(), ce.clone());
            let decl_out = Located::new(elab::Declaration::Cookie(nt, x.clone(), id, ce), span);
            (vec![decl_out], new_env, denv.clone())
        }

        source::Decl::Style(x) => {
            let nt = new_named_id();
            let (new_env, id) = env.clone().push_e_named(
                x.clone(),
                Located::new(elab::Constructor::Unit, span.clone()),
            );
            let decl_out = Located::new(elab::Declaration::Style(nt, x.clone(), id), span);
            (vec![decl_out], new_env, denv.clone())
        }

        source::Decl::Task(e1, e2) => {
            let (e1e, _) = elab_exp(ctx, env, denv, e1);
            let (e2e, _) = elab_exp(ctx, env, denv, e2);
            let decl_out = Located::new(elab::Declaration::Task(e1e, e2e), span);
            (vec![decl_out], env.clone(), denv.clone())
        }

        source::Decl::Policy(e) => {
            let (ee, _) = elab_exp(ctx, env, denv, e);
            let decl_out = Located::new(elab::Declaration::Policy(ee), span);
            (vec![decl_out], env.clone(), denv.clone())
        }

        source::Decl::OnError(m, ms, x) => {
            let decl_out = Located::new(
                elab::Declaration::OnError(
                    env.lookup_str(m).map(|(id, _)| *id).unwrap_or(0),
                    ms.clone(),
                    x.clone(),
                ),
                span,
            );
            (vec![decl_out], env.clone(), denv.clone())
        }

        source::Decl::Ffi(x, modes, c) => {
            let (ce, _) = elab_con(ctx, env, c);
            let (new_env, id) = env.clone().push_e_named(x.clone(), ce.clone());
            let decl_out = Located::new(
                elab::Declaration::Ffi(x.clone(), id, modes.clone(), ce),
                span,
            );
            (vec![decl_out], new_env, denv.clone())
        }
    }
}

fn collect_val_decls(
    pat: &elab::LocatedPattern,
    exp: &elab::LocatedExpression,
    typ: &elab::LocatedConstructor,
    span: &Span,
    decls: &mut Vec<elab::LocatedDeclaration>,
    env: &mut Env,
) {
    match &pat.node {
        elab::Pattern::Var(x, t) => {
            let id = new_named_id();
            *env = env.clone().push_e_named_as(x.clone(), id, t.clone());
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
    ctx: &mut ElabCtx,
    env: &Env,
    denv: &disjoint::DisjointEnv,
    x: &str,
    opt_sgn: Option<&source::LocSgn>,
    str_body: &source::LocStr,
    span: &Span,
) -> (Vec<elab::LocatedDeclaration>, Env, disjoint::DisjointEnv) {
    let ascribed_sgn = opt_sgn.map(|sgn| elab_sgn(ctx, env, denv, sgn));
    let (str_e, inferred_sgn) = elab_str(ctx, env, denv, str_body, ascribed_sgn.as_ref());
    let (new_env, id) = env
        .clone()
        .push_str_named(x.to_string(), inferred_sgn.clone());
    let decl_out = Located::new(
        elab::Declaration::Structure(x.to_string(), id, inferred_sgn, str_e),
        span.clone(),
    );
    (vec![decl_out], new_env, denv.clone())
}

fn elab_open(
    ctx: &mut ElabCtx,
    env: &Env,
    denv: &disjoint::DisjointEnv,
    ms: &[String],
    span: &Span,
) -> (Vec<elab::LocatedDeclaration>, Env, disjoint::DisjointEnv) {
    let (str_id, items) = match resolve_module_path(ctx, env, ms, span) {
        Some(v) => v,
        None => return (vec![], env.clone(), denv.clone()),
    };
    // Add all items from the signature to the current environment
    let mut new_env = env.clone();
    for sgi in &items {
        new_env = enrich_env_from_sgi(
            new_env,
            &sgi.node,
            str_id,
            &ms[..ms.len() - 1],
            &ms[ms.len() - 1],
        );
    }
    (vec![], new_env, denv.clone())
}

fn enrich_env_from_sgi(
    env: Env,
    sgi: &elab::SignatureItem,
    str_id: usize,
    prefix: &[String],
    module_name: &str,
) -> Env {
    match sgi {
        elab::SignatureItem::Val(x, id, t) => env.push_e_named_as(x.clone(), *id, t.clone()),
        elab::SignatureItem::ConAbs(x, id, k) | elab::SignatureItem::Constructor(x, id, k, _) => {
            env.push_c_named_as(x.clone(), *id, k.clone(), None)
        }
        elab::SignatureItem::ClassAbs(x, id, k) | elab::SignatureItem::Class(x, id, k, _) => {
            let ktype = Located::new(elab::Kind::Type, k.span.clone());
            let class_k = Located::new(
                elab::Kind::Arrow(Box::new(k.clone()), Box::new(ktype)),
                k.span.clone(),
            );
            env.push_c_named_as(x.clone(), *id, class_k, None)
        }
        elab::SignatureItem::Structure(_, x, id, sgn) => {
            env.push_str_named_as(x.clone(), *id, sgn.clone())
        }
        elab::SignatureItem::Signature(x, id, sgn) => {
            env.push_sgn_named_as(x.clone(), *id, sgn.clone())
        }
        elab::SignatureItem::Datatype(dts) => {
            let mut cur_env = env;
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
        _ => env,
    }
}

fn elab_table_decl(
    ctx: &mut ElabCtx,
    env: &Env,
    denv: &disjoint::DisjointEnv,
    x: &str,
    c: &source::LocCon,
    pk_e: &source::LocExp,
    unique_e: &source::LocExp,
    span: &Span,
) -> (Vec<elab::LocatedDeclaration>, Env, disjoint::DisjointEnv) {
    let (ce, _) = elab_con(ctx, env, c);
    let (pk_ee, pk_et) = elab_exp(ctx, env, denv, pk_e);
    let (unique_ee, unique_et) = elab_exp(ctx, env, denv, unique_e);

    let mod_id = env.lookup_str("Basis").map(|(id, _)| *id).unwrap_or(0);
    let nt = new_named_id();
    let (new_env, id) = env.clone().push_e_named(x.to_string(), ce.clone());

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
    (vec![decl_out], new_env, denv.clone())
}

// ---------------------------------------------------------------------------
// Structure elaboration
// ---------------------------------------------------------------------------

pub fn elab_str(
    ctx: &mut ElabCtx,
    env: &Env,
    denv: &disjoint::DisjointEnv,
    str_: &source::LocStr,
    ascribed: Option<&elab::LocatedSignature>,
) -> (elab::LocatedStructure, elab::LocatedSignature) {
    let span = str_.span.clone();
    match &str_.node {
        source::Str::Const(decls) => {
            let mut cur_env = env.clone();
            let mut cur_denv = denv.clone();
            let mut elab_decls: Vec<elab::LocatedDeclaration> = Vec::new();
            for d in decls {
                let (ds, new_env, new_denv) = elab_decl(ctx, &cur_env, &cur_denv, d);
                cur_env = new_env;
                cur_denv = new_denv;
                elab_decls.extend(ds);
            }
            // Build signature from the declarations
            let sgn = decls_to_sgn(&elab_decls, &span);
            // Check ascription
            if let Some(asc) = ascribed {
                sub_sgn(ctx, &cur_env, denv, &sgn, asc, &span);
            }
            let str_out = Located::new(elab::Structure::Const(elab_decls), span.clone());
            (str_out, sgn)
        }
        source::Str::Var(x) => match env.lookup_str(x) {
            Some((id, sgn)) => {
                let str_out = Located::new(elab::Structure::Var(*id), span.clone());
                if let Some(asc) = ascribed {
                    sub_sgn(ctx, env, denv, sgn, asc, &span);
                }
                (str_out, sgn.clone())
            }
            None => {
                ctx.error(span.clone(), format!("Unbound structure `{}`", x));
                (str_error(span.clone()), sgn_error(span))
            }
        },
        source::Str::Proj(str_inner, field) => {
            let (str_ie, str_isgn) = elab_str(ctx, env, denv, str_inner, None);
            let items = get_sgn_const_items(env, &str_isgn);
            if let Some(sgi) = sgi_find_str(&items, field) {
                if let elab::SignatureItem::Structure(_, _, id, sgn) = sgi {
                    let str_out = Located::new(
                        elab::Structure::Proj(Box::new(str_ie), field.clone()),
                        span.clone(),
                    );
                    return (str_out, sgn.clone());
                }
            }
            ctx.error(span.clone(), format!("No structure `{}` in module", field));
            (str_error(span.clone()), sgn_error(span))
        }
        source::Str::Fun(x, sgn, _opt_result_sgn, body) => {
            let sgne = elab_sgn(ctx, env, denv, sgn);
            let (env2, param_id) = env.clone().push_str_named(x.clone(), sgne.clone());
            let (bodye, body_sgn) = elab_str(ctx, &env2, denv, body, None);
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
            let (str1e, str1sgn) = elab_str(ctx, env, denv, str1, None);
            let (str2e, str2sgn) = elab_str(ctx, env, denv, str2, None);
            // str1sgn must be a functor
            let str1sgnn = hnorm_sgn(env, &str1sgn);
            match str1sgnn.node {
                elab::Signature::Fun(_, param_id, dom, ran) => {
                    sub_sgn(ctx, env, denv, &str2sgn, &dom, &span);
                    let str_out = Located::new(
                        elab::Structure::App(Box::new(str1e), Box::new(str2e)),
                        span.clone(),
                    );
                    // Substitute str2 for the param in ran
                    // Simplified: return ran as-is
                    (str_out, *ran)
                }
                _ => {
                    ctx.error(
                        span.clone(),
                        "Application of non-functor structure".to_string(),
                    );
                    (str_error(span.clone()), sgn_error(span))
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

fn solve_constraints(ctx: &mut ElabCtx, env: &Env) {
    let constraints = std::mem::take(&mut ctx.constraints);
    let mut remaining = Vec::new();

    for c in constraints {
        match c {
            Constraint::Disjoint {
                span,
                env: c_env,
                goal,
            } => {
                let goals = disjoint::prove(
                    goal.span.clone(),
                    &goal.denv,
                    goal.c1.clone(),
                    goal.c2.clone(),
                );
                if !goals.is_empty() {
                    // Re-add unresolved goals
                    for g in goals {
                        remaining.push(Constraint::Disjoint {
                            span: span.clone(),
                            env: c_env.clone(),
                            goal: g,
                        });
                    }
                }
            }
            Constraint::TypeClass {
                span,
                env: c_env,
                class,
                result,
            } => {
                // Try to resolve the class instance
                match resolve_class(&c_env, &class, &span) {
                    Some(witness) => {
                        *result.lock().unwrap() = Some(witness);
                    }
                    None => {
                        remaining.push(Constraint::TypeClass {
                            span: span.clone(),
                            env: c_env,
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
            Constraint::Disjoint { span, goal, .. } => {
                ctx.error(span, format!("Unresolved disjointness constraint"));
            }
            Constraint::TypeClass { span, class, .. } => {
                ctx.error(
                    span,
                    format!("Unresolved typeclass constraint: {:?}", class.node),
                );
            }
        }
    }
}

fn resolve_class(
    env: &Env,
    class: &elab::LocatedConstructor,
    span: &Span,
) -> Option<elab::LocatedExpression> {
    // Try all classes in the environment
    for (cn, rules) in env.classes() {
        let class_con = cn.to_con(span.clone());
        // Check if class matches
        let class_n = hnorm_con(class.clone());
        // Try closed rules first
        for (nq, hyps, head, witness) in &rules.closed_rules {
            if try_match_class(env, &class_n, head, *nq) {
                // Check hypotheses
                let all_hyps_satisfied = hyps.iter().all(|h| resolve_class(env, h, span).is_some());
                if all_hyps_satisfied {
                    return Some(witness.clone());
                }
            }
        }
        // Then open rules
        for (nq, hyps, head, witness) in &rules.open_rules {
            if try_match_class(env, &class_n, head, *nq) {
                let all_hyps_satisfied = hyps.iter().all(|h| resolve_class(env, h, span).is_some());
                if all_hyps_satisfied {
                    return Some(witness.clone());
                }
            }
        }
    }
    None
}

fn try_match_class(
    env: &Env,
    class: &elab::LocatedConstructor,
    head: &elab::LocatedConstructor,
    num_quantifiers: usize,
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

pub fn elab_file(
    file: crate::source::File,
    _settings: &crate::settings::Settings,
    errors: &mut ErrorReporter,
) -> Option<crate::elaborated::File> {
    let mut ctx = ElabCtx::new();
    let mut env = Env::empty();
    let mut denv = disjoint::empty_env();
    let mut all_decls: Vec<elab::LocatedDeclaration> = Vec::new();

    for decl in &file {
        let (ds, new_env, new_denv) = elab_decl(&mut ctx, &env, &denv, decl);
        env = new_env;
        denv = new_denv;
        all_decls.extend(ds);

        // After elaborating `FfiStr("Basis", ...)`, automatically open Basis
        // so that `unit`, `transaction`, `return`, etc. are in scope without
        // qualification — matching the SML `dopen env' {str = basis_n, ...}`.
        if let crate::source::Decl::FfiStr(name, _, _) = &decl.node {
            if name == "Basis" {
                let basis_span = decl.span.clone();
                let (open_ds, open_env, open_denv) =
                    elab_open(&mut ctx, &env, &denv, &["Basis".to_string()], &basis_span);
                env = open_env;
                denv = open_denv;
                all_decls.extend(open_ds);
            }
        }
    }

    // Report all errors
    for (span, msg) in ctx.errors {
        errors.report_at(span, msg);
    }

    if errors.has_errors() {
        None
    } else {
        Some(all_decls)
    }
}
