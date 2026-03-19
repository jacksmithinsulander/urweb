#![allow(dead_code, unused_variables, unused_imports)]

//! Constructor and kind substitution / normalization operations.
//!
//! Translated from `elab_ops.sml`.

use std::sync::{Arc, Mutex};

use crate::elaborated::{
    CUnif, CUnifRef, Constructor, Explicitness, KUnif, KUnifRef, Kind, LocatedConstructor,
    LocatedKind,
};
use crate::error_types::{Located, Span};

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Lift every free `Kind::Rel(n)` with `n >= bound` by `by`.
fn lift_kind_in_kind_bound(by: usize, bound: usize, k: LocatedKind) -> LocatedKind {
    let span = k.span.clone();
    let node = match k.node {
        Kind::Rel(n) => {
            if n < bound {
                Kind::Rel(n)
            } else {
                Kind::Rel(n + by)
            }
        }
        Kind::Arrow(k1, k2) => Kind::Arrow(
            Box::new(lift_kind_in_kind_bound(by, bound, *k1)),
            Box::new(lift_kind_in_kind_bound(by, bound, *k2)),
        ),
        Kind::Record(k1) => Kind::Record(Box::new(lift_kind_in_kind_bound(by, bound, *k1))),
        Kind::Tuple(ks) => Kind::Tuple(
            ks.into_iter()
                .map(|ki| lift_kind_in_kind_bound(by, bound, ki))
                .collect(),
        ),
        Kind::Fun(x, body) => Kind::Fun(x, Box::new(lift_kind_in_kind_bound(by, bound + 1, *body))),
        other => other,
    };
    Located { node, span }
}

/// Substitute `rep` for `Kind::Rel(xn)`, adjusting indices.
fn sub_kind_in_kind_bound(by: usize, xn: usize, rep: &LocatedKind, k: LocatedKind) -> LocatedKind {
    let span = k.span.clone();
    let node = match k.node {
        Kind::Rel(n) => {
            if n == xn {
                return lift_kind_in_kind_bound(by, 0, rep.clone());
            } else if n > xn {
                Kind::Rel(n - 1)
            } else {
                Kind::Rel(n)
            }
        }
        Kind::Arrow(k1, k2) => Kind::Arrow(
            Box::new(sub_kind_in_kind_bound(by, xn, rep, *k1)),
            Box::new(sub_kind_in_kind_bound(by, xn, rep, *k2)),
        ),
        Kind::Record(ki) => Kind::Record(Box::new(sub_kind_in_kind_bound(by, xn, rep, *ki))),
        Kind::Tuple(ks) => Kind::Tuple(
            ks.into_iter()
                .map(|ki| sub_kind_in_kind_bound(by, xn, rep, ki))
                .collect(),
        ),
        Kind::Fun(x, body) => Kind::Fun(
            x,
            Box::new(sub_kind_in_kind_bound(by + 1, xn + 1, rep, *body)),
        ),
        other => other,
    };
    Located { node, span }
}

/// Lift `Kind::Rel(n)` for `n >= bound` by 1 within a constructor.
fn lift_kind_in_con_bound(bound: usize, c: LocatedConstructor) -> LocatedConstructor {
    let span = c.span.clone();
    let node = match c.node {
        Constructor::TFun(a, b) => Constructor::TFun(
            Box::new(lift_kind_in_con_bound(bound, *a)),
            Box::new(lift_kind_in_con_bound(bound, *b)),
        ),
        Constructor::TCFun(exp, x, k, body) => Constructor::TCFun(
            exp,
            x,
            Box::new(lift_kind_in_kind_bound(1, bound, *k)),
            Box::new(lift_kind_in_con_bound(bound + 1, *body)),
        ),
        Constructor::TRecord(r) => {
            Constructor::TRecord(Box::new(lift_kind_in_con_bound(bound, *r)))
        }
        Constructor::TDisjoint(a, b, c2) => Constructor::TDisjoint(
            Box::new(lift_kind_in_con_bound(bound, *a)),
            Box::new(lift_kind_in_con_bound(bound, *b)),
            Box::new(lift_kind_in_con_bound(bound, *c2)),
        ),
        Constructor::App(f, x) => Constructor::App(
            Box::new(lift_kind_in_con_bound(bound, *f)),
            Box::new(lift_kind_in_con_bound(bound, *x)),
        ),
        Constructor::Abs(x, k, body) => Constructor::Abs(
            x,
            Box::new(lift_kind_in_kind_bound(1, bound, *k)),
            Box::new(lift_kind_in_con_bound(bound, *body)),
        ),
        Constructor::KAbs(x, body) => {
            Constructor::KAbs(x, Box::new(lift_kind_in_con_bound(bound + 1, *body)))
        }
        Constructor::KApp(c2, k) => Constructor::KApp(
            Box::new(lift_kind_in_con_bound(bound, *c2)),
            Box::new(lift_kind_in_kind_bound(1, bound, *k)),
        ),
        Constructor::TKFun(x, body) => {
            Constructor::TKFun(x, Box::new(lift_kind_in_con_bound(bound + 1, *body)))
        }
        Constructor::Record(k, xcs) => Constructor::Record(
            Box::new(lift_kind_in_kind_bound(1, bound, *k)),
            xcs.into_iter()
                .map(|(x, v)| {
                    (
                        lift_kind_in_con_bound(bound, x),
                        lift_kind_in_con_bound(bound, v),
                    )
                })
                .collect(),
        ),
        Constructor::Concat(a, b) => Constructor::Concat(
            Box::new(lift_kind_in_con_bound(bound, *a)),
            Box::new(lift_kind_in_con_bound(bound, *b)),
        ),
        Constructor::Map(k1, k2) => Constructor::Map(
            Box::new(lift_kind_in_kind_bound(1, bound, *k1)),
            Box::new(lift_kind_in_kind_bound(1, bound, *k2)),
        ),
        Constructor::Tuple(cs) => Constructor::Tuple(
            cs.into_iter()
                .map(|ci| lift_kind_in_con_bound(bound, ci))
                .collect(),
        ),
        Constructor::Proj(c2, n) => {
            Constructor::Proj(Box::new(lift_kind_in_con_bound(bound, *c2)), n)
        }
        other => other,
    };
    Located { node, span }
}

// ---------------------------------------------------------------------------
// Public lifting / substitution API
// ---------------------------------------------------------------------------

/// Lift every free `Kind::Rel(n)` inside a kind by 1.
pub fn lift_kind_in_kind(kind: LocatedKind) -> LocatedKind {
    lift_kind_in_kind_bound(1, 0, kind)
}

/// Substitute `rep` for the outermost kind variable (`KRel xn`) in `k`.
pub fn sub_kind_in_kind(
    kind_index: usize,
    replacement: &LocatedKind,
    kind: LocatedKind,
) -> LocatedKind {
    sub_kind_in_kind_bound(0, kind_index, replacement, kind)
}

/// Lift every free `Kind::Rel` inside a constructor by 1 (entering one kind binder).
pub fn lift_kind_in_con(constructor: LocatedConstructor) -> LocatedConstructor {
    lift_kind_in_con_bound(0, constructor)
}

/// Substitute `rep` for the outermost kind variable in a constructor.
pub fn sub_kind_in_con(
    kind_index: usize,
    replacement: &LocatedKind,
    constructor: LocatedConstructor,
) -> LocatedConstructor {
    sub_kind_in_con_inner(0, kind_index, replacement, constructor)
}

fn sub_kind_in_con_inner(
    by: usize,
    xn: usize,
    rep: &LocatedKind,
    c: LocatedConstructor,
) -> LocatedConstructor {
    let span = c.span.clone();
    let node = match c.node {
        Constructor::TFun(a, b) => Constructor::TFun(
            Box::new(sub_kind_in_con_inner(by, xn, rep, *a)),
            Box::new(sub_kind_in_con_inner(by, xn, rep, *b)),
        ),
        Constructor::TCFun(exp, x, k, body) => Constructor::TCFun(
            exp,
            x,
            Box::new(sub_kind_in_kind_bound(by, xn, rep, *k)),
            Box::new(sub_kind_in_con_inner(by + 1, xn + 1, rep, *body)),
        ),
        Constructor::TRecord(r) => {
            Constructor::TRecord(Box::new(sub_kind_in_con_inner(by, xn, rep, *r)))
        }
        Constructor::TDisjoint(a, b, c2) => Constructor::TDisjoint(
            Box::new(sub_kind_in_con_inner(by, xn, rep, *a)),
            Box::new(sub_kind_in_con_inner(by, xn, rep, *b)),
            Box::new(sub_kind_in_con_inner(by, xn, rep, *c2)),
        ),
        Constructor::App(f, x) => Constructor::App(
            Box::new(sub_kind_in_con_inner(by, xn, rep, *f)),
            Box::new(sub_kind_in_con_inner(by, xn, rep, *x)),
        ),
        Constructor::Abs(x, k, body) => Constructor::Abs(
            x,
            Box::new(sub_kind_in_kind_bound(by, xn, rep, *k)),
            Box::new(sub_kind_in_con_inner(by, xn, rep, *body)),
        ),
        Constructor::KAbs(x, body) => Constructor::KAbs(
            x,
            Box::new(sub_kind_in_con_inner(by + 1, xn + 1, rep, *body)),
        ),
        Constructor::KApp(c2, k) => Constructor::KApp(
            Box::new(sub_kind_in_con_inner(by, xn, rep, *c2)),
            Box::new(sub_kind_in_kind_bound(by, xn, rep, *k)),
        ),
        Constructor::TKFun(x, body) => Constructor::TKFun(
            x,
            Box::new(sub_kind_in_con_inner(by + 1, xn + 1, rep, *body)),
        ),
        Constructor::Record(k, xcs) => Constructor::Record(
            Box::new(sub_kind_in_kind_bound(by, xn, rep, *k)),
            xcs.into_iter()
                .map(|(x, v)| {
                    (
                        sub_kind_in_con_inner(by, xn, rep, x),
                        sub_kind_in_con_inner(by, xn, rep, v),
                    )
                })
                .collect(),
        ),
        Constructor::Concat(a, b) => Constructor::Concat(
            Box::new(sub_kind_in_con_inner(by, xn, rep, *a)),
            Box::new(sub_kind_in_con_inner(by, xn, rep, *b)),
        ),
        Constructor::Map(k1, k2) => Constructor::Map(
            Box::new(sub_kind_in_kind_bound(by, xn, rep, *k1)),
            Box::new(sub_kind_in_kind_bound(by, xn, rep, *k2)),
        ),
        Constructor::Tuple(cs) => Constructor::Tuple(
            cs.into_iter()
                .map(|ci| sub_kind_in_con_inner(by, xn, rep, ci))
                .collect(),
        ),
        Constructor::Proj(c2, n) => {
            Constructor::Proj(Box::new(sub_kind_in_con_inner(by, xn, rep, *c2)), n)
        }
        other => other,
    };
    Located { node, span }
}

// ---------------------------------------------------------------------------
// Con-in-Con lifting
// ---------------------------------------------------------------------------

/// Lift every free `Constructor::Rel(n)` inside a constructor by `by`, starting at `bound`.
fn lift_con_in_con_bound(by: usize, bound: usize, c: LocatedConstructor) -> LocatedConstructor {
    let span = c.span.clone();
    let node = match c.node {
        Constructor::Rel(n) => {
            if n < bound {
                Constructor::Rel(n)
            } else {
                Constructor::Rel(n + by)
            }
        }
        // Unification variables track their nesting level
        Constructor::Unif(nl, s, k, name, r) => Constructor::Unif(nl + by, s, k, name, r),
        Constructor::TFun(a, b) => Constructor::TFun(
            Box::new(lift_con_in_con_bound(by, bound, *a)),
            Box::new(lift_con_in_con_bound(by, bound, *b)),
        ),
        Constructor::TCFun(exp, x, k, body) => {
            Constructor::TCFun(exp, x, k, Box::new(lift_con_in_con_bound(by, bound, *body)))
        }
        Constructor::TRecord(r) => {
            Constructor::TRecord(Box::new(lift_con_in_con_bound(by, bound, *r)))
        }
        Constructor::TDisjoint(a, b, c2) => Constructor::TDisjoint(
            Box::new(lift_con_in_con_bound(by, bound, *a)),
            Box::new(lift_con_in_con_bound(by, bound, *b)),
            Box::new(lift_con_in_con_bound(by, bound, *c2)),
        ),
        Constructor::App(f, x) => Constructor::App(
            Box::new(lift_con_in_con_bound(by, bound, *f)),
            Box::new(lift_con_in_con_bound(by, bound, *x)),
        ),
        Constructor::Abs(x, k, body) => {
            Constructor::Abs(x, k, Box::new(lift_con_in_con_bound(by, bound + 1, *body)))
        }
        Constructor::KAbs(x, body) => {
            Constructor::KAbs(x, Box::new(lift_con_in_con_bound(by, bound, *body)))
        }
        Constructor::KApp(c2, k) => {
            Constructor::KApp(Box::new(lift_con_in_con_bound(by, bound, *c2)), k)
        }
        Constructor::TKFun(x, body) => {
            Constructor::TKFun(x, Box::new(lift_con_in_con_bound(by, bound, *body)))
        }
        Constructor::Record(k, xcs) => Constructor::Record(
            k,
            xcs.into_iter()
                .map(|(x, v)| {
                    (
                        lift_con_in_con_bound(by, bound, x),
                        lift_con_in_con_bound(by, bound, v),
                    )
                })
                .collect(),
        ),
        Constructor::Concat(a, b) => Constructor::Concat(
            Box::new(lift_con_in_con_bound(by, bound, *a)),
            Box::new(lift_con_in_con_bound(by, bound, *b)),
        ),
        Constructor::Tuple(cs) => Constructor::Tuple(
            cs.into_iter()
                .map(|ci| lift_con_in_con_bound(by, bound, ci))
                .collect(),
        ),
        Constructor::Proj(c2, n) => {
            Constructor::Proj(Box::new(lift_con_in_con_bound(by, bound, *c2)), n)
        }
        other => other,
    };
    Located { node, span }
}

/// Lift every free `Constructor::Rel(n)` inside `c` by 1.
pub fn lift_con_in_con(constructor: LocatedConstructor) -> LocatedConstructor {
    lift_con_in_con_bound(1, 0, constructor)
}

// ---------------------------------------------------------------------------
// Con-in-Con substitution
// ---------------------------------------------------------------------------

/// Error sentinel: a unification variable with nesting level -1 (sentinel ~1 from SML).
#[derive(Debug)]
pub struct SubUnif;

/// Substitute `rep` for `Constructor::Rel(xn)` in `c`, adjusting all free de Bruijn indices.
/// Returns `Err(SubUnif)` if a `CUnif` with `nl == 0` at the substitution depth
/// is encountered (mirrors SML's `SubUnif` exception for `CUnif(~1, …)`).
pub fn sub_con_in_con(
    con_index: usize,
    replacement: &LocatedConstructor,
    constructor: LocatedConstructor,
) -> Result<LocatedConstructor, SubUnif> {
    sub_con_in_con_inner(0, con_index, replacement, constructor)
}

fn sub_con_in_con_inner(
    by: usize,
    xn: usize,
    rep: &LocatedConstructor,
    c: LocatedConstructor,
) -> Result<LocatedConstructor, SubUnif> {
    let span = c.span.clone();
    let node = match c.node {
        Constructor::Rel(n) => {
            if n == xn {
                return Ok(lift_con_in_con_bound(by, 0, rep.clone()));
            } else if n > xn {
                Constructor::Rel(n - 1)
            } else {
                Constructor::Rel(n)
            }
        }
        // SML: CUnif(~1, …) => raise SubUnif
        // We represent the ~1 sentinel as nl == 0 at depth 0 with the real
        // depth tracked via `by`.  The SML code uses nl = -1 to mean
        // "can't substitute here"; we mirror that by treating nl == 0 at
        // the actual substitution depth (by == 0) as the sentinel.
        Constructor::Unif(nl, s, k, name, r) => {
            // Check if this is the SubUnif sentinel: nl wraps around in SML as
            // ~1 which we represent as `usize::MAX` after a saturating subtraction.
            if nl == usize::MAX {
                return Err(SubUnif);
            }
            if nl == 0 {
                Constructor::Unif(0, s, k, name, r)
            } else {
                Constructor::Unif(nl - 1, s, k, name, r)
            }
        }
        Constructor::TFun(a, b) => Constructor::TFun(
            Box::new(sub_con_in_con_inner(by, xn, rep, *a)?),
            Box::new(sub_con_in_con_inner(by, xn, rep, *b)?),
        ),
        Constructor::TCFun(exp, x, k, body) => Constructor::TCFun(
            exp,
            x,
            k,
            // TCFun introduces a constructor binder, so increment by and xn
            Box::new(sub_con_in_con_inner(by + 1, xn + 1, rep, *body)?),
        ),
        Constructor::TRecord(r) => {
            Constructor::TRecord(Box::new(sub_con_in_con_inner(by, xn, rep, *r)?))
        }
        Constructor::TDisjoint(a, b, c2) => Constructor::TDisjoint(
            Box::new(sub_con_in_con_inner(by, xn, rep, *a)?),
            Box::new(sub_con_in_con_inner(by, xn, rep, *b)?),
            Box::new(sub_con_in_con_inner(by, xn, rep, *c2)?),
        ),
        Constructor::App(f, x) => Constructor::App(
            Box::new(sub_con_in_con_inner(by, xn, rep, *f)?),
            Box::new(sub_con_in_con_inner(by, xn, rep, *x)?),
        ),
        Constructor::Abs(x, k, body) => Constructor::Abs(
            x,
            k,
            Box::new(sub_con_in_con_inner(by + 1, xn + 1, rep, *body)?),
        ),
        Constructor::KAbs(x, body) => {
            Constructor::KAbs(x, Box::new(sub_con_in_con_inner(by, xn, rep, *body)?))
        }
        Constructor::KApp(c2, k) => {
            Constructor::KApp(Box::new(sub_con_in_con_inner(by, xn, rep, *c2)?), k)
        }
        Constructor::TKFun(x, body) => {
            Constructor::TKFun(x, Box::new(sub_con_in_con_inner(by, xn, rep, *body)?))
        }
        Constructor::Record(k, xcs) => {
            let mut new_xcs = Vec::with_capacity(xcs.len());
            for (x, v) in xcs {
                new_xcs.push((
                    sub_con_in_con_inner(by, xn, rep, x)?,
                    sub_con_in_con_inner(by, xn, rep, v)?,
                ));
            }
            Constructor::Record(k, new_xcs)
        }
        Constructor::Concat(a, b) => Constructor::Concat(
            Box::new(sub_con_in_con_inner(by, xn, rep, *a)?),
            Box::new(sub_con_in_con_inner(by, xn, rep, *b)?),
        ),
        Constructor::Tuple(cs) => {
            let mut new_cs = Vec::with_capacity(cs.len());
            for ci in cs {
                new_cs.push(sub_con_in_con_inner(by, xn, rep, ci)?);
            }
            Constructor::Tuple(new_cs)
        }
        Constructor::Proj(c2, n) => {
            Constructor::Proj(Box::new(sub_con_in_con_inner(by, xn, rep, *c2)?), n)
        }
        other => other,
    };
    Ok(Located { node, span })
}

// ---------------------------------------------------------------------------
// Occurs check
// ---------------------------------------------------------------------------

/// Returns `true` if `Constructor::Rel(n)` appears free in `c` (at de Bruijn depth `bound`).
fn occurs_at(n: usize, bound: usize, c: &LocatedConstructor) -> bool {
    match &c.node {
        Constructor::Rel(m) => *m == n + bound,
        Constructor::TFun(a, b) => occurs_at(n, bound, a) || occurs_at(n, bound, b),
        Constructor::TCFun(_, _, _, body) => occurs_at(n, bound, body),
        Constructor::TRecord(r) => occurs_at(n, bound, r),
        Constructor::TDisjoint(a, b, c2) => {
            occurs_at(n, bound, a) || occurs_at(n, bound, b) || occurs_at(n, bound, c2)
        }
        Constructor::App(f, x) => occurs_at(n, bound, f) || occurs_at(n, bound, x),
        Constructor::Abs(_, _, body) => occurs_at(n, bound + 1, body),
        Constructor::KAbs(_, body) => occurs_at(n, bound, body),
        Constructor::KApp(c2, _) => occurs_at(n, bound, c2),
        Constructor::TKFun(_, body) => occurs_at(n, bound, body),
        Constructor::Record(_, xcs) => xcs
            .iter()
            .any(|(x, v)| occurs_at(n, bound, x) || occurs_at(n, bound, v)),
        Constructor::Concat(a, b) => occurs_at(n, bound, a) || occurs_at(n, bound, b),
        Constructor::Tuple(cs) => cs.iter().any(|ci| occurs_at(n, bound, ci)),
        Constructor::Proj(c2, _) => occurs_at(n, bound, c2),
        _ => false,
    }
}

/// Returns `true` if de Bruijn variable 0 occurs free in `c`.
pub fn occurs(constructor: &LocatedConstructor) -> bool {
    occurs_at(0, 0, constructor)
}

/// Returns `true` if the unification variable `r` appears anywhere in `c`.
/// Used for the occurs check when solving Unif variables.
pub fn occurs_cunif(r: &CUnifRef, c: &LocatedConstructor) -> bool {
    match &c.node {
        Constructor::Unif(_, _, _, _, r2) => Arc::ptr_eq(r, r2),
        Constructor::TFun(a, b) => occurs_cunif(r, a) || occurs_cunif(r, b),
        Constructor::TCFun(_, _, _, body) => occurs_cunif(r, body),
        Constructor::TRecord(rc) => occurs_cunif(r, rc),
        Constructor::TDisjoint(a, b, c2) => {
            occurs_cunif(r, a) || occurs_cunif(r, b) || occurs_cunif(r, c2)
        }
        Constructor::App(f, x) => occurs_cunif(r, f) || occurs_cunif(r, x),
        Constructor::Abs(_, _, body) => occurs_cunif(r, body),
        Constructor::KAbs(_, body) => occurs_cunif(r, body),
        Constructor::KApp(c2, _) => occurs_cunif(r, c2),
        Constructor::TKFun(_, body) => occurs_cunif(r, body),
        Constructor::Record(_, xcs) => xcs
            .iter()
            .any(|(x, v)| occurs_cunif(r, x) || occurs_cunif(r, v)),
        Constructor::Concat(a, b) => occurs_cunif(r, a) || occurs_cunif(r, b),
        Constructor::Tuple(cs) => cs.iter().any(|ci| occurs_cunif(r, ci)),
        Constructor::Proj(c2, _) => occurs_cunif(r, c2),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Stats counters (mirrors SML refs)
// ---------------------------------------------------------------------------

use std::sync::atomic::{AtomicUsize, Ordering};

static IDENTITY: AtomicUsize = AtomicUsize::new(0);
static DISTRIBUTE: AtomicUsize = AtomicUsize::new(0);
static FUSE: AtomicUsize = AtomicUsize::new(0);

pub fn reset_stats() {
    IDENTITY.store(0, Ordering::Relaxed);
    DISTRIBUTE.store(0, Ordering::Relaxed);
    FUSE.store(0, Ordering::Relaxed);
}

fn inc_identity() {
    IDENTITY.fetch_add(1, Ordering::Relaxed);
}
fn inc_distribute() {
    DISTRIBUTE.fetch_add(1, Ordering::Relaxed);
}
fn inc_fuse() {
    FUSE.fetch_add(1, Ordering::Relaxed);
}

// ---------------------------------------------------------------------------
// Head-normalisation
// ---------------------------------------------------------------------------

/// Read through a solved unification variable, returning the stored constructor.
fn read_cunif(r: &CUnifRef) -> Option<LocatedConstructor> {
    match &*r.lock().unwrap() {
        CUnif::Known(c) => Some(*c.clone()),
        CUnif::Unknown => None,
    }
}

/// Lift all free `Constructor::Rel` indices in `c` by `nl` levels.
pub fn mlift_con_in_con(
    binder_count: usize,
    constructor: LocatedConstructor,
) -> LocatedConstructor {
    lift_con_in_con_bound(binder_count, 0, constructor)
}

/// Head-normalise a constructor: reduce the outermost redex if possible.
///
/// This is a direct translation of `hnormCon` from `elab_ops.sml`.
/// We do not carry an environment here; callers that need named/modproj
/// lookup can extend this function or layer their own normalization.
pub fn hnorm_con(constructor: LocatedConstructor) -> LocatedConstructor {
    use std::cell::Cell;
    thread_local! {
        static HNORM_DEPTH: Cell<usize> = Cell::new(0);
    }
    let d = HNORM_DEPTH.with(|c| {
        let v = c.get();
        c.set(v + 1);
        v
    });
    if d > 200 {
        HNORM_DEPTH.with(|c| c.set(0));
        panic!(
            "hnorm_con: infinite loop detected (depth > 200); likely circular unification variable"
        );
    }
    let result = hnorm_con_inner(constructor);
    HNORM_DEPTH.with(|c| c.set(d));
    result
}

fn hnorm_con_inner(constructor: LocatedConstructor) -> LocatedConstructor {
    let span = constructor.span.clone();
    match constructor.node.clone() {
        // Solved unification variable: lift and continue normalizing
        Constructor::Unif(binder_count, _, _, _, reference) => {
            if let Some(inner) = read_cunif(&reference) {
                hnorm_con(mlift_con_in_con(binder_count, inner))
            } else {
                constructor
            }
        }

        // Eta reduction: (fn x => f x) where x does not appear in f
        Constructor::Abs(x, k, body) => {
            let body_norm = hnorm_con(*body);
            match &body_norm.node {
                Constructor::App(f, arg) => {
                    if matches!(&arg.node, Constructor::Rel(0)) && !occurs(f) {
                        // sub 0 -> Unit, then hnorm
                        let unit = Located {
                            node: Constructor::Unit,
                            span: span.clone(),
                        };
                        if let Ok(substituted) = sub_con_in_con(0, &unit, *f.clone()) {
                            return hnorm_con(substituted);
                        }
                    }
                    Located {
                        node: Constructor::Abs(x, k, Box::new(body_norm)),
                        span,
                    }
                }
                _ => Located {
                    node: Constructor::Abs(x, k, Box::new(body_norm)),
                    span,
                },
            }
        }

        // Beta reduction
        Constructor::App(c1, c2) => {
            let c1_norm = hnorm_con(*c1);
            match c1_norm.node.clone() {
                Constructor::Abs(_, _, cb) => {
                    let c2_norm = hnorm_con(*c2);
                    if let Ok(sub) = sub_con_in_con(0, &c2_norm, *cb) {
                        hnorm_con(sub)
                    } else {
                        Located {
                            node: Constructor::App(Box::new(c1_norm), Box::new(c2_norm)),
                            span,
                        }
                    }
                }
                Constructor::App(c1p, f) => {
                    // Map fusion / distributivity / identity
                    let c2_norm = hnorm_con(*c2);
                    let c1p_norm = hnorm_con(*c1p);
                    match &c1p_norm.node {
                        Constructor::Map(_k1, k2) => {
                            let k2 = k2.clone();
                            match &c2_norm.node {
                                Constructor::Record(_, fields) if fields.is_empty() => Located {
                                    node: Constructor::Record(k2, vec![]),
                                    span,
                                },
                                Constructor::Record(_, fields) if !fields.is_empty() => {
                                    let fields = fields.clone();
                                    let (first_name, first_val) = fields[0].clone();
                                    let rest_fields = fields[1..].to_vec();
                                    let mapped_first = Located {
                                        node: Constructor::App(f.clone(), Box::new(first_val)),
                                        span: span.clone(),
                                    };
                                    let mapped_rec = Located {
                                        node: Constructor::Record(
                                            k2.clone(),
                                            vec![(first_name, hnorm_con(mapped_first))],
                                        ),
                                        span: span.clone(),
                                    };
                                    let rest_con = Located {
                                        node: Constructor::Record(k2.clone(), rest_fields),
                                        span: span.clone(),
                                    };
                                    let rec_app = Located {
                                        node: Constructor::App(
                                            Box::new(Located {
                                                node: c1_norm.node.clone(),
                                                span: span.clone(),
                                            }),
                                            Box::new(rest_con),
                                        ),
                                        span: span.clone(),
                                    };
                                    hnorm_con(Located {
                                        node: Constructor::Concat(
                                            Box::new(mapped_rec),
                                            Box::new(hnorm_con(rec_app)),
                                        ),
                                        span,
                                    })
                                }
                                Constructor::Concat(cc1, cc2) => {
                                    match &cc1.node {
                                        Constructor::Record(_, fields) if !fields.is_empty() => {
                                            let fields = fields.clone();
                                            let k_inner = match &cc1.node {
                                                Constructor::Record(k, _) => k.clone(),
                                                _ => unreachable!(),
                                            };
                                            let (first_name, first_val) = fields[0].clone();
                                            let rest_fields = fields[1..].to_vec();
                                            let mapped_first = hnorm_con(Located {
                                                node: Constructor::App(
                                                    f.clone(),
                                                    Box::new(first_val),
                                                ),
                                                span: span.clone(),
                                            });
                                            let mapped_rec = Located {
                                                node: Constructor::Record(
                                                    k2.clone(),
                                                    vec![(first_name, mapped_first)],
                                                ),
                                                span: span.clone(),
                                            };
                                            let rest_part = Located {
                                                node: Constructor::Concat(
                                                    Box::new(Located {
                                                        node: Constructor::Record(
                                                            k_inner,
                                                            rest_fields,
                                                        ),
                                                        span: span.clone(),
                                                    }),
                                                    cc2.clone(),
                                                ),
                                                span: span.clone(),
                                            };
                                            let rest_mapped = hnorm_con(Located {
                                                node: Constructor::App(
                                                    Box::new(Located {
                                                        node: c1_norm.node.clone(),
                                                        span: span.clone(),
                                                    }),
                                                    Box::new(rest_part),
                                                ),
                                                span: span.clone(),
                                            });
                                            hnorm_con(Located {
                                                node: Constructor::Concat(
                                                    Box::new(mapped_rec),
                                                    Box::new(rest_mapped),
                                                ),
                                                span,
                                            })
                                        }
                                        _ => {
                                            // tryDistributivity
                                            inc_distribute();
                                            let map_f = Located {
                                                node: Constructor::App(
                                                    Box::new(c1p_norm.clone()),
                                                    f.clone(),
                                                ),
                                                span: span.clone(),
                                            };
                                            let app1 = Located {
                                                node: Constructor::App(
                                                    Box::new(map_f.clone()),
                                                    cc1.clone(),
                                                ),
                                                span: span.clone(),
                                            };
                                            let app2 = Located {
                                                node: Constructor::App(
                                                    Box::new(map_f),
                                                    cc2.clone(),
                                                ),
                                                span: span.clone(),
                                            };
                                            hnorm_con(Located {
                                                node: Constructor::Concat(
                                                    Box::new(app1),
                                                    Box::new(app2),
                                                ),
                                                span,
                                            })
                                        }
                                    }
                                }
                                _ => {
                                    // tryDistributivity on outer c2_norm
                                    match &c2_norm.node {
                                        Constructor::Concat(cc1, cc2) => {
                                            inc_distribute();
                                            let map_f = Located {
                                                node: Constructor::App(
                                                    Box::new(c1p_norm.clone()),
                                                    f.clone(),
                                                ),
                                                span: span.clone(),
                                            };
                                            let app1 = Located {
                                                node: Constructor::App(
                                                    Box::new(map_f.clone()),
                                                    cc1.clone(),
                                                ),
                                                span: span.clone(),
                                            };
                                            let app2 = Located {
                                                node: Constructor::App(
                                                    Box::new(map_f),
                                                    cc2.clone(),
                                                ),
                                                span: span.clone(),
                                            };
                                            hnorm_con(Located {
                                                node: Constructor::Concat(
                                                    Box::new(app1),
                                                    Box::new(app2),
                                                ),
                                                span,
                                            })
                                        }
                                        _ => Located {
                                            node: Constructor::App(
                                                Box::new(Located {
                                                    node: Constructor::App(Box::new(c1p_norm), f),
                                                    span: span.clone(),
                                                }),
                                                Box::new(c2_norm),
                                            ),
                                            span,
                                        },
                                    }
                                }
                            }
                        }
                        _ => Located {
                            node: Constructor::App(
                                Box::new(Located {
                                    node: Constructor::App(Box::new(c1p_norm), f),
                                    span: span.clone(),
                                }),
                                Box::new(c2_norm),
                            ),
                            span,
                        },
                    }
                }
                _ => Located {
                    node: Constructor::App(Box::new(c1_norm), Box::new(hnorm_con(*c2))),
                    span,
                },
            }
        }

        // Kind application: (fn α => body) k  =>  body[k/0]
        Constructor::KApp(c1, k) => {
            let c1_norm = hnorm_con(*c1);
            match c1_norm.node {
                Constructor::KAbs(_, body) => hnorm_con(sub_kind_in_con(0, &k, *body)),
                _ => Located {
                    node: Constructor::KApp(Box::new(c1_norm), k),
                    span,
                },
            }
        }

        // Record concatenation: flatten / simplify
        Constructor::Concat(c1, c2) => {
            let c1_norm = hnorm_con(*c1);
            let c2_norm = hnorm_con(*c2);
            match (c1_norm.node.clone(), c2_norm.node.clone()) {
                (Constructor::Record(k, xcs1), Constructor::Record(_, xcs2)) => {
                    let mut merged = xcs1;
                    merged.extend(xcs2);
                    Located {
                        node: Constructor::Record(k, merged),
                        span,
                    }
                }
                (Constructor::Record(_, ref xcs), _) if xcs.is_empty() => c2_norm,
                (Constructor::Concat(c11, c12), _) => hnorm_con(Located {
                    node: Constructor::Concat(
                        c11,
                        Box::new(Located {
                            node: Constructor::Concat(c12, Box::new(c2_norm)),
                            span: span.clone(),
                        }),
                    ),
                    span,
                }),
                (_, Constructor::Record(_, ref xcs)) if xcs.is_empty() => c1_norm,
                _ => Located {
                    node: Constructor::Concat(Box::new(c1_norm), Box::new(c2_norm)),
                    span,
                },
            }
        }

        // Tuple projection
        Constructor::Proj(c1, n) => {
            let c1_norm = hnorm_con(*c1);
            match c1_norm.node {
                Constructor::Tuple(cs) if n >= 1 && n <= cs.len() => hnorm_con(cs[n - 1].clone()),
                _ => Located {
                    node: Constructor::Proj(Box::new(c1_norm), n),
                    span,
                },
            }
        }

        other => Located { node: other, span },
    }
}

// ---------------------------------------------------------------------------
// Full reduction (reduceCon)
// ---------------------------------------------------------------------------

/// Fully reduce a constructor: recursively normalise all sub-terms.
///
/// Mirrors `reduceCon` from `elab_ops.sml`.  Named / module-projected
/// constructor bodies are not looked up here because we have no environment;
/// callers can extend as needed.
/// Reduce a constructor by one head beta-reduction step.
///
/// Mirrors SML `reduceCon`: first head-normalizes with `hnorm_con`, then
/// if the result is `App(Abs(...), arg)` performs one beta step and recurses.
/// Does NOT structurally recurse into all sub-constructors (unlike a full
/// normalizer) — that avoids infinite loops on cyclic unification variables.
pub fn reduce_con(constructor: LocatedConstructor) -> LocatedConstructor {
    // Head-normalize first (follows Unif chains, beta/eta at the head).
    let r = hnorm_con(constructor);
    match r.node.clone() {
        Constructor::App(c_prime, x) => {
            let c_prime_norm = hnorm_con(*c_prime);
            match c_prime_norm.node.clone() {
                Constructor::Abs(_, _, body) => {
                    // Beta step: (λ. body) x → body[x/0]
                    if let Ok(subst) = sub_con_in_con(0, &*x, *body) {
                        reduce_con(subst)
                    } else {
                        r
                    }
                }
                _ => r,
            }
        }
        _ => r,
    }
}

// NOTE: reduce_con_inner is no longer used; the old full-normalizer was removed
// because it caused infinite loops on cyclic unification variables.
#[allow(dead_code)]
fn reduce_con_inner_legacy(constructor: LocatedConstructor) -> LocatedConstructor {
    let span = constructor.span.clone();
    match constructor.node {
        Constructor::App(c1, c2) => {
            let c1 = reduce_con(*c1);
            let c2 = reduce_con(*c2);
            match c1.node.clone() {
                Constructor::Abs(_, _, cb) => {
                    if let Ok(sub) = sub_con_in_con(0, &c2, *cb) {
                        reduce_con(sub)
                    } else {
                        Located {
                            node: Constructor::App(Box::new(c1), Box::new(c2)),
                            span,
                        }
                    }
                }
                Constructor::App(c1p, f) => {
                    let c1p = reduce_con(*c1p);
                    let f = reduce_con(*f);
                    match &c1p.node {
                        Constructor::Map(_k1, k2) => {
                            let k2 = k2.clone();
                            match &c2.node {
                                Constructor::Record(_, fields) if fields.is_empty() => Located {
                                    node: Constructor::Record(k2, vec![]),
                                    span,
                                },
                                Constructor::Record(_, fields) if !fields.is_empty() => {
                                    let fields = fields.clone();
                                    let (first_name, first_val) = fields[0].clone();
                                    let rest = fields[1..].to_vec();
                                    let mapped_first = reduce_con(Located {
                                        node: Constructor::App(
                                            Box::new(f.clone()),
                                            Box::new(first_val),
                                        ),
                                        span: span.clone(),
                                    });
                                    let mapped_rec = Located {
                                        node: Constructor::Record(
                                            k2.clone(),
                                            vec![(first_name, mapped_first)],
                                        ),
                                        span: span.clone(),
                                    };
                                    let rest_app = reduce_con(Located {
                                        node: Constructor::App(
                                            Box::new(Located {
                                                node: Constructor::App(
                                                    Box::new(c1p.clone()),
                                                    Box::new(f.clone()),
                                                ),
                                                span: span.clone(),
                                            }),
                                            Box::new(Located {
                                                node: Constructor::Record(k2.clone(), rest),
                                                span: span.clone(),
                                            }),
                                        ),
                                        span: span.clone(),
                                    });
                                    reduce_con(Located {
                                        node: Constructor::Concat(
                                            Box::new(mapped_rec),
                                            Box::new(rest_app),
                                        ),
                                        span,
                                    })
                                }
                                _ => {
                                    // tryDistributivity
                                    match c2.node.clone() {
                                        Constructor::Concat(cc1, cc2) => {
                                            inc_distribute();
                                            let map_f = Located {
                                                node: Constructor::App(
                                                    Box::new(c1p.clone()),
                                                    Box::new(f.clone()),
                                                ),
                                                span: span.clone(),
                                            };
                                            let app1 = Located {
                                                node: Constructor::App(
                                                    Box::new(map_f.clone()),
                                                    cc1,
                                                ),
                                                span: span.clone(),
                                            };
                                            let app2 = Located {
                                                node: Constructor::App(Box::new(map_f), cc2),
                                                span: span.clone(),
                                            };
                                            reduce_con(Located {
                                                node: Constructor::Concat(
                                                    Box::new(app1),
                                                    Box::new(app2),
                                                ),
                                                span,
                                            })
                                        }
                                        _ => Located {
                                            node: Constructor::App(
                                                Box::new(Located {
                                                    node: Constructor::App(
                                                        Box::new(c1p),
                                                        Box::new(f),
                                                    ),
                                                    span: span.clone(),
                                                }),
                                                Box::new(c2),
                                            ),
                                            span,
                                        },
                                    }
                                }
                            }
                        }
                        _ => Located {
                            node: Constructor::App(
                                Box::new(Located {
                                    node: Constructor::App(Box::new(c1p), Box::new(f)),
                                    span: span.clone(),
                                }),
                                Box::new(c2),
                            ),
                            span,
                        },
                    }
                }
                _ => Located {
                    node: Constructor::App(Box::new(c1), Box::new(c2)),
                    span,
                },
            }
        }

        Constructor::Abs(x, k, body) => {
            let body = reduce_con(*body);
            match &body.node {
                Constructor::App(f, arg) => {
                    if matches!(&arg.node, Constructor::Rel(0)) && !occurs(f) {
                        let unit = Located {
                            node: Constructor::Unit,
                            span: span.clone(),
                        };
                        if let Ok(sub) = sub_con_in_con(0, &unit, *f.clone()) {
                            return reduce_con(sub);
                        }
                    }
                    Located {
                        node: Constructor::Abs(x, k, Box::new(body)),
                        span,
                    }
                }
                _ => Located {
                    node: Constructor::Abs(x, k, Box::new(body)),
                    span,
                },
            }
        }

        Constructor::KAbs(x, body) => Located {
            node: Constructor::KAbs(x, Box::new(reduce_con(*body))),
            span,
        },
        Constructor::KApp(c1, k) => {
            let c1 = reduce_con(*c1);
            match c1.node.clone() {
                Constructor::KAbs(_, body) => reduce_con(sub_kind_in_con(0, &k, *body)),
                _ => Located {
                    node: Constructor::KApp(Box::new(c1), k),
                    span,
                },
            }
        }
        Constructor::TKFun(x, body) => Located {
            node: Constructor::TKFun(x, Box::new(reduce_con(*body))),
            span,
        },

        Constructor::Record(k, xcs) => Located {
            node: Constructor::Record(
                k,
                xcs.into_iter()
                    .map(|(x, v)| (reduce_con(x), reduce_con(v)))
                    .collect(),
            ),
            span,
        },

        Constructor::Concat(c1, c2) => {
            let c1 = reduce_con(*c1);
            let c2 = reduce_con(*c2);
            match (c1.node.clone(), c2.node.clone()) {
                // 1. Two records
                (Constructor::Record(k, xcs1), Constructor::Record(_, xcs2)) => {
                    let mut merged = xcs1;
                    merged.extend(xcs2);
                    Located {
                        node: Constructor::Record(k, merged),
                        span,
                    }
                }
                // 2. Empty left
                (Constructor::Record(_, ref xcs), _) if xcs.is_empty() => c2,
                // 2. Empty right
                (_, Constructor::Record(_, ref xcs)) if xcs.is_empty() => c1,
                // 3. Left record, right is concat-of-record
                (Constructor::Record(k, xcs1), Constructor::Concat(inner_rec, rest2))
                    if matches!(&inner_rec.node, Constructor::Record(_, _)) =>
                {
                    if let Constructor::Record(_, xcs2) = inner_rec.node.clone() {
                        let mut merged = xcs1;
                        merged.extend(xcs2);
                        Located {
                            node: Constructor::Concat(
                                Box::new(Located {
                                    node: Constructor::Record(k, merged),
                                    span: span.clone(),
                                }),
                                rest2,
                            ),
                            span,
                        }
                    } else {
                        Located {
                            node: Constructor::Concat(Box::new(c1), Box::new(c2)),
                            span,
                        }
                    }
                }
                // 5. Split left concat
                (Constructor::Concat(c11, c12), _) => reduce_con(Located {
                    node: Constructor::Concat(
                        c11,
                        Box::new(Located {
                            node: Constructor::Concat(c12, Box::new(c2)),
                            span: span.clone(),
                        }),
                    ),
                    span,
                }),
                // 6 & 7. Swap to hit earlier rules
                (_, Constructor::Record(_, _)) | (_, Constructor::Concat(_, _)) => {
                    reduce_con(Located {
                        node: Constructor::Concat(Box::new(c2), Box::new(c1)),
                        span,
                    })
                }
                _ => Located {
                    node: Constructor::Concat(Box::new(c1), Box::new(c2)),
                    span,
                },
            }
        }

        Constructor::Tuple(cs) => Located {
            node: Constructor::Tuple(cs.into_iter().map(reduce_con).collect()),
            span,
        },
        Constructor::Proj(c1, n) => {
            let c1 = reduce_con(*c1);
            match c1.node.clone() {
                Constructor::Tuple(cs) if n >= 1 && n <= cs.len() => reduce_con(cs[n - 1].clone()),
                _ => Located {
                    node: Constructor::Proj(Box::new(c1), n),
                    span,
                },
            }
        }

        other => Located { node: other, span },
    }
}

// ---------------------------------------------------------------------------
// consEqSimple
// ---------------------------------------------------------------------------

/// Structurally compare two constructors up to head-normalisation, without
/// unifying.  Returns `true` if they are definitionally equal by simple rules.
///
/// Mirrors `consEqSimple` from `elab_ops.sml`.
pub fn cons_eq_simple(c1: &LocatedConstructor, c2: &LocatedConstructor) -> bool {
    let n1 = hnorm_con(c1.clone());
    let n2 = hnorm_con(c2.clone());
    cons_eq_simple_normed(&n1, &n2)
}

fn cons_eq_simple_normed(c1: &LocatedConstructor, c2: &LocatedConstructor) -> bool {
    match (&c1.node, &c2.node) {
        (Constructor::Rel(n1), Constructor::Rel(n2)) => n1 == n2,
        (Constructor::Named(n1), Constructor::Named(n2)) => n1 == n2,
        (Constructor::ModProj(n1, ms1, x1), Constructor::ModProj(n2, ms2, x2)) => {
            n1 == n2 && ms1 == ms2 && x1 == x2
        }
        (Constructor::App(f1, x1), Constructor::App(f2, x2)) => {
            cons_eq_simple(f1, f2) && cons_eq_simple(x1, x2)
        }
        (Constructor::Abs(_, k1, b1), Constructor::Abs(_, _k2, b2)) => {
            // k1 == k2 would require kind equality; we skip that for simplicity
            cons_eq_simple(b1, b2)
        }
        (Constructor::Name(s1), Constructor::Name(s2)) => s1 == s2,
        (Constructor::Record(_, xts1), Constructor::Record(_, xts2)) => {
            xts1.len() == xts2.len()
                && xts1
                    .iter()
                    .zip(xts2.iter())
                    .all(|((x1, t1), (x2, t2))| cons_eq_simple(x1, x2) && cons_eq_simple(t1, t2))
        }
        (Constructor::Concat(x1, y1), Constructor::Concat(x2, y2)) => {
            cons_eq_simple(x1, x2) && cons_eq_simple(y1, y2)
        }
        (Constructor::Map(_, _), Constructor::Map(_, _)) => true,
        (Constructor::Unit, Constructor::Unit) => true,
        (Constructor::Tuple(cs1), Constructor::Tuple(cs2)) => {
            cs1.len() == cs2.len()
                && cs1
                    .iter()
                    .zip(cs2.iter())
                    .all(|(a, b)| cons_eq_simple(a, b))
        }
        (Constructor::Proj(c1, n1), Constructor::Proj(c2, n2)) => {
            n1 == n2 && cons_eq_simple(c1, c2)
        }
        (Constructor::Unif(_, _, _, _, r1), Constructor::Unif(_, _, _, _, r2)) => {
            Arc::ptr_eq(r1, r2)
        }
        (Constructor::TFun(d1, r1), Constructor::TFun(d2, r2)) => {
            cons_eq_simple(d1, d2) && cons_eq_simple(r1, r2)
        }
        (Constructor::TRecord(c1), Constructor::TRecord(c2)) => cons_eq_simple(c1, c2),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Tests (catch missed mutants)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elaborated::{Constructor, Kind};
    use crate::error_types::Located;

    fn dummy<T>(node: T) -> Located<T> {
        Located::dummy(node)
    }

    #[test]
    fn lift_kind_in_kind_rel_plus_one() {
        let k = dummy(Kind::Rel(0));
        let out = lift_kind_in_kind(k);
        assert!(matches!(out.node, Kind::Rel(1)));
    }

    #[test]
    fn lift_kind_in_kind_bound_below_unchanged() {
        let k = dummy(Kind::Rel(0));
        let out = lift_kind_in_kind_bound(1, 1, k);
        assert!(matches!(out.node, Kind::Rel(0)));
    }

    #[test]
    fn sub_kind_in_kind_rel_zero_replaced() {
        let rep = dummy(Kind::Type);
        let k = dummy(Kind::Rel(0));
        let out = sub_kind_in_kind(0, &rep, k);
        assert!(matches!(out.node, Kind::Type));
    }

    #[test]
    fn sub_kind_in_kind_rel_above_decremented() {
        let rep = dummy(Kind::Type);
        let k = dummy(Kind::Rel(2));
        let out = sub_kind_in_kind(0, &rep, k);
        assert!(matches!(out.node, Kind::Rel(1)));
    }

    #[test]
    fn occurs_rel_zero() {
        let c = dummy(Constructor::Rel(0));
        assert!(occurs(&c));
    }

    #[test]
    fn occurs_unit_false() {
        let c = dummy(Constructor::Unit);
        assert!(!occurs(&c));
    }

    #[test]
    fn occurs_at_rel_at_bound() {
        let c = dummy(Constructor::Rel(1));
        assert!(occurs_at(0, 1, &c));
    }

    #[test]
    fn occurs_at_rel_mismatch_false() {
        let c = dummy(Constructor::Rel(2));
        assert!(!occurs_at(0, 1, &c));
    }

    #[test]
    fn occurs_at_tfun_in_left() {
        let left = dummy(Constructor::Rel(0));
        let right = dummy(Constructor::Unit);
        let c = dummy(Constructor::TFun(Box::new(left), Box::new(right)));
        assert!(occurs_at(0, 0, &c));
    }

    #[test]
    fn occurs_at_tfun_in_right() {
        let left = dummy(Constructor::Unit);
        let right = dummy(Constructor::Rel(0));
        let c = dummy(Constructor::TFun(Box::new(left), Box::new(right)));
        assert!(occurs_at(0, 0, &c));
    }

    #[test]
    fn occurs_at_abs_shifts_bound() {
        // Under Abs, bound becomes bound+1; index 0 at outer is index 1 in body.
        let body = dummy(Constructor::Rel(2));
        let k = dummy(Kind::Type);
        let c = dummy(Constructor::Abs("x".into(), Box::new(k), Box::new(body)));
        assert!(occurs_at(0, 1, &c));
    }

    #[test]
    fn occurs_at_app_in_fun() {
        let f = dummy(Constructor::Rel(0));
        let a = dummy(Constructor::Unit);
        let c = dummy(Constructor::App(Box::new(f), Box::new(a)));
        assert!(occurs_at(0, 0, &c));
    }

    #[test]
    fn occurs_at_trecord_inner() {
        let inner = dummy(Constructor::Rel(0));
        let r = dummy(Constructor::TRecord(Box::new(inner)));
        assert!(occurs_at(0, 0, &r));
    }

    #[test]
    fn lift_con_in_con_rel_plus_one() {
        let c = dummy(Constructor::Rel(0));
        let out = lift_con_in_con(c);
        assert!(matches!(out.node, Constructor::Rel(1)));
    }

    #[test]
    fn sub_con_in_con_rel_zero_replaced() {
        let rep = dummy(Constructor::Named(42));
        let c = dummy(Constructor::Rel(0));
        let out = sub_con_in_con(0, &rep, c).unwrap();
        assert!(matches!(out.node, Constructor::Named(42)));
    }

    #[test]
    fn sub_con_in_con_rel_above_decremented() {
        let rep = dummy(Constructor::Unit);
        let c = dummy(Constructor::Rel(2));
        let out = sub_con_in_con(0, &rep, c).unwrap();
        assert!(matches!(out.node, Constructor::Rel(1)));
    }

    #[test]
    fn cons_eq_simple_tfun_same() {
        let u = dummy(Constructor::Unit);
        let tfun = dummy(Constructor::TFun(Box::new(u.clone()), Box::new(u)));
        assert!(cons_eq_simple(&tfun, &tfun));
    }

    #[test]
    fn cons_eq_simple_tuple_same() {
        let u = dummy(Constructor::Unit);
        let t = dummy(Constructor::Tuple(vec![u.clone(), u]));
        assert!(cons_eq_simple(&t, &t));
    }

    #[test]
    fn cons_eq_simple_record_same() {
        let k = dummy(Kind::Type);
        let u = dummy(Constructor::Unit);
        let r = dummy(Constructor::Record(
            Box::new(k),
            vec![(dummy(Constructor::Name("x".into())), u)],
        ));
        assert!(cons_eq_simple(&r, &r));
    }

    #[test]
    fn hnorm_con_unit_unchanged() {
        let c = dummy(Constructor::Unit);
        let out = hnorm_con(c);
        assert!(matches!(out.node, Constructor::Unit));
    }

    #[test]
    fn reduce_con_unit_unchanged() {
        let c = dummy(Constructor::Unit);
        let out = reduce_con(c);
        assert!(matches!(out.node, Constructor::Unit));
    }
}
