//! Constructor and kind substitution / normalization operations.
//!
//! Translated from `elab_ops.sml`.
//!
//! Public helpers document `# Arguments`, `# Returns`, and `# Errors` (including [`SubUnif`])
//! where de Bruijn level conventions are not obvious from types alone.
//!
//! **Bounded work:** [`hnorm_con`] uses a thread-local depth counter; solved-[`Constructor::Unif`] peeling
//! uses [`PEEL_SOLVED_CONSTRUCTOR_UNIF_CHAIN_MAX_STEPS`] so alias chains cannot cycle without bound.

use std::sync::Arc;

use crate::elaborated::{CUnif, CUnifRef, Constructor, Kind, LocatedConstructor, LocatedKind};
use crate::error_types::Located;

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Lift every free `Kind::Rel(n)` with `n >= bound` by `by`.
fn lift_kind_in_kind_bound(by: usize, bound: usize, kind: LocatedKind) -> LocatedKind {
    let span = kind.span.clone();
    let node = match kind.node {
        Kind::Rel(n) => {
            if n < bound {
                Kind::Rel(n) // bound: not lifted
            } else {
                // Saturating prevents overflow when n is a sentinel large value from an error path.
                Kind::Rel(n.saturating_add(by))
            }
        }
        Kind::Arrow(domain_kind, range_kind) => Kind::Arrow(
            Box::new(lift_kind_in_kind_bound(by, bound, *domain_kind)),
            Box::new(lift_kind_in_kind_bound(by, bound, *range_kind)),
        ),
        Kind::Record(record_element_kind) => Kind::Record(Box::new(lift_kind_in_kind_bound(
            by,
            bound,
            *record_element_kind,
        ))),
        Kind::Tuple(components) => Kind::Tuple(
            components
                .into_iter()
                .map(|component_kind| lift_kind_in_kind_bound(by, bound, component_kind))
                .collect(),
        ),
        Kind::Fun(x, body) => Kind::Fun(x, Box::new(lift_kind_in_kind_bound(by, bound + 1, *body))),
        other => other,
    };
    Located { node, span }
}

/// Substitute `rep` for `Kind::Rel(xn)`, adjusting indices.
fn sub_kind_in_kind_bound(
    by: usize,
    xn: usize,
    rep: &LocatedKind,
    kind: LocatedKind,
) -> LocatedKind {
    let span = kind.span.clone();
    let node = match kind.node {
        Kind::Rel(n) => {
            if n == xn {
                return lift_kind_in_kind_bound(by, 0, rep.clone());
            } else if n > xn {
                Kind::Rel(n - 1)
            } else {
                Kind::Rel(n)
            }
        }
        Kind::Arrow(domain_kind, range_kind) => Kind::Arrow(
            Box::new(sub_kind_in_kind_bound(by, xn, rep, *domain_kind)),
            Box::new(sub_kind_in_kind_bound(by, xn, rep, *range_kind)),
        ),
        Kind::Record(record_element_kind) => Kind::Record(Box::new(sub_kind_in_kind_bound(
            by,
            xn,
            rep,
            *record_element_kind,
        ))),
        Kind::Tuple(components) => Kind::Tuple(
            components
                .into_iter()
                .map(|component_kind| sub_kind_in_kind_bound(by, xn, rep, component_kind))
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
fn lift_kind_in_con_bound(bound: usize, constructor: LocatedConstructor) -> LocatedConstructor {
    let span = constructor.span.clone();
    let node = match constructor.node {
        Constructor::TFun(domain, codomain) => Constructor::TFun(
            Box::new(lift_kind_in_con_bound(bound, *domain)),
            Box::new(lift_kind_in_con_bound(bound, *codomain)),
        ),
        Constructor::TCFun(exp, x, k, body) => Constructor::TCFun(
            exp,
            x,
            Box::new(lift_kind_in_kind_bound(1, bound, *k)),
            // TCFun is a constructor binder (not kind), so `bound` for kind variables is unchanged.
            Box::new(lift_kind_in_con_bound(bound, *body)),
        ),
        Constructor::TRecord(row) => {
            Constructor::TRecord(Box::new(lift_kind_in_con_bound(bound, *row)))
        }
        Constructor::TDisjoint(disjoint_left_row, disjoint_right_row, body_constructor) => {
            Constructor::TDisjoint(
                Box::new(lift_kind_in_con_bound(bound, *disjoint_left_row)),
                Box::new(lift_kind_in_con_bound(bound, *disjoint_right_row)),
                Box::new(lift_kind_in_con_bound(bound, *body_constructor)),
            )
        }
        Constructor::App(functor, argument) => Constructor::App(
            Box::new(lift_kind_in_con_bound(bound, *functor)),
            Box::new(lift_kind_in_con_bound(bound, *argument)),
        ),
        Constructor::Abs(x, k, body) => Constructor::Abs(
            x,
            Box::new(lift_kind_in_kind_bound(1, bound, *k)),
            Box::new(lift_kind_in_con_bound(bound, *body)),
        ),
        Constructor::KAbs(x, body) => {
            Constructor::KAbs(x, Box::new(lift_kind_in_con_bound(bound + 1, *body)))
        }
        Constructor::KApp(functor, kind_argument) => Constructor::KApp(
            Box::new(lift_kind_in_con_bound(bound, *functor)),
            Box::new(lift_kind_in_kind_bound(1, bound, *kind_argument)),
        ),
        Constructor::TKFun(x, body) => {
            Constructor::TKFun(x, Box::new(lift_kind_in_con_bound(bound + 1, *body)))
        }
        Constructor::Record(row_kind, field_pairs) => Constructor::Record(
            Box::new(lift_kind_in_kind_bound(1, bound, *row_kind)),
            field_pairs
                .into_iter()
                .map(|(field_name, field_type)| {
                    (
                        lift_kind_in_con_bound(bound, field_name),
                        lift_kind_in_con_bound(bound, field_type),
                    )
                })
                .collect(),
        ),
        Constructor::Concat(left_row, right_row) => Constructor::Concat(
            Box::new(lift_kind_in_con_bound(bound, *left_row)),
            Box::new(lift_kind_in_con_bound(bound, *right_row)),
        ),
        Constructor::Map(map_domain_kind, map_codomain_kind) => Constructor::Map(
            Box::new(lift_kind_in_kind_bound(1, bound, *map_domain_kind)),
            Box::new(lift_kind_in_kind_bound(1, bound, *map_codomain_kind)),
        ),
        Constructor::Tuple(elements) => Constructor::Tuple(
            elements
                .into_iter()
                .map(|element| lift_kind_in_con_bound(bound, element))
                .collect(),
        ),
        Constructor::Proj(base, index) => {
            Constructor::Proj(Box::new(lift_kind_in_con_bound(bound, *base)), index)
        }
        other => other,
    };
    Located { node, span }
}

// ---------------------------------------------------------------------------
// Public lifting / substitution API
// ---------------------------------------------------------------------------

/// Lift every free [`Kind::Rel`] de Bruijn index by 1 (enter one kind binder).
///
/// # Arguments
///
/// * `kind` — Kind to adjust.
///
/// # Returns
///
/// Kind with indices `n >= 0` incremented.
pub fn lift_kind_in_kind(kind: LocatedKind) -> LocatedKind {
    lift_kind_in_kind_bound(1, 0, kind)
}

/// Substitute `replacement` for [`Kind::Rel`] index `kind_index` in `kind`, adjusting other free indices.
///
/// # Arguments
///
/// * `kind_index` — de Bruijn level of the variable to replace.
/// * `replacement` — Kind substituted in; lifted across binders as in SML `subKindInKind`.
/// * `kind` — Kind to transform.
///
/// # Returns
///
/// Kind after substitution.
pub fn sub_kind_in_kind(
    kind_index: usize,
    replacement: &LocatedKind,
    kind: LocatedKind,
) -> LocatedKind {
    sub_kind_in_kind_bound(0, kind_index, replacement, kind)
}

/// Lift every free [`Kind::Rel`] inside `constructor` by 1 (cross one kind binder in `TCFun`, `Abs`, etc.).
///
/// # Arguments
///
/// * `constructor` — Constructor whose embedded kinds are adjusted.
///
/// # Returns
///
/// Constructor with incremented kind indices under those binders.
pub fn lift_kind_in_con(constructor: LocatedConstructor) -> LocatedConstructor {
    lift_kind_in_con_bound(0, constructor)
}

/// Substitute `replacement` for [`Kind::Rel`] `kind_index` throughout `constructor`.
///
/// # Arguments
///
/// * `kind_index` — Variable level to replace.
/// * `replacement` — Kind to splice in.
/// * `constructor` — Target constructor.
///
/// # Returns
///
/// Constructor after kind substitution.
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
    constructor: LocatedConstructor,
) -> LocatedConstructor {
    let span = constructor.span.clone();
    let node = match constructor.node {
        Constructor::TFun(domain, codomain) => Constructor::TFun(
            Box::new(sub_kind_in_con_inner(by, xn, rep, *domain)),
            Box::new(sub_kind_in_con_inner(by, xn, rep, *codomain)),
        ),
        Constructor::TCFun(exp, x, k, body) => Constructor::TCFun(
            exp,
            x,
            Box::new(sub_kind_in_kind_bound(by, xn, rep, *k)),
            // TCFun is a constructor binder (not kind), so kind-variable indices are unchanged.
            Box::new(sub_kind_in_con_inner(by, xn, rep, *body)),
        ),
        Constructor::TRecord(row) => {
            Constructor::TRecord(Box::new(sub_kind_in_con_inner(by, xn, rep, *row)))
        }
        Constructor::TDisjoint(disjoint_left_row, disjoint_right_row, body_constructor) => {
            Constructor::TDisjoint(
                Box::new(sub_kind_in_con_inner(by, xn, rep, *disjoint_left_row)),
                Box::new(sub_kind_in_con_inner(by, xn, rep, *disjoint_right_row)),
                Box::new(sub_kind_in_con_inner(by, xn, rep, *body_constructor)),
            )
        }
        Constructor::App(functor, argument) => Constructor::App(
            Box::new(sub_kind_in_con_inner(by, xn, rep, *functor)),
            Box::new(sub_kind_in_con_inner(by, xn, rep, *argument)),
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
        Constructor::KApp(functor, kind_argument) => Constructor::KApp(
            Box::new(sub_kind_in_con_inner(by, xn, rep, *functor)),
            Box::new(sub_kind_in_kind_bound(by, xn, rep, *kind_argument)),
        ),
        Constructor::TKFun(x, body) => Constructor::TKFun(
            x,
            Box::new(sub_kind_in_con_inner(by + 1, xn + 1, rep, *body)),
        ),
        Constructor::Record(row_kind, field_pairs) => Constructor::Record(
            Box::new(sub_kind_in_kind_bound(by, xn, rep, *row_kind)),
            field_pairs
                .into_iter()
                .map(|(field_name, field_type)| {
                    (
                        sub_kind_in_con_inner(by, xn, rep, field_name),
                        sub_kind_in_con_inner(by, xn, rep, field_type),
                    )
                })
                .collect(),
        ),
        Constructor::Concat(left_row, right_row) => Constructor::Concat(
            Box::new(sub_kind_in_con_inner(by, xn, rep, *left_row)),
            Box::new(sub_kind_in_con_inner(by, xn, rep, *right_row)),
        ),
        Constructor::Map(map_domain_kind, map_codomain_kind) => Constructor::Map(
            Box::new(sub_kind_in_kind_bound(by, xn, rep, *map_domain_kind)),
            Box::new(sub_kind_in_kind_bound(by, xn, rep, *map_codomain_kind)),
        ),
        Constructor::Tuple(elements) => Constructor::Tuple(
            elements
                .into_iter()
                .map(|element| sub_kind_in_con_inner(by, xn, rep, element))
                .collect(),
        ),
        Constructor::Proj(base, index) => {
            Constructor::Proj(Box::new(sub_kind_in_con_inner(by, xn, rep, *base)), index)
        }
        other => other,
    };
    Located { node, span }
}

// ---------------------------------------------------------------------------
// Con-in-Con lifting
// ---------------------------------------------------------------------------

/// Lift every free `Constructor::Rel(n)` inside a constructor by `by`, starting at `bound`.
fn lift_con_in_con_bound(
    by: usize,
    bound: usize,
    constructor: LocatedConstructor,
) -> LocatedConstructor {
    let span = constructor.span.clone();
    let node = match constructor.node {
        Constructor::Rel(n) => {
            if n < bound {
                Constructor::Rel(n) // bound: not lifted
            } else {
                // Use saturating_add: if `n` is a sentinel (e.g. usize::MAX from a failed lookup),
                // adding `by` would overflow; saturating keeps it large (still "unbound") safely.
                Constructor::Rel(n.saturating_add(by))
            }
        }
        // Unification variables track their nesting level; saturating prevents overflow on error paths.
        Constructor::Unif(nl, s, k, name, r) => {
            Constructor::Unif(nl.saturating_add(by), s, k, name, r)
        }
        Constructor::TFun(domain, codomain) => Constructor::TFun(
            Box::new(lift_con_in_con_bound(by, bound, *domain)),
            Box::new(lift_con_in_con_bound(by, bound, *codomain)),
        ),
        Constructor::TCFun(exp, x, k, body) => {
            // TCFun introduces a constructor binder, so increment `bound` so local Rel(0) is not lifted.
            Constructor::TCFun(
                exp,
                x,
                k,
                Box::new(lift_con_in_con_bound(by, bound + 1, *body)),
            )
        }
        Constructor::TRecord(row) => {
            Constructor::TRecord(Box::new(lift_con_in_con_bound(by, bound, *row)))
        }
        Constructor::TDisjoint(disjoint_left_row, disjoint_right_row, body_constructor) => {
            Constructor::TDisjoint(
                Box::new(lift_con_in_con_bound(by, bound, *disjoint_left_row)),
                Box::new(lift_con_in_con_bound(by, bound, *disjoint_right_row)),
                Box::new(lift_con_in_con_bound(by, bound, *body_constructor)),
            )
        }
        Constructor::App(functor, argument) => Constructor::App(
            Box::new(lift_con_in_con_bound(by, bound, *functor)),
            Box::new(lift_con_in_con_bound(by, bound, *argument)),
        ),
        Constructor::Abs(x, k, body) => {
            Constructor::Abs(x, k, Box::new(lift_con_in_con_bound(by, bound + 1, *body)))
        }
        Constructor::KAbs(x, body) => {
            Constructor::KAbs(x, Box::new(lift_con_in_con_bound(by, bound, *body)))
        }
        Constructor::KApp(functor, kind_argument) => Constructor::KApp(
            Box::new(lift_con_in_con_bound(by, bound, *functor)),
            kind_argument,
        ),
        Constructor::TKFun(x, body) => {
            Constructor::TKFun(x, Box::new(lift_con_in_con_bound(by, bound, *body)))
        }
        Constructor::Record(row_kind, field_pairs) => Constructor::Record(
            row_kind,
            field_pairs
                .into_iter()
                .map(|(field_name, field_type)| {
                    (
                        lift_con_in_con_bound(by, bound, field_name),
                        lift_con_in_con_bound(by, bound, field_type),
                    )
                })
                .collect(),
        ),
        Constructor::Concat(left_row, right_row) => Constructor::Concat(
            Box::new(lift_con_in_con_bound(by, bound, *left_row)),
            Box::new(lift_con_in_con_bound(by, bound, *right_row)),
        ),
        Constructor::Tuple(elements) => Constructor::Tuple(
            elements
                .into_iter()
                .map(|element| lift_con_in_con_bound(by, bound, element))
                .collect(),
        ),
        Constructor::Proj(base, index) => {
            Constructor::Proj(Box::new(lift_con_in_con_bound(by, bound, *base)), index)
        }
        other => other,
    };
    Located { node, span }
}

/// Lift every free [`Constructor::Rel`] inside `constructor` by 1 (one constructor binder).
///
/// # Arguments
///
/// * `constructor` — Elaborated constructor.
///
/// # Returns
///
/// Constructor with de Bruijn indices adjusted.
pub fn lift_con_in_con(constructor: LocatedConstructor) -> LocatedConstructor {
    lift_con_in_con_bound(1, 0, constructor)
}

// ---------------------------------------------------------------------------
// Squish: inverse of mlift_con_in_con (mirrors SML `squish`)
// ---------------------------------------------------------------------------

/// Shift all free [`Constructor::Rel`] indices down by `by`, raising on in-scope locals or Unif.
///
/// Mirrors `squish by` in `elaborate.sml`.  Used when storing a constructor solution into a
/// [`Constructor::Unif`] cell that has been lifted `by` times since creation — the inverse of
/// [`mlift_con_in_con`].  Any [`Constructor::Rel`] in `[0, by)` (local variables that would be
/// lost after squishing) and any [`Constructor::Unif`] node raise [`CantSquish`].
///
/// # Arguments
///
/// * `by` — Number of binder levels to squish out (the Unif's nesting level `nl`).
/// * `constructor` — Constructor computed at depth `by`; indices ≥ `by` are shifted down.
///
/// # Errors
///
/// [`CantSquish`] when a free [`Constructor::Rel`] in `[0, by)` or a [`Constructor::Unif`] is encountered.
///
/// # Returns
///
/// `Ok(constructor_at_depth_0)` on success.
pub fn squish_con(
    by: usize,
    constructor: LocatedConstructor,
) -> Result<LocatedConstructor, CantSquish> {
    if by == 0 {
        // Identity: no binders to squish.
        return Ok(constructor);
    }
    squish_con_bound(by, 0, constructor)
}

/// Raised when [`squish_con`] encounters a constructor that cannot be squished.
///
/// Mirrors `exception CantSquish` in `elaborate.sml`.
#[derive(Debug)]
pub struct CantSquish;

/// Recursive body of [`squish_con`]: `bound` tracks locally-bound constructor variables.
///
/// # Arguments
///
/// * `by` — Fixed: number of binders being squished.
/// * `bound` — Current depth of locally-bound constructor variables; increments inside binders.
/// * `constructor` — Sub-constructor to squish.
fn squish_con_bound(
    by: usize,
    bound: usize,
    constructor: LocatedConstructor,
) -> Result<LocatedConstructor, CantSquish> {
    let span = constructor.span.clone();
    let node = match constructor.node {
        Constructor::Rel(n) => {
            if n < bound {
                // Local variable (bound within this constructor's own binders): keep as-is.
                Constructor::Rel(n)
            } else if n < bound + by {
                // Free variable referencing one of the `by` binders being squished away: cannot squish.
                return Err(CantSquish);
            } else {
                // Outer variable beyond the squished range: shift index down by `by`.
                Constructor::Rel(n - by)
            }
        }
        Constructor::Unif(_, _, _, _, _) => {
            // Any unification variable blocks squishing (it might solve to a local reference).
            return Err(CantSquish);
        }
        Constructor::TFun(domain, codomain) => Constructor::TFun(
            Box::new(squish_con_bound(by, bound, *domain)?),
            Box::new(squish_con_bound(by, bound, *codomain)?),
        ),
        Constructor::TCFun(exp, x, k, body) => {
            // TCFun introduces a constructor binder: increment `bound` for the body.
            Constructor::TCFun(exp, x, k, Box::new(squish_con_bound(by, bound + 1, *body)?))
        }
        Constructor::TRecord(row) => {
            Constructor::TRecord(Box::new(squish_con_bound(by, bound, *row)?))
        }
        Constructor::TDisjoint(left_row, right_row, body_con) => Constructor::TDisjoint(
            Box::new(squish_con_bound(by, bound, *left_row)?),
            Box::new(squish_con_bound(by, bound, *right_row)?),
            Box::new(squish_con_bound(by, bound, *body_con)?),
        ),
        Constructor::App(functor, argument) => Constructor::App(
            Box::new(squish_con_bound(by, bound, *functor)?),
            Box::new(squish_con_bound(by, bound, *argument)?),
        ),
        Constructor::Abs(x, k, body) => {
            // Abs introduces a constructor binder: increment `bound` for the body.
            Constructor::Abs(x, k, Box::new(squish_con_bound(by, bound + 1, *body)?))
        }
        Constructor::KAbs(x, body) => {
            // KAbs is a kind binder, not a constructor binder: `bound` is unchanged.
            Constructor::KAbs(x, Box::new(squish_con_bound(by, bound, *body)?))
        }
        Constructor::KApp(functor, kind_argument) => Constructor::KApp(
            Box::new(squish_con_bound(by, bound, *functor)?),
            kind_argument,
        ),
        Constructor::TKFun(x, body) => {
            // TKFun is a kind binder, not a constructor binder: `bound` is unchanged.
            Constructor::TKFun(x, Box::new(squish_con_bound(by, bound, *body)?))
        }
        Constructor::Record(row_kind, field_pairs) => {
            let mut squished_pairs = Vec::with_capacity(field_pairs.len());
            for (field_name, field_type) in field_pairs {
                // Squish both the field name constructor and the field type constructor.
                squished_pairs.push((
                    squish_con_bound(by, bound, field_name)?,
                    squish_con_bound(by, bound, field_type)?,
                ));
            }
            Constructor::Record(row_kind, squished_pairs)
        }
        Constructor::Concat(left_row, right_row) => Constructor::Concat(
            Box::new(squish_con_bound(by, bound, *left_row)?),
            Box::new(squish_con_bound(by, bound, *right_row)?),
        ),
        Constructor::Tuple(elements) => {
            let mut squished = Vec::with_capacity(elements.len());
            for element in elements {
                squished.push(squish_con_bound(by, bound, element)?);
            }
            Constructor::Tuple(squished)
        }
        Constructor::Proj(base, index) => {
            Constructor::Proj(Box::new(squish_con_bound(by, bound, *base)?), index)
        }
        // All other constructor forms (Named, ModProj, Unit, Map, Name, Error, etc.) have no
        // free constructor Rel indices and cannot contain CantSquish-triggering sub-terms.
        other => other,
    };
    Ok(Located { node, span })
}

// ---------------------------------------------------------------------------
// Con-in-Con substitution
// ---------------------------------------------------------------------------

/// Substitution stopped at a forbidden unification-variable site (SML `SubUnif`).
///
/// See [`sub_con_in_con`].
#[derive(Debug)]
pub struct SubUnif;

/// Substitute `replacement` for [`Constructor::Rel`] `con_index` in `constructor`.
///
/// # Arguments
///
/// * `con_index` — de Bruijn index to replace.
/// * `replacement` — Constructor spliced in (lifted across intervening binders).
/// * `constructor` — Subject.
///
/// # Errors
///
/// [`SubUnif`] if a [`Constructor::Unif`] sentinel blocks substitution (mirrors `CUnif(~1, …)` in SML).
///
/// # Returns
///
/// `Ok(updated)` on success.
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
    constructor: LocatedConstructor,
) -> Result<LocatedConstructor, SubUnif> {
    let span = constructor.span.clone();
    let node = match constructor.node {
        Constructor::Rel(n) => {
            if n == xn {
                return Ok(lift_con_in_con_bound(by, 0, rep.clone()));
            } else if n > xn {
                Constructor::Rel(n - 1)
            } else {
                Constructor::Rel(n)
            }
        }
        // SML `subConInCon'`: `CUnif(~1, ...) → raise SubUnif; CUnif(n, ...) → CUnif(n-1, ...)`.
        // We represent SML's `-1` sentinel as `usize::MAX` (wrapping underflow from 0).
        // `wrapping_sub(1)` matches the SML decrement exactly: nl=0 → usize::MAX (= -1 sentinel),
        // and usize::MAX (already -1) is caught first and raises SubUnif.
        Constructor::Unif(nl, s, k, name, r) => match read_cunif(&r) {
            Some(known_constructor) => {
                // Keep parity with SML `ElabUtil.Con.mapB`, which traverses through solved constructor unifiers.
                let lifted_known_constructor = mlift_con_in_con(nl, known_constructor);
                // Continue substitution through the solved constructor instead of treating the cell as opaque.
                return sub_con_in_con_inner(by, xn, rep, lifted_known_constructor);
            }
            None => {
                if nl == usize::MAX {
                    // This Unif already holds the ~1 sentinel: block substitution.
                    return Err(SubUnif);
                }
                // Decrement nesting level by 1; nl=0 wraps to usize::MAX (the ~1 sentinel),
                // matching SML's CUnif(0) → CUnif(0-1) = CUnif(~1) behavior.
                Constructor::Unif(nl.wrapping_sub(1), s, k, name, r)
            }
        },
        Constructor::TFun(domain, codomain) => Constructor::TFun(
            Box::new(sub_con_in_con_inner(by, xn, rep, *domain)?),
            Box::new(sub_con_in_con_inner(by, xn, rep, *codomain)?),
        ),
        Constructor::TCFun(exp, x, k, body) => Constructor::TCFun(
            exp,
            x,
            k,
            // TCFun introduces a constructor binder, so increment by and xn
            Box::new(sub_con_in_con_inner(by + 1, xn + 1, rep, *body)?),
        ),
        Constructor::TRecord(row) => {
            Constructor::TRecord(Box::new(sub_con_in_con_inner(by, xn, rep, *row)?))
        }
        Constructor::TDisjoint(disjoint_left_row, disjoint_right_row, body_constructor) => {
            Constructor::TDisjoint(
                Box::new(sub_con_in_con_inner(by, xn, rep, *disjoint_left_row)?),
                Box::new(sub_con_in_con_inner(by, xn, rep, *disjoint_right_row)?),
                Box::new(sub_con_in_con_inner(by, xn, rep, *body_constructor)?),
            )
        }
        Constructor::App(functor, argument) => Constructor::App(
            Box::new(sub_con_in_con_inner(by, xn, rep, *functor)?),
            Box::new(sub_con_in_con_inner(by, xn, rep, *argument)?),
        ),
        Constructor::Abs(x, k, body) => Constructor::Abs(
            x,
            k,
            Box::new(sub_con_in_con_inner(by + 1, xn + 1, rep, *body)?),
        ),
        Constructor::KAbs(x, body) => {
            Constructor::KAbs(x, Box::new(sub_con_in_con_inner(by, xn, rep, *body)?))
        }
        Constructor::KApp(functor, kind_argument) => Constructor::KApp(
            Box::new(sub_con_in_con_inner(by, xn, rep, *functor)?),
            kind_argument,
        ),
        Constructor::TKFun(x, body) => {
            Constructor::TKFun(x, Box::new(sub_con_in_con_inner(by, xn, rep, *body)?))
        }
        Constructor::Record(row_kind, field_pairs) => {
            let mut new_field_pairs = Vec::with_capacity(field_pairs.len());
            for (field_name, field_type) in field_pairs {
                new_field_pairs.push((
                    sub_con_in_con_inner(by, xn, rep, field_name)?,
                    sub_con_in_con_inner(by, xn, rep, field_type)?,
                ));
            }
            Constructor::Record(row_kind, new_field_pairs)
        }
        Constructor::Concat(left_row, right_row) => Constructor::Concat(
            Box::new(sub_con_in_con_inner(by, xn, rep, *left_row)?),
            Box::new(sub_con_in_con_inner(by, xn, rep, *right_row)?),
        ),
        Constructor::Tuple(elements) => {
            let mut new_elements = Vec::with_capacity(elements.len());
            for element in elements {
                new_elements.push(sub_con_in_con_inner(by, xn, rep, element)?);
            }
            Constructor::Tuple(new_elements)
        }
        Constructor::Proj(base, index) => {
            Constructor::Proj(Box::new(sub_con_in_con_inner(by, xn, rep, *base)?), index)
        }
        other => other,
    };
    Ok(Located { node, span })
}

// ---------------------------------------------------------------------------
// Occurs check
// ---------------------------------------------------------------------------

/// Returns `true` if `Constructor::Rel(n)` appears free in `constructor` (at de Bruijn depth `bound`).
fn occurs_at(debruijn_index: usize, bound: usize, constructor: &LocatedConstructor) -> bool {
    match &constructor.node {
        Constructor::Rel(m) => *m == debruijn_index + bound,
        Constructor::TFun(domain, codomain) => {
            occurs_at(debruijn_index, bound, domain) || occurs_at(debruijn_index, bound, codomain)
        }
        // TCFun introduces a constructor binder: increment `bound` so the bound variable is not treated as free.
        Constructor::TCFun(_, _, _, body) => occurs_at(debruijn_index, bound + 1, body),
        Constructor::TRecord(row) => occurs_at(debruijn_index, bound, row),
        Constructor::TDisjoint(disjoint_left_row, disjoint_right_row, body_constructor) => {
            occurs_at(debruijn_index, bound, disjoint_left_row)
                || occurs_at(debruijn_index, bound, disjoint_right_row)
                || occurs_at(debruijn_index, bound, body_constructor)
        }
        Constructor::App(functor, argument) => {
            occurs_at(debruijn_index, bound, functor) || occurs_at(debruijn_index, bound, argument)
        }
        Constructor::Abs(_, _, body) => occurs_at(debruijn_index, bound + 1, body),
        Constructor::KAbs(_, body) => occurs_at(debruijn_index, bound, body),
        Constructor::KApp(functor, _) => occurs_at(debruijn_index, bound, functor),
        Constructor::TKFun(_, body) => occurs_at(debruijn_index, bound, body),
        Constructor::Record(_, field_pairs) => {
            field_pairs.iter().any(|(field_name, field_type)| {
                occurs_at(debruijn_index, bound, field_name)
                    || occurs_at(debruijn_index, bound, field_type)
            })
        }
        Constructor::Concat(left_row, right_row) => {
            occurs_at(debruijn_index, bound, left_row)
                || occurs_at(debruijn_index, bound, right_row)
        }
        Constructor::Tuple(elements) => elements
            .iter()
            .any(|element| occurs_at(debruijn_index, bound, element)),
        Constructor::Proj(base, _) => occurs_at(debruijn_index, bound, base),
        _ => false,
    }
}

/// Returns whether de Bruijn variable 0 occurs free in `constructor` (occurs-check helper).
///
/// # Arguments
///
/// * `constructor` — Constructor at the current binding depth.
///
/// # Returns
///
/// `true` if `Constructor::Rel(0)` appears free at the current binding depth.
pub fn occurs(constructor: &LocatedConstructor) -> bool {
    occurs_at(0, 0, constructor)
}

/// Returns whether constructor unification `unification_cell` occurs anywhere in `constructor`.
///
/// # Arguments
///
/// * `unification_cell` — [`CUnif`] reference cell (identity compared with [`Arc::ptr_eq`]).
/// * `constructor` — Constructor to search.
///
/// # Returns
///
/// `true` if any [`Constructor::Unif`] in `c` shares `r`.
pub fn occurs_cunif(unification_cell: &CUnifRef, constructor: &LocatedConstructor) -> bool {
    match &constructor.node {
        Constructor::Unif(_, _, _, _, other_cell) => Arc::ptr_eq(unification_cell, other_cell),
        Constructor::TFun(domain, codomain) => {
            occurs_cunif(unification_cell, domain) || occurs_cunif(unification_cell, codomain)
        }
        Constructor::TCFun(_, _, _, body) => occurs_cunif(unification_cell, body),
        Constructor::TRecord(row) => occurs_cunif(unification_cell, row),
        Constructor::TDisjoint(disjoint_left_row, disjoint_right_row, body_constructor) => {
            occurs_cunif(unification_cell, disjoint_left_row)
                || occurs_cunif(unification_cell, disjoint_right_row)
                || occurs_cunif(unification_cell, body_constructor)
        }
        Constructor::App(functor, argument) => {
            occurs_cunif(unification_cell, functor) || occurs_cunif(unification_cell, argument)
        }
        Constructor::Abs(_, _, body) => occurs_cunif(unification_cell, body),
        Constructor::KAbs(_, body) => occurs_cunif(unification_cell, body),
        Constructor::KApp(functor, _) => occurs_cunif(unification_cell, functor),
        Constructor::TKFun(_, body) => occurs_cunif(unification_cell, body),
        Constructor::Record(_, field_pairs) => {
            field_pairs.iter().any(|(field_name, field_type)| {
                occurs_cunif(unification_cell, field_name)
                    || occurs_cunif(unification_cell, field_type)
            })
        }
        Constructor::Concat(left_row, right_row) => {
            occurs_cunif(unification_cell, left_row) || occurs_cunif(unification_cell, right_row)
        }
        Constructor::Tuple(elements) => elements
            .iter()
            .any(|element| occurs_cunif(unification_cell, element)),
        Constructor::Proj(base, _) => occurs_cunif(unification_cell, base),
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

/// Reset internal normalisation counters (`identity` / `distribute` / `fuse` mirrors of SML refs).
///
/// # Returns
///
/// Nothing. Intended for tests or debugging.
pub fn reset_stats() {
    IDENTITY.store(0, Ordering::Relaxed);
    DISTRIBUTE.store(0, Ordering::Relaxed);
    FUSE.store(0, Ordering::Relaxed);
}

fn inc_distribute() {
    DISTRIBUTE.fetch_add(1, Ordering::Relaxed);
}

// ---------------------------------------------------------------------------
// Head-normalisation
// ---------------------------------------------------------------------------

/// Read through a solved unification variable, returning the stored constructor.
fn read_cunif(r: &CUnifRef) -> Option<LocatedConstructor> {
    match &*crate::compiler_diagnostics::lock_for_compile(r.as_ref(), "type operations CUnif cell")
    {
        CUnif::Known(c) => Some(*c.clone()),
        CUnif::Unknown => None,
    }
}

/// Upper bound on solved kind-unifier links peeled in one call.
const PEEL_SOLVED_KIND_UNIF_CHAIN_MAX_STEPS: usize = 8192;

/// Follow solved [`Kind::Unif`] / [`Kind::TupleUnif`] cells to a stable head.
fn hnorm_kind(mut kind: LocatedKind) -> LocatedKind {
    for _ in 0..PEEL_SOLVED_KIND_UNIF_CHAIN_MAX_STEPS {
        let reference = match &kind.node {
            Kind::Unif(_, _, reference) | Kind::TupleUnif(_, _, reference) => reference,
            _ => return kind,
        };
        let guard = crate::compiler_diagnostics::lock_for_compile(
            reference.as_ref(),
            "type operations KUnif cell",
        );
        if let crate::elaborated::KUnif::Known(inner) = &*guard {
            let next = *inner.clone();
            drop(guard);
            kind = next;
        } else {
            drop(guard);
            return kind;
        }
    }
    let span = kind.span.clone();
    Located::new(Kind::Error, span)
}

/// Lift all free [`Constructor::Rel`] indices in `constructor` by `binder_count` (multi-binder `mlift`).
///
/// # Arguments
///
/// * `binder_count` — Number of constructor binders entered.
/// * `constructor` — Subject.
///
/// # Returns
///
/// Constructor with adjusted indices.
pub fn mlift_con_in_con(
    binder_count: usize,
    constructor: LocatedConstructor,
) -> LocatedConstructor {
    lift_con_in_con_bound(binder_count, 0, constructor)
}

/// Upper bound on solved [`Constructor::Unif`] indirections peeled in one call.
///
/// Cycles or pathological chains must not spin without stack growth (LangSec / bounded work per request).
const PEEL_SOLVED_CONSTRUCTOR_UNIF_CHAIN_MAX_STEPS: usize = 8192;

/// Peel a chain of solved [`Constructor::Unif`] heads in one go (no one-frame-per-link recursion).
///
/// Long `Known` pointer chains from constructor unification can otherwise exhaust the stack before
/// [`hnorm_con`]'s depth counter runs out. Step cap returns [`Constructor::Error`] like excessive
/// [`hnorm_con`] depth (bad or cyclic instantiation graph).
///
/// # Arguments
///
/// * `constructor` — Elaborated constructor whose outermost nodes may be solved unifiers.
///
/// # Returns
///
/// First non-`Unif`, or the first `Unif` whose cell is still [`CUnif::Unknown`].
fn peel_solved_constructor_unif_chain(mut constructor: LocatedConstructor) -> LocatedConstructor {
    for _ in 0..PEEL_SOLVED_CONSTRUCTOR_UNIF_CHAIN_MAX_STEPS {
        match &constructor.node {
            Constructor::Unif(binder_count, _, _, _, reference) => match read_cunif(reference) {
                Some(inner) => {
                    constructor = mlift_con_in_con(*binder_count, inner); // Lift through `binder_count` binders.
                }
                None => return constructor,
            },
            _ => return constructor,
        }
    }
    let span = constructor.span.clone();
    Located::new(Constructor::Error, span)
}

/// Head-normalize a constructor: peel solved [`Constructor::Unif`], beta/eta, `KApp`/`Map`/`Concat`/`Proj` rules.
///
/// Translation of `hnormCon` from `elab_ops.sml`. No [`crate::elaborated::environment::Env`]:
/// [`Constructor::Named`] / [`Constructor::ModProj`] are not expanded to definitions here.
///
/// # Arguments
///
/// * `constructor` — Elaborated constructor.
///
/// # Returns
///
/// Head-normal form, or [`Constructor::Error`] if recursion depth exceeds 200 (guards cyclic unifiers).
pub fn hnorm_con(constructor: LocatedConstructor) -> LocatedConstructor {
    use std::cell::Cell;
    thread_local! {
        static HNORM_DEPTH: Cell<usize> = const { Cell::new(0) };
    }
    let d = HNORM_DEPTH.with(|c| {
        let v = c.get();
        c.set(v + 1);
        v
    });
    if d > 200 {
        HNORM_DEPTH.with(|c| c.set(0));
        let span = constructor.span.clone();
        return Located::new(Constructor::Error, span);
    }
    // Collapse solved-unifier prefixes iteratively so depth-200 only limits beta/eta steps, not chain length.
    let constructor = peel_solved_constructor_unif_chain(constructor);
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
                // NOTE: SML `hnormCon` only beta-reduces `App(CAbs, c2)`; `App(TCFun, c2)` falls
                // through to the default `c1' => (CApp((c1', loc), hnormCon env c2), loc)` arm.
                // TCFun is a universal constructor quantifier (∀ x :: K. body), NOT a lambda;
                // beta-reducing it here was incorrect and caused spurious constructor substitutions.
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
                                        Constructor::Record(k_inner, fields)
                                            if !fields.is_empty() =>
                                        {
                                            let fields = fields.clone();
                                            let k_inner = k_inner.clone();
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

/// Reduce a constructor by repeated head [`hnorm_con`] plus beta on `App(Abs(…), _)`.
///
/// Mirrors SML `reduceCon` without a full structural normalizer (avoids non-termination on cyclic unifiers).
/// Named / module-projected bodies are not loaded from the environment.
///
/// # Arguments
///
/// * `constructor` — Starting constructor.
///
/// # Returns
///
/// Constructor after head reduction steps succeed; otherwise the last stable head-normal form.
pub fn reduce_con(constructor: LocatedConstructor) -> LocatedConstructor {
    // Head-normalize first (follows Unif chains, beta/eta at the head).
    let r = hnorm_con(constructor);
    match r.node.clone() {
        Constructor::App(c_prime, x) => {
            let c_prime_norm = hnorm_con(*c_prime);
            match c_prime_norm.node.clone() {
                Constructor::Abs(_, _, body) => {
                    // Beta step: (λ. body) x → body[x/0]
                    if let Ok(subst) = sub_con_in_con(0, &x, *body) {
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

/// Cheap structural equality after [`hnorm_con`] (no unification; skips some kind checks in `Abs`).
///
/// Mirrors `consEqSimple` from `elab_ops.sml`.
///
/// # Arguments
///
/// * `left_constructor`, `right_constructor` — Constructors to compare.
///
/// # Returns
///
/// `true` when the simplified rules deem them equal (including same [`Constructor::Unif`] cell).
pub fn cons_eq_simple(
    left_constructor: &LocatedConstructor,
    right_constructor: &LocatedConstructor,
) -> bool {
    let left_normalized = hnorm_con(left_constructor.clone());
    let right_normalized = hnorm_con(right_constructor.clone());
    cons_eq_simple_normed(&left_normalized, &right_normalized)
}

fn kinds_eq_simple(left_kind: &LocatedKind, right_kind: &LocatedKind) -> bool {
    let left_normalized = hnorm_kind(left_kind.clone());
    let right_normalized = hnorm_kind(right_kind.clone());
    match (&left_normalized.node, &right_normalized.node) {
        (Kind::Rel(left_index), Kind::Rel(right_index)) => left_index == right_index,
        (Kind::Type, Kind::Type) => true,
        (Kind::Name, Kind::Name) => true,
        (Kind::Record(left_row_kind), Kind::Record(right_row_kind)) => {
            kinds_eq_simple(left_row_kind.as_ref(), right_row_kind.as_ref())
        }
        (Kind::Arrow(left_domain, left_range), Kind::Arrow(right_domain, right_range)) => {
            kinds_eq_simple(left_domain.as_ref(), right_domain.as_ref())
                && kinds_eq_simple(left_range.as_ref(), right_range.as_ref())
        }
        (Kind::Tuple(left_elements), Kind::Tuple(right_elements)) => {
            left_elements.len() == right_elements.len()
                && left_elements.iter().zip(right_elements.iter()).all(
                    |(left_element, right_element)| kinds_eq_simple(left_element, right_element),
                )
        }
        (Kind::Fun(_, left_body), Kind::Fun(_, right_body)) => {
            kinds_eq_simple(left_body.as_ref(), right_body.as_ref())
        }
        (Kind::Unif(_, _, left_cell), Kind::Unif(_, _, right_cell)) => {
            Arc::ptr_eq(left_cell, right_cell) // compare Arc pointer identity without redundant references
        }
        (Kind::Error, Kind::Error) => true,
        _ => false,
    }
}

fn cons_eq_simple_normed(left: &LocatedConstructor, right: &LocatedConstructor) -> bool {
    match (&left.node, &right.node) {
        (Constructor::Rel(left_index), Constructor::Rel(right_index)) => left_index == right_index,
        (Constructor::Named(left_id), Constructor::Named(right_id)) => left_id == right_id,
        (Constructor::ModProj(m1, path1, name1), Constructor::ModProj(m2, path2, name2)) => {
            m1 == m2 && path1 == path2 && name1 == name2
        }
        (Constructor::App(left_functor, left_arg), Constructor::App(right_functor, right_arg)) => {
            cons_eq_simple(left_functor, right_functor) && cons_eq_simple(left_arg, right_arg)
        }
        (
            Constructor::Abs(_, _left_kind, left_body),
            Constructor::Abs(_, _right_kind, right_body),
        ) => cons_eq_simple(left_body, right_body),
        (Constructor::KAbs(_, left_body), Constructor::KAbs(_, right_body)) => {
            cons_eq_simple(left_body, right_body)
        }
        (
            Constructor::KApp(left_functor, left_kind),
            Constructor::KApp(right_functor, right_kind),
        ) => cons_eq_simple(left_functor, right_functor) && kinds_eq_simple(left_kind, right_kind),
        (
            Constructor::TCFun(left_explicitness, _, left_kind, left_body),
            Constructor::TCFun(right_explicitness, _, right_kind, right_body),
        ) => {
            left_explicitness == right_explicitness
                && kinds_eq_simple(left_kind, right_kind)
                && cons_eq_simple(left_body, right_body)
        }
        (Constructor::Name(left_name), Constructor::Name(right_name)) => left_name == right_name,
        (Constructor::Record(_, left_fields), Constructor::Record(_, right_fields)) => {
            left_fields.len() == right_fields.len()
                && left_fields.iter().zip(right_fields.iter()).all(
                    |((left_field_name, left_field_type), (right_field_name, right_field_type))| {
                        cons_eq_simple(left_field_name, right_field_name)
                            && cons_eq_simple(left_field_type, right_field_type)
                    },
                )
        }
        (Constructor::Concat(left_a, left_b), Constructor::Concat(right_a, right_b)) => {
            cons_eq_simple(left_a, right_a) && cons_eq_simple(left_b, right_b)
        }
        (Constructor::Map(_, _), Constructor::Map(_, _)) => true,
        (Constructor::Unit, Constructor::Unit) => true,
        (Constructor::Tuple(left_elements), Constructor::Tuple(right_elements)) => {
            left_elements.len() == right_elements.len()
                && left_elements.iter().zip(right_elements.iter()).all(
                    |(left_element, right_element)| cons_eq_simple(left_element, right_element),
                )
        }
        (Constructor::Proj(left_base, left_index), Constructor::Proj(right_base, right_index)) => {
            left_index == right_index && cons_eq_simple(left_base, right_base)
        }
        (Constructor::Unif(_, _, _, _, left_cell), Constructor::Unif(_, _, _, _, right_cell)) => {
            Arc::ptr_eq(left_cell, right_cell)
        }
        (Constructor::TFun(left_dom, left_rng), Constructor::TFun(right_dom, right_rng)) => {
            cons_eq_simple(left_dom, right_dom) && cons_eq_simple(left_rng, right_rng)
        }
        (
            Constructor::TDisjoint(left_a, left_b, left_body),
            Constructor::TDisjoint(right_a, right_b, right_body),
        ) => {
            cons_eq_simple(left_a, right_a)
                && cons_eq_simple(left_b, right_b)
                && cons_eq_simple(left_body, right_body)
        }
        (Constructor::TRecord(left_row), Constructor::TRecord(right_row)) => {
            cons_eq_simple(left_row, right_row)
        }
        (Constructor::TKFun(_, left_body), Constructor::TKFun(_, right_body)) => {
            cons_eq_simple(left_body, right_body)
        }
        (Constructor::Error, Constructor::Error) => true,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Tests (catch missed mutants)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elaborated::{Constructor, Explicitness, Kind};
    use crate::error_types::Located;
    use anyhow::anyhow; // anyhow!() macro for error construction in tests
    use std::sync::{Arc, Mutex};

    fn dummy<T>(node: T) -> Located<T> {
        Located::dummy(node)
    }

    #[test]
    fn lift_kind_in_kind_rel_plus_one() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let k = dummy(Kind::Rel(0));
        let out = lift_kind_in_kind(k);
        assert!(matches!(out.node, Kind::Rel(1)));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn lift_kind_in_kind_bound_below_unchanged() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let k = dummy(Kind::Rel(0));
        let out = lift_kind_in_kind_bound(1, 1, k);
        assert!(matches!(out.node, Kind::Rel(0)));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sub_kind_in_kind_rel_zero_replaced() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let rep = dummy(Kind::Type);
        let k = dummy(Kind::Rel(0));
        let out = sub_kind_in_kind(0, &rep, k);
        assert!(matches!(out.node, Kind::Type));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sub_kind_in_kind_rel_above_decremented() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let rep = dummy(Kind::Type);
        let k = dummy(Kind::Rel(2));
        let out = sub_kind_in_kind(0, &rep, k);
        assert!(matches!(out.node, Kind::Rel(1)));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn occurs_rel_zero() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let c = dummy(Constructor::Rel(0));
        assert!(occurs(&c));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn occurs_unit_false() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let c = dummy(Constructor::Unit);
        assert!(!occurs(&c));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn occurs_at_rel_at_bound() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let c = dummy(Constructor::Rel(1));
        assert!(occurs_at(0, 1, &c));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn occurs_at_rel_mismatch_false() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let c = dummy(Constructor::Rel(2));
        assert!(!occurs_at(0, 1, &c));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn occurs_at_tfun_in_left() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let left = dummy(Constructor::Rel(0));
        let right = dummy(Constructor::Unit);
        let c = dummy(Constructor::TFun(Box::new(left), Box::new(right)));
        assert!(occurs_at(0, 0, &c));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn occurs_at_tfun_in_right() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let left = dummy(Constructor::Unit);
        let right = dummy(Constructor::Rel(0));
        let c = dummy(Constructor::TFun(Box::new(left), Box::new(right)));
        assert!(occurs_at(0, 0, &c));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn occurs_at_abs_shifts_bound() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // Under Abs, bound becomes bound+1; index 0 at outer is index 1 in body.
        let body = dummy(Constructor::Rel(2));
        let k = dummy(Kind::Type);
        let c = dummy(Constructor::Abs("x".into(), Box::new(k), Box::new(body)));
        assert!(occurs_at(0, 1, &c));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn occurs_at_app_in_fun() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let f = dummy(Constructor::Rel(0));
        let a = dummy(Constructor::Unit);
        let c = dummy(Constructor::App(Box::new(f), Box::new(a)));
        assert!(occurs_at(0, 0, &c));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn occurs_at_trecord_inner() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let inner = dummy(Constructor::Rel(0));
        let r = dummy(Constructor::TRecord(Box::new(inner)));
        assert!(occurs_at(0, 0, &r));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn lift_con_in_con_rel_plus_one() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let c = dummy(Constructor::Rel(0));
        let out = lift_con_in_con(c);
        assert!(matches!(out.node, Constructor::Rel(1)));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sub_con_in_con_rel_zero_replaced() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let rep = dummy(Constructor::Named(42));
        let c = dummy(Constructor::Rel(0));
        let out = match sub_con_in_con(0, &rep, c) {
            Ok(out) => out,
            Err(_) => return Err(anyhow!("expected substitution of Rel(0) to succeed")),
        };
        assert!(matches!(out.node, Constructor::Named(42)));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sub_con_in_con_rel_above_decremented() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let rep = dummy(Constructor::Unit);
        let c = dummy(Constructor::Rel(2));
        let out = match sub_con_in_con(0, &rep, c) {
            Ok(out) => out,
            Err(_) => {
                return Err(anyhow!(
                    "expected substitution of higher Rel index to succeed"
                ))
            }
        };
        assert!(matches!(out.node, Constructor::Rel(1)));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sub_con_in_con_peels_known_unif_before_sentinel_check() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // Build a solved constructor unifier whose stored constructor still contains the target Rel(0).
        let known_constructor = dummy(Constructor::Rel(0));
        // Store the solved constructor in the unification cell so substitution must traverse through it.
        let reference = Arc::new(Mutex::new(CUnif::Known(Box::new(known_constructor))));
        // Use a zero nesting level so a non-parity implementation would wrap to the ~1 sentinel on this node.
        let constructor = dummy(Constructor::Unif(
            0,
            crate::error_types::Span::dummy(),
            Box::new(dummy(Kind::Type)),
            "known".into(),
            reference,
        ));
        // Substitute a concrete constructor for Rel(0).
        let replacement = dummy(Constructor::Named(7));
        // The solved unifier should be traversed first, so substitution succeeds instead of producing SubUnif.
        let substituted_constructor = match sub_con_in_con(0, &replacement, constructor) {
            Ok(constructor) => constructor,
            Err(_) => {
                return Err(anyhow!(
                    "expected solved constructor unifier substitution to succeed"
                ));
            }
        };
        // The inner Rel(0) should be replaced by the requested constructor.
        assert!(matches!(
            substituted_constructor.node,
            Constructor::Named(7)
        ));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn cons_eq_simple_tfun_same() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let u = dummy(Constructor::Unit);
        let tfun = dummy(Constructor::TFun(Box::new(u.clone()), Box::new(u)));
        assert!(cons_eq_simple(&tfun, &tfun));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn cons_eq_simple_tuple_same() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let u = dummy(Constructor::Unit);
        let t = dummy(Constructor::Tuple(vec![u.clone(), u]));
        assert!(cons_eq_simple(&t, &t));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn cons_eq_simple_record_same() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let k = dummy(Kind::Type);
        let u = dummy(Constructor::Unit);
        let r = dummy(Constructor::Record(
            Box::new(k),
            vec![(dummy(Constructor::Name("x".into())), u)],
        ));
        assert!(cons_eq_simple(&r, &r));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn hnorm_does_not_beta_reduce_app_of_tcfun() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // SML hnormCon only beta-reduces App(CAbs, c), NOT App(TCFun, c).
        // TCFun is a forall/pi type (∀ x :: K. body); CApp(TCFun, c) is NOT
        // reducible in hnorm — the ECApp elaboration handles TCFun via substitution.
        // Constructor::Abs (CAbs in SML) is the constructor lambda; TCFun is the forall.
        let k = dummy(Kind::Type);
        let body = dummy(Constructor::Rel(0));
        let head = dummy(Constructor::TCFun(
            Explicitness::Implicit,
            "a".into(),
            Box::new(k),
            Box::new(body),
        ));
        let arg = dummy(Constructor::Unit);
        let app = dummy(Constructor::App(
            Box::new(head.clone()),
            Box::new(arg.clone()),
        ));
        let out = hnorm_con(app);
        // App(TCFun(...), Unit) should remain as App(...) — TCFun does not beta-reduce.
        assert!(
            matches!(&out.node, Constructor::App(h, _) if matches!(&h.node, Constructor::TCFun(..))),
            "App(TCFun, c) should not beta-reduce in hnorm_con (only App(Abs, c) does)"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn hnorm_con_unit_unchanged() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let c = dummy(Constructor::Unit);
        let out = hnorm_con(c);
        assert!(matches!(out.node, Constructor::Unit));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn reduce_con_unit_unchanged() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let c = dummy(Constructor::Unit);
        let out = reduce_con(c);
        assert!(matches!(out.node, Constructor::Unit));
        Ok(()) // return success to the test harness
    }
}
