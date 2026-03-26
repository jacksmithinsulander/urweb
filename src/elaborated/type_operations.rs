//! Constructor and kind substitution / normalization operations.
//!
//! Translated from `elab_ops.sml`.
//!
//! Public helpers document `# Arguments`, `# Returns`, and `# Errors` (including [`SubUnif`])
//! where de Bruijn level conventions are not obvious from types alone.

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
                Kind::Rel(n)
            } else {
                Kind::Rel(n + by)
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
            Box::new(lift_kind_in_con_bound(bound + 1, *body)),
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
            Box::new(sub_kind_in_con_inner(by + 1, xn + 1, rep, *body)),
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
                Constructor::Rel(n)
            } else {
                Constructor::Rel(n + by)
            }
        }
        // Unification variables track their nesting level
        Constructor::Unif(nl, s, k, name, r) => Constructor::Unif(nl + by, s, k, name, r),
        Constructor::TFun(domain, codomain) => Constructor::TFun(
            Box::new(lift_con_in_con_bound(by, bound, *domain)),
            Box::new(lift_con_in_con_bound(by, bound, *codomain)),
        ),
        Constructor::TCFun(exp, x, k, body) => {
            Constructor::TCFun(exp, x, k, Box::new(lift_con_in_con_bound(by, bound, *body)))
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
        Constructor::TCFun(_, _, _, body) => occurs_at(debruijn_index, bound, body),
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
    match &*crate::compiler_diagnostics::lock_for_compile(r.as_ref(), "type operations CUnif cell")
    {
        CUnif::Known(c) => Some(*c.clone()),
        CUnif::Unknown => None,
    }
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
        ) => {
            // Kind equality would require a kind comparison; we skip that for simplicity.
            cons_eq_simple(left_body, right_body)
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
        (Constructor::TRecord(left_row), Constructor::TRecord(right_row)) => {
            cons_eq_simple(left_row, right_row)
        }
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
