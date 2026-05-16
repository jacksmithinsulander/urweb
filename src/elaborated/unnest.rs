//! unnest — lambda-lift nested recursive definitions.
//!
//! Ports `unnest.sml`. Runs between elaborate and explify.

//!
//! Any `EDValRec` binding inside an `ELet` expression is hoisted to a
//! top-level `Declaration::ValRec`, with additional lambda parameters
//! for every free kind/constructor/expression variable it captures.
//!
//! `EDVal` bindings with function types are first converted to `EDValRec`
//! (matching the SML optimisation) so they too get hoisted.

use std::collections::BTreeSet;

use crate::diagnostics::{DiagnosticId, DiagnosticPayload};
use crate::elaborated::{
    Constructor, Declaration, ElaboratedDeclaration, Explicitness, Expression, File, Kind,
    LocatedConstructor, LocatedDeclaration, LocatedElaboratedDeclaration, LocatedExpression,
    LocatedKind, LocatedPattern, Pattern,
};
use crate::error_types::{ErrorReporter, Located};

// ---------------------------------------------------------------------------
// Lift / shift de Bruijn indices
// ---------------------------------------------------------------------------

/// Shift all `Constructor::Rel(n >= bound)` by `by` in a constructor.
fn lift_c(by: i64, bound: usize, c: LocatedConstructor) -> LocatedConstructor {
    let span = c.span.clone();
    let node = match c.node {
        Constructor::Rel(n) if n >= bound => Constructor::Rel((n as i64 + by) as usize),
        Constructor::TFun(a, b) => Constructor::TFun(
            Box::new(lift_c(by, bound, *a)),
            Box::new(lift_c(by, bound, *b)),
        ),
        Constructor::TCFun(expl, name, k, body) => {
            Constructor::TCFun(expl, name, k, Box::new(lift_c(by, bound + 1, *body)))
        }
        Constructor::TRecord(c2) => Constructor::TRecord(Box::new(lift_c(by, bound, *c2))),
        Constructor::TDisjoint(a, b, c2) => Constructor::TDisjoint(
            Box::new(lift_c(by, bound, *a)),
            Box::new(lift_c(by, bound, *b)),
            Box::new(lift_c(by, bound, *c2)),
        ),
        Constructor::App(f, x) => Constructor::App(
            Box::new(lift_c(by, bound, *f)),
            Box::new(lift_c(by, bound, *x)),
        ),
        Constructor::Abs(name, k, body) => {
            Constructor::Abs(name, k, Box::new(lift_c(by, bound + 1, *body)))
        }
        Constructor::KAbs(name, body) => {
            Constructor::KAbs(name, Box::new(lift_c(by, bound, *body)))
        }
        Constructor::KApp(f, k) => Constructor::KApp(Box::new(lift_c(by, bound, *f)), k),
        Constructor::TKFun(name, body) => {
            Constructor::TKFun(name, Box::new(lift_c(by, bound, *body)))
        }
        Constructor::Record(k, fields) => Constructor::Record(
            k,
            fields
                .into_iter()
                .map(|(n, v)| (lift_c(by, bound, n), lift_c(by, bound, v)))
                .collect(),
        ),
        Constructor::Concat(a, b) => Constructor::Concat(
            Box::new(lift_c(by, bound, *a)),
            Box::new(lift_c(by, bound, *b)),
        ),
        Constructor::Map(k1, k2) => Constructor::Map(k1, k2),
        Constructor::Tuple(cs) => {
            Constructor::Tuple(cs.into_iter().map(|c2| lift_c(by, bound, c2)).collect())
        }
        Constructor::Proj(c2, n) => Constructor::Proj(Box::new(lift_c(by, bound, *c2)), n),
        Constructor::Unif(nesting_level, span_ref, kind, name, reference) => Constructor::Unif(
            (nesting_level as i64 + by) as usize,
            span_ref,
            kind,
            name,
            reference,
        ),
        Constructor::Enum(arms) => Constructor::Enum(
            arms.into_iter()
                .map(|(tag_name, arguments)| {
                    (
                        tag_name,
                        arguments
                            .into_iter()
                            .map(|argument| lift_c(by, bound, argument))
                            .collect(),
                    )
                })
                .collect(),
        ),
        other => other,
    };
    Located::new(node, span)
}

/// Shift all `Constructor::Rel(n >= bound)` by `by` in constructors appearing inside an expression.
fn lift_c_in_e(by: i64, bound: usize, e: LocatedExpression) -> LocatedExpression {
    let span = e.span.clone();
    let node = match e.node {
        Expression::Prim(_)
        | Expression::Rel(_)
        | Expression::Named(_)
        | Expression::ModProj(_, _, _)
        | Expression::Error
        | Expression::Hole(_) => e.node,
        Expression::Unif(reference) => {
            let known_expression = {
                let guard = crate::compiler_diagnostics::lock_for_compile(
                    reference.as_ref(),
                    "unnest expression unification cell",
                );
                guard.clone()
            };
            match known_expression {
                Some(known_expression_value) => {
                    return lift_c_in_e(by, bound, known_expression_value)
                }
                None => Expression::Unif(reference),
            }
        }
        Expression::App(f, x) => Expression::App(
            Box::new(lift_c_in_e(by, bound, *f)),
            Box::new(lift_c_in_e(by, bound, *x)),
        ),
        Expression::Abs(name, dom, ran, body) => Expression::Abs(
            name,
            lift_c(by, bound, dom),
            lift_c(by, bound, ran),
            Box::new(lift_c_in_e(by, bound, *body)),
        ),
        Expression::CApp(f, c) => {
            Expression::CApp(Box::new(lift_c_in_e(by, bound, *f)), lift_c(by, bound, c))
        }
        Expression::CAbs(expl, name, k, body) => {
            Expression::CAbs(expl, name, k, Box::new(lift_c_in_e(by, bound + 1, *body)))
        }
        Expression::KAbs(name, body) => {
            Expression::KAbs(name, Box::new(lift_c_in_e(by, bound, *body)))
        }
        Expression::KApp(f, k) => Expression::KApp(Box::new(lift_c_in_e(by, bound, *f)), k),
        Expression::Record(fields) => Expression::Record(
            fields
                .into_iter()
                .map(|(n, v, t)| {
                    (
                        lift_c(by, bound, n),
                        lift_c_in_e(by, bound, v),
                        lift_c(by, bound, t),
                    )
                })
                .collect(),
        ),
        Expression::Field(e2, c, meta) => Expression::Field(
            Box::new(lift_c_in_e(by, bound, *e2)),
            lift_c(by, bound, c),
            crate::elaborated::FieldMeta {
                field: lift_c(by, bound, meta.field),
                rest: lift_c(by, bound, meta.rest),
            },
        ),
        Expression::Concat(a, c1, b, c2) => Expression::Concat(
            Box::new(lift_c_in_e(by, bound, *a)),
            lift_c(by, bound, c1),
            Box::new(lift_c_in_e(by, bound, *b)),
            lift_c(by, bound, c2),
        ),
        Expression::Cut(e2, c, meta) => Expression::Cut(
            Box::new(lift_c_in_e(by, bound, *e2)),
            lift_c(by, bound, c),
            crate::elaborated::FieldMeta {
                field: lift_c(by, bound, meta.field),
                rest: lift_c(by, bound, meta.rest),
            },
        ),
        Expression::CutMulti(e2, c, meta) => Expression::CutMulti(
            Box::new(lift_c_in_e(by, bound, *e2)),
            lift_c(by, bound, c),
            crate::elaborated::RestMeta {
                rest: lift_c(by, bound, meta.rest),
            },
        ),
        Expression::Case(disc, arms, meta) => Expression::Case(
            Box::new(lift_c_in_e(by, bound, *disc)),
            arms.into_iter()
                .map(|(p, arm)| (p, lift_c_in_e(by, bound, arm)))
                .collect(),
            crate::elaborated::CaseMeta {
                disc: lift_c(by, bound, meta.disc),
                result: lift_c(by, bound, meta.result),
            },
        ),
        Expression::Let(des, body, t) => {
            let mut cur_bound = bound;
            let des2: Vec<_> = des
                .into_iter()
                .map(|de| {
                    let span2 = de.span.clone();
                    let (node2, added) = match de.node {
                        ElaboratedDeclaration::Val(p, ty, e2) => {
                            let d = pat_bind_depth(&p);
                            let e2l = lift_c_in_e(by, cur_bound, e2);
                            (
                                ElaboratedDeclaration::Val(p, lift_c(by, cur_bound, ty), e2l),
                                d,
                            )
                        }
                        ElaboratedDeclaration::ValRec(vis) => {
                            let nr = vis.len();
                            let vis2 = vis
                                .into_iter()
                                .map(|(x, ty, e2)| {
                                    (
                                        x,
                                        lift_c(by, cur_bound, ty),
                                        lift_c_in_e(by, cur_bound + nr, e2),
                                    )
                                })
                                .collect();
                            (ElaboratedDeclaration::ValRec(vis2), nr)
                        }
                    };
                    cur_bound += added;
                    Located::new(node2, span2)
                })
                .collect();
            Expression::Let(
                des2,
                Box::new(lift_c_in_e(by, cur_bound, *body)),
                lift_c(by, bound, t),
            )
        }
    };
    Located::new(node, span)
}

/// Shift all `Expression::Rel(n >= bound)` by `by` in an expression.
fn lift_e(by: i64, bound: usize, e: LocatedExpression) -> LocatedExpression {
    let span = e.span.clone();
    let node = match e.node {
        Expression::Rel(n) if n >= bound => Expression::Rel((n as i64 + by) as usize),
        Expression::Unif(reference) => {
            let known_expression = {
                let guard = crate::compiler_diagnostics::lock_for_compile(
                    reference.as_ref(),
                    "unnest expression unification cell",
                );
                guard.clone()
            };
            match known_expression {
                Some(known_expression_value) => return lift_e(by, bound, known_expression_value),
                None => Expression::Unif(reference),
            }
        }
        Expression::App(f, x) => Expression::App(
            Box::new(lift_e(by, bound, *f)),
            Box::new(lift_e(by, bound, *x)),
        ),
        Expression::Abs(name, dom, ran, body) => {
            Expression::Abs(name, dom, ran, Box::new(lift_e(by, bound + 1, *body)))
        }
        Expression::CApp(f, c) => Expression::CApp(Box::new(lift_e(by, bound, *f)), c),
        Expression::CAbs(expl, name, k, body) => {
            Expression::CAbs(expl, name, k, Box::new(lift_e(by, bound, *body)))
        }
        Expression::KAbs(name, body) => Expression::KAbs(name, Box::new(lift_e(by, bound, *body))),
        Expression::KApp(f, k) => Expression::KApp(Box::new(lift_e(by, bound, *f)), k),
        Expression::Record(fields) => Expression::Record(
            fields
                .into_iter()
                .map(|(n, v, t)| (n, lift_e(by, bound, v), t))
                .collect(),
        ),
        Expression::Field(e2, c, meta) => {
            Expression::Field(Box::new(lift_e(by, bound, *e2)), c, meta)
        }
        Expression::Concat(a, c1, b, c2) => Expression::Concat(
            Box::new(lift_e(by, bound, *a)),
            c1,
            Box::new(lift_e(by, bound, *b)),
            c2,
        ),
        Expression::Cut(e2, c, meta) => Expression::Cut(Box::new(lift_e(by, bound, *e2)), c, meta),
        Expression::CutMulti(e2, c, meta) => {
            Expression::CutMulti(Box::new(lift_e(by, bound, *e2)), c, meta)
        }
        Expression::Case(disc, arms, meta) => Expression::Case(
            Box::new(lift_e(by, bound, *disc)),
            arms.into_iter()
                .map(|(p, arm)| {
                    let d = pat_bind_depth(&p);
                    (p, lift_e(by, bound + d, arm))
                })
                .collect(),
            meta,
        ),
        Expression::Let(des, body, t) => {
            let mut cur_bound = bound;
            let des2: Vec<_> = des
                .into_iter()
                .map(|de| {
                    let span2 = de.span.clone();
                    let (node2, added) = match de.node {
                        ElaboratedDeclaration::Val(p, ty, e2) => {
                            let d = pat_bind_depth(&p);
                            let e2l = lift_e(by, cur_bound, e2);
                            let added = d;
                            (ElaboratedDeclaration::Val(p, ty, e2l), added)
                        }
                        ElaboratedDeclaration::ValRec(vis) => {
                            let nr = vis.len();
                            let vis2 = vis
                                .into_iter()
                                .map(|(x, ty, e2)| (x, ty, lift_e(by, cur_bound + nr, e2)))
                                .collect();
                            (ElaboratedDeclaration::ValRec(vis2), nr)
                        }
                    };
                    cur_bound += added;
                    Located::new(node2, span2)
                })
                .collect();
            Expression::Let(des2, Box::new(lift_e(by, cur_bound, *body)), t)
        }
        other => other,
    };
    Located::new(node, span)
}

// ---------------------------------------------------------------------------
// Substitution: replace ERel(xn) with `rep`
// ---------------------------------------------------------------------------

/// Replace `Expression::Rel(xn)` with `rep` in `e`.
/// Unnest's local substitution only replaces exact matches; the later
/// `lift_e(-(by as i64), ...)` pass removes hoisted binders in one step.
fn sub_e(xn: usize, rep: &LocatedExpression, e: LocatedExpression) -> LocatedExpression {
    sub_e_bound(xn, 0, rep, e)
}

fn sub_e_bound(
    xn: usize,
    depth: usize,
    rep: &LocatedExpression,
    e: LocatedExpression,
) -> LocatedExpression {
    let span = e.span.clone();
    let node = match e.node {
        Expression::Rel(n) => {
            let abs_xn = xn + depth;
            if n == abs_xn {
                return lift_e(depth as i64, 0, rep.clone());
            } else {
                Expression::Rel(n)
            }
        }
        Expression::Unif(reference) => {
            let known_expression = {
                let guard = crate::compiler_diagnostics::lock_for_compile(
                    reference.as_ref(),
                    "unnest expression unification cell",
                );
                guard.clone()
            };
            match known_expression {
                Some(known_expression_value) => {
                    return sub_e_bound(xn, depth, rep, known_expression_value);
                }
                None => Expression::Unif(reference),
            }
        }
        Expression::App(f, x) => Expression::App(
            Box::new(sub_e_bound(xn, depth, rep, *f)),
            Box::new(sub_e_bound(xn, depth, rep, *x)),
        ),
        Expression::Abs(name, dom, ran, body) => Expression::Abs(
            name,
            dom,
            ran,
            Box::new(sub_e_bound(xn, depth + 1, rep, *body)),
        ),
        Expression::CApp(f, c) => Expression::CApp(Box::new(sub_e_bound(xn, depth, rep, *f)), c),
        Expression::CAbs(expl, name, k, body) => {
            let rep2 = lift_c_in_e(1, 0, rep.clone());
            Expression::CAbs(
                expl,
                name,
                k,
                Box::new(sub_e_bound(xn, depth, &rep2, *body)),
            )
        }
        Expression::KAbs(name, body) => {
            Expression::KAbs(name, Box::new(sub_e_bound(xn, depth, rep, *body)))
        }
        Expression::KApp(f, k) => Expression::KApp(Box::new(sub_e_bound(xn, depth, rep, *f)), k),
        Expression::Record(fields) => Expression::Record(
            fields
                .into_iter()
                .map(|(n, v, t)| (n, sub_e_bound(xn, depth, rep, v), t))
                .collect(),
        ),
        Expression::Field(e2, c, meta) => {
            Expression::Field(Box::new(sub_e_bound(xn, depth, rep, *e2)), c, meta)
        }
        Expression::Concat(a, c1, b, c2) => Expression::Concat(
            Box::new(sub_e_bound(xn, depth, rep, *a)),
            c1,
            Box::new(sub_e_bound(xn, depth, rep, *b)),
            c2,
        ),
        Expression::Cut(e2, c, meta) => {
            Expression::Cut(Box::new(sub_e_bound(xn, depth, rep, *e2)), c, meta)
        }
        Expression::CutMulti(e2, c, meta) => {
            Expression::CutMulti(Box::new(sub_e_bound(xn, depth, rep, *e2)), c, meta)
        }
        Expression::Case(disc, arms, meta) => Expression::Case(
            Box::new(sub_e_bound(xn, depth, rep, *disc)),
            arms.into_iter()
                .map(|(p, arm)| {
                    let d = pat_bind_depth(&p);
                    (p, sub_e_bound(xn, depth + d, rep, arm))
                })
                .collect(),
            meta,
        ),
        Expression::Let(des, body, t) => {
            let mut cur_depth = depth;
            let des2: Vec<_> = des
                .into_iter()
                .map(|de| {
                    let span2 = de.span.clone();
                    let (node2, added) = match de.node {
                        ElaboratedDeclaration::Val(p, ty, e2) => {
                            let d = pat_bind_depth(&p);
                            let e2s = sub_e_bound(xn, cur_depth, rep, e2);
                            let added = d;
                            (ElaboratedDeclaration::Val(p, ty, e2s), added)
                        }
                        ElaboratedDeclaration::ValRec(vis) => {
                            let nr = vis.len();
                            let vis2 = vis
                                .into_iter()
                                .map(|(x, ty, e2)| {
                                    (x, ty, sub_e_bound(xn, cur_depth + nr, rep, e2))
                                })
                                .collect();
                            (ElaboratedDeclaration::ValRec(vis2), nr)
                        }
                    };
                    cur_depth += added;
                    Located::new(node2, span2)
                })
                .collect();
            Expression::Let(des2, Box::new(sub_e_bound(xn, cur_depth, rep, *body)), t)
        }
        other => other,
    };
    Located::new(node, span)
}

fn apply_subs(subs: &[(usize, LocatedExpression)], e: LocatedExpression) -> LocatedExpression {
    subs.iter().fold(e, |acc, (xn, rep)| sub_e(*xn, rep, acc))
}

// ---------------------------------------------------------------------------
// Pattern binding depth
// ---------------------------------------------------------------------------

fn pat_bind_depth(p: &LocatedPattern) -> usize {
    match &p.node {
        Pattern::Var(_, _) => 1,
        Pattern::Prim(_) => 0,
        Pattern::Constructor(_, _, _, inner) => inner.as_ref().map_or(0, |p| pat_bind_depth(p)),
        Pattern::Record(fields) => fields.iter().map(|(_, p, _)| pat_bind_depth(p)).sum(),
    }
}

/// Collect pattern-bound expression variables in the same innermost-first order
/// produced by `pat_binds` during elaboration.
fn pattern_bindings_env_order(pattern: &LocatedPattern) -> Vec<(String, LocatedConstructor)> {
    fn collect(pattern: &LocatedPattern, bindings: &mut Vec<(String, LocatedConstructor)>) {
        match &pattern.node {
            Pattern::Var(name, type_con) => {
                bindings.insert(0, (name.clone(), type_con.clone()));
            }
            Pattern::Prim(_) => {}
            Pattern::Constructor(_, _, _, None) => {}
            Pattern::Constructor(_, _, _, Some(inner_pattern)) => {
                collect(inner_pattern, bindings);
            }
            Pattern::Record(fields) => {
                for (_, sub_pattern, _) in fields {
                    collect(sub_pattern, bindings);
                }
            }
        }
    }

    let mut bindings = Vec::new();
    collect(pattern, &mut bindings);
    bindings
}

// ---------------------------------------------------------------------------
// Free variable computation
// ---------------------------------------------------------------------------

/// Free kind variables in a kind (indices >= `kbound`, adjusted to 0-based).
fn fvs_kind(kbound: usize, k: &LocatedKind) -> BTreeSet<usize> {
    let mut out = BTreeSet::new();
    fvs_kind_acc(kbound, k, &mut out);
    out
}

fn fvs_kind_acc(kbound: usize, k: &LocatedKind, out: &mut BTreeSet<usize>) {
    match &k.node {
        Kind::Rel(n) if *n >= kbound => {
            out.insert(n - kbound);
        }
        Kind::Arrow(a, b) => {
            // Recurse into both sides of an explicit kind arrow.
            fvs_kind_acc(kbound, a, out);
            fvs_kind_acc(kbound, b, out);
        }
        Kind::KFun(body) => {
            // KFun binds one kind variable; increment bound before recursing into body.
            fvs_kind_acc(kbound + 1, body, out);
        }
        Kind::Record(k2) => fvs_kind_acc(kbound, k2, out),
        Kind::Tuple(ks) => ks.iter().for_each(|k2| fvs_kind_acc(kbound, k2, out)),
        Kind::Unif(_, _, reference) | Kind::TupleUnif(_, _, reference) => {
            let known_kind = {
                let guard = crate::compiler_diagnostics::lock_for_compile(
                    reference.as_ref(),
                    "unnest kind unification cell",
                );
                match &*guard {
                    crate::elaborated::KUnif::Known(known) => Some(*known.clone()),
                    crate::elaborated::KUnif::Unknown => None,
                }
            };
            match (&k.node, known_kind) {
                (_, Some(known_kind_value)) => fvs_kind_acc(kbound, &known_kind_value, out),
                (Kind::TupleUnif(_, pairs, _), None) => {
                    pairs
                        .iter()
                        .for_each(|(_, kind_item)| fvs_kind_acc(kbound, kind_item, out));
                }
                _ => {}
            }
        }
        _ => {}
    }
}

/// Free (kind, con) variables in a constructor.
fn fvs_con(kb: usize, cb: usize, c: &LocatedConstructor) -> (BTreeSet<usize>, BTreeSet<usize>) {
    let mut kvs = BTreeSet::new();
    let mut cvs = BTreeSet::new();
    fvs_con_acc(kb, cb, c, &mut kvs, &mut cvs);
    (kvs, cvs)
}

fn fvs_con_acc(
    kb: usize,
    cb: usize,
    c: &LocatedConstructor,
    kvs: &mut BTreeSet<usize>,
    cvs: &mut BTreeSet<usize>,
) {
    match &c.node {
        Constructor::Rel(n) if *n >= cb => {
            cvs.insert(n - cb);
        }
        Constructor::TFun(a, b) => {
            fvs_con_acc(kb, cb, a, kvs, cvs);
            fvs_con_acc(kb, cb, b, kvs, cvs);
        }
        Constructor::TCFun(_, _, k, body) => {
            fvs_kind_acc(kb, k, kvs);
            fvs_con_acc(kb, cb + 1, body, kvs, cvs);
        }
        Constructor::TRecord(c2) => fvs_con_acc(kb, cb, c2, kvs, cvs),
        Constructor::TDisjoint(a, b, c2) => {
            fvs_con_acc(kb, cb, a, kvs, cvs);
            fvs_con_acc(kb, cb, b, kvs, cvs);
            fvs_con_acc(kb, cb, c2, kvs, cvs);
        }
        Constructor::App(f, x) => {
            fvs_con_acc(kb, cb, f, kvs, cvs);
            fvs_con_acc(kb, cb, x, kvs, cvs);
        }
        Constructor::Abs(_, k, body) => {
            fvs_kind_acc(kb, k, kvs);
            fvs_con_acc(kb, cb + 1, body, kvs, cvs);
        }
        Constructor::KAbs(_, body) => fvs_con_acc(kb + 1, cb, body, kvs, cvs),
        Constructor::KApp(f, k) => {
            fvs_con_acc(kb, cb, f, kvs, cvs);
            fvs_kind_acc(kb, k, kvs);
        }
        Constructor::TKFun(_, body) => fvs_con_acc(kb + 1, cb, body, kvs, cvs),
        Constructor::Record(k, fields) => {
            fvs_kind_acc(kb, k, kvs);
            for (n, v) in fields {
                fvs_con_acc(kb, cb, n, kvs, cvs);
                fvs_con_acc(kb, cb, v, kvs, cvs);
            }
        }
        Constructor::Concat(a, b) => {
            fvs_con_acc(kb, cb, a, kvs, cvs);
            fvs_con_acc(kb, cb, b, kvs, cvs);
        }
        Constructor::Map(k1, k2) => {
            fvs_kind_acc(kb, k1, kvs);
            fvs_kind_acc(kb, k2, kvs);
        }
        Constructor::Tuple(cs) => cs.iter().for_each(|c2| fvs_con_acc(kb, cb, c2, kvs, cvs)),
        Constructor::Proj(c2, _) => fvs_con_acc(kb, cb, c2, kvs, cvs),
        Constructor::Unif(nesting_level, _, _, _, reference) => {
            let known_constructor = {
                let guard = crate::compiler_diagnostics::lock_for_compile(
                    reference.as_ref(),
                    "unnest constructor unification cell",
                );
                match &*guard {
                    crate::elaborated::CUnif::Known(known) => Some(*known.clone()),
                    crate::elaborated::CUnif::Unknown(_) => None,
                }
            };
            if let Some(known_constructor_value) = known_constructor {
                let lifted = lift_c(*nesting_level as i64, 0, known_constructor_value);
                fvs_con_acc(kb, cb, &lifted, kvs, cvs);
            }
        }
        Constructor::Enum(arms) => {
            for (_, arguments) in arms {
                arguments
                    .iter()
                    .for_each(|argument| fvs_con_acc(kb, cb, argument, kvs, cvs));
            }
        }
        _ => {}
    }
}

/// Free (kind, con, exp) variables in an expression.
/// `nr` = number of recursive definitions in scope that are NOT free.
fn fvs_exp(
    kb: usize,
    cb: usize,
    eb: usize,
    nr: usize,
    e: &LocatedExpression,
) -> (BTreeSet<usize>, BTreeSet<usize>, BTreeSet<usize>) {
    let mut kvs = BTreeSet::new();
    let mut cvs = BTreeSet::new();
    let mut evs = BTreeSet::new();
    fvs_exp_acc(kb, cb, eb + nr, e, &mut kvs, &mut cvs, &mut evs);
    (kvs, cvs, evs)
}

fn fvs_exp_acc(
    kb: usize,
    cb: usize,
    eb: usize,
    e: &LocatedExpression,
    kvs: &mut BTreeSet<usize>,
    cvs: &mut BTreeSet<usize>,
    evs: &mut BTreeSet<usize>,
) {
    match &e.node {
        Expression::Rel(n) if *n >= eb => {
            evs.insert(n - eb);
        }
        Expression::Unif(reference) => {
            let known_expression = {
                let guard = crate::compiler_diagnostics::lock_for_compile(
                    reference.as_ref(),
                    "unnest expression unification cell",
                );
                guard.clone()
            };
            if let Some(known_expression_value) = known_expression {
                fvs_exp_acc(kb, cb, eb, &known_expression_value, kvs, cvs, evs);
            }
        }
        Expression::App(f, x) => {
            fvs_exp_acc(kb, cb, eb, f, kvs, cvs, evs);
            fvs_exp_acc(kb, cb, eb, x, kvs, cvs, evs);
        }
        Expression::Abs(_, dom, ran, body) => {
            fvs_con_acc(kb, cb, dom, kvs, cvs);
            fvs_con_acc(kb, cb, ran, kvs, cvs);
            fvs_exp_acc(kb, cb, eb + 1, body, kvs, cvs, evs);
        }
        Expression::CApp(f, c) => {
            fvs_exp_acc(kb, cb, eb, f, kvs, cvs, evs);
            fvs_con_acc(kb, cb, c, kvs, cvs);
        }
        Expression::CAbs(_, _, k, body) => {
            fvs_kind_acc(kb, k, kvs);
            fvs_exp_acc(kb, cb + 1, eb, body, kvs, cvs, evs);
        }
        Expression::KAbs(_, body) => fvs_exp_acc(kb + 1, cb, eb, body, kvs, cvs, evs),
        Expression::KApp(f, k) => {
            fvs_exp_acc(kb, cb, eb, f, kvs, cvs, evs);
            fvs_kind_acc(kb, k, kvs);
        }
        Expression::Record(fields) => {
            for (n, v, t) in fields {
                fvs_con_acc(kb, cb, n, kvs, cvs);
                fvs_exp_acc(kb, cb, eb, v, kvs, cvs, evs);
                fvs_con_acc(kb, cb, t, kvs, cvs);
            }
        }
        Expression::Field(e2, c, meta) => {
            fvs_exp_acc(kb, cb, eb, e2, kvs, cvs, evs);
            fvs_con_acc(kb, cb, c, kvs, cvs);
            fvs_con_acc(kb, cb, &meta.field, kvs, cvs);
            fvs_con_acc(kb, cb, &meta.rest, kvs, cvs);
        }
        Expression::Concat(a, c1, b, c2) => {
            fvs_exp_acc(kb, cb, eb, a, kvs, cvs, evs);
            fvs_con_acc(kb, cb, c1, kvs, cvs);
            fvs_exp_acc(kb, cb, eb, b, kvs, cvs, evs);
            fvs_con_acc(kb, cb, c2, kvs, cvs);
        }
        Expression::Cut(e2, c, meta) => {
            fvs_exp_acc(kb, cb, eb, e2, kvs, cvs, evs);
            fvs_con_acc(kb, cb, c, kvs, cvs);
            fvs_con_acc(kb, cb, &meta.field, kvs, cvs);
            fvs_con_acc(kb, cb, &meta.rest, kvs, cvs);
        }
        Expression::CutMulti(e2, c, meta) => {
            fvs_exp_acc(kb, cb, eb, e2, kvs, cvs, evs);
            fvs_con_acc(kb, cb, c, kvs, cvs);
            fvs_con_acc(kb, cb, &meta.rest, kvs, cvs);
        }
        Expression::Case(disc, arms, meta) => {
            fvs_exp_acc(kb, cb, eb, disc, kvs, cvs, evs);
            fvs_con_acc(kb, cb, &meta.disc, kvs, cvs);
            fvs_con_acc(kb, cb, &meta.result, kvs, cvs);
            for (p, arm) in arms {
                let d = pat_bind_depth(p);
                fvs_exp_acc(kb, cb, eb + d, arm, kvs, cvs, evs);
            }
        }
        Expression::Let(des, body, _) => {
            let mut cur_eb = eb;
            for de in des {
                match &de.node {
                    ElaboratedDeclaration::Val(p, ty, e2) => {
                        fvs_con_acc(kb, cb, ty, kvs, cvs);
                        fvs_exp_acc(kb, cb, cur_eb, e2, kvs, cvs, evs);
                        cur_eb += pat_bind_depth(p);
                    }
                    ElaboratedDeclaration::ValRec(vis) => {
                        let nr2 = vis.len();
                        for (_, ty, e2) in vis {
                            fvs_con_acc(kb, cb, ty, kvs, cvs);
                            fvs_exp_acc(kb, cb, cur_eb + nr2, e2, kvs, cvs, evs);
                        }
                        cur_eb += nr2;
                    }
                }
            }
            fvs_exp_acc(kb, cb, cur_eb, body, kvs, cvs, evs);
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Squishing: remap free variable indices to captured set
// ---------------------------------------------------------------------------

fn position_of(
    x: usize,
    list: &[usize],
    context: &str,
    span: &crate::error_types::Span,
    errors: &mut ErrorReporter,
) -> usize {
    list.iter().position(|&v| v == x).unwrap_or_else(|| {
        if std::env::var("URWEB_DEBUG_UNNEST_REMAP").ok().as_deref() == Some("1") {
            eprintln!(
                "unnest remap debug context={} missing={} list={:?} span={}:{}",
                context, x, list, span.file, span.first.line,
            );
        }
        errors.report_type_at(
            span.clone(),
            DiagnosticPayload::new(
                DiagnosticId::UnnestRemapFailedInternal,
                vec![x.to_string(), format!("{list:?}")],
            ),
        );
        0
    })
}

/// Remap free kind variables in `k` to use positions in `kfv`.
#[allow(dead_code)]
fn squish_k(kfv: &[usize], k: LocatedKind, errors: &mut ErrorReporter) -> LocatedKind {
    squish_k_bound(0, kfv, k, errors)
}

fn squish_k_bound(
    kb: usize,
    kfv: &[usize],
    k: LocatedKind,
    errors: &mut ErrorReporter,
) -> LocatedKind {
    let span = k.span.clone();
    let node = match k.node {
        Kind::Rel(n) if n >= kb => Kind::Rel(position_of(n - kb, kfv, "kind", &span, errors) + kb),
        Kind::Arrow(a, b) => Kind::Arrow(
            Box::new(squish_k_bound(kb, kfv, *a, errors)),
            Box::new(squish_k_bound(kb, kfv, *b, errors)),
        ),
        Kind::KFun(body) => Kind::KFun(Box::new(squish_k_bound(kb + 1, kfv, *body, errors))),
        Kind::Record(inner) => Kind::Record(Box::new(squish_k_bound(kb, kfv, *inner, errors))),
        Kind::Tuple(items) => Kind::Tuple(
            items
                .into_iter()
                .map(|item| squish_k_bound(kb, kfv, item, errors))
                .collect(),
        ),
        Kind::Unif(span_inner, debug_name, reference) => {
            let known_kind = {
                let guard = crate::compiler_diagnostics::lock_for_compile(
                    reference.as_ref(),
                    "unnest kind unification cell",
                );
                match &*guard {
                    crate::elaborated::KUnif::Known(known) => Some(*known.clone()),
                    crate::elaborated::KUnif::Unknown => None,
                }
            };
            match known_kind {
                Some(known_kind_value) => return squish_k_bound(kb, kfv, known_kind_value, errors),
                None => Kind::Unif(span_inner, debug_name, reference),
            }
        }
        Kind::TupleUnif(span_inner, items, reference) => {
            let known_kind = {
                let guard = crate::compiler_diagnostics::lock_for_compile(
                    reference.as_ref(),
                    "unnest kind unification cell",
                );
                match &*guard {
                    crate::elaborated::KUnif::Known(known) => Some(*known.clone()),
                    crate::elaborated::KUnif::Unknown => None,
                }
            };
            match known_kind {
                Some(known_kind_value) => return squish_k_bound(kb, kfv, known_kind_value, errors),
                None => Kind::TupleUnif(
                    span_inner,
                    items
                        .into_iter()
                        .map(|(index, item)| (index, squish_k_bound(kb, kfv, item, errors)))
                        .collect(),
                    reference,
                ),
            }
        }
        other => other,
    };
    Located::new(node, span)
}

/// Remap free constructor variables in `c` to use positions in `kfv`/`cfv`.
fn squish_c(
    kfv: &[usize],
    cfv: &[usize],
    c: LocatedConstructor,
    errors: &mut ErrorReporter,
) -> LocatedConstructor {
    squish_c_bound(0, 0, kfv, cfv, c, errors)
}

fn squish_c_bound(
    kb: usize,
    cb: usize,
    kfv: &[usize],
    cfv: &[usize],
    c: LocatedConstructor,
    errors: &mut ErrorReporter,
) -> LocatedConstructor {
    let span = c.span.clone();
    let node = match c.node {
        Constructor::Rel(n) if n >= cb => {
            Constructor::Rel(position_of(n - cb, cfv, "con", &span, errors) + cb)
        }
        Constructor::TFun(a, b) => Constructor::TFun(
            Box::new(squish_c_bound(kb, cb, kfv, cfv, *a, errors)),
            Box::new(squish_c_bound(kb, cb, kfv, cfv, *b, errors)),
        ),
        Constructor::TCFun(expl, name, k, body) => Constructor::TCFun(
            expl,
            name,
            Box::new(squish_k_bound(kb, kfv, *k, errors)),
            Box::new(squish_c_bound(kb, cb + 1, kfv, cfv, *body, errors)),
        ),
        Constructor::TRecord(c2) => {
            Constructor::TRecord(Box::new(squish_c_bound(kb, cb, kfv, cfv, *c2, errors)))
        }
        Constructor::TDisjoint(a, b, c2) => Constructor::TDisjoint(
            Box::new(squish_c_bound(kb, cb, kfv, cfv, *a, errors)),
            Box::new(squish_c_bound(kb, cb, kfv, cfv, *b, errors)),
            Box::new(squish_c_bound(kb, cb, kfv, cfv, *c2, errors)),
        ),
        Constructor::App(f, x) => Constructor::App(
            Box::new(squish_c_bound(kb, cb, kfv, cfv, *f, errors)),
            Box::new(squish_c_bound(kb, cb, kfv, cfv, *x, errors)),
        ),
        Constructor::Abs(name, k, body) => Constructor::Abs(
            name,
            Box::new(squish_k_bound(kb, kfv, *k, errors)),
            Box::new(squish_c_bound(kb, cb + 1, kfv, cfv, *body, errors)),
        ),
        Constructor::KAbs(name, body) => Constructor::KAbs(
            name,
            Box::new(squish_c_bound(kb + 1, cb, kfv, cfv, *body, errors)),
        ),
        Constructor::KApp(f, k) => Constructor::KApp(
            Box::new(squish_c_bound(kb, cb, kfv, cfv, *f, errors)),
            Box::new(squish_k_bound(kb, kfv, *k, errors)),
        ),
        Constructor::TKFun(name, body) => Constructor::TKFun(
            name,
            Box::new(squish_c_bound(kb + 1, cb, kfv, cfv, *body, errors)),
        ),
        Constructor::Record(k, fields) => Constructor::Record(
            Box::new(squish_k_bound(kb, kfv, *k, errors)),
            fields
                .into_iter()
                .map(|(n, v)| {
                    (
                        squish_c_bound(kb, cb, kfv, cfv, n, errors),
                        squish_c_bound(kb, cb, kfv, cfv, v, errors),
                    )
                })
                .collect(),
        ),
        Constructor::Concat(a, b) => Constructor::Concat(
            Box::new(squish_c_bound(kb, cb, kfv, cfv, *a, errors)),
            Box::new(squish_c_bound(kb, cb, kfv, cfv, *b, errors)),
        ),
        Constructor::Map(k1, k2) => Constructor::Map(
            Box::new(squish_k_bound(kb, kfv, *k1, errors)),
            Box::new(squish_k_bound(kb, kfv, *k2, errors)),
        ),
        Constructor::Tuple(cs) => Constructor::Tuple(
            cs.into_iter()
                .map(|c2| squish_c_bound(kb, cb, kfv, cfv, c2, errors))
                .collect(),
        ),
        Constructor::Proj(c2, n) => {
            Constructor::Proj(Box::new(squish_c_bound(kb, cb, kfv, cfv, *c2, errors)), n)
        }
        Constructor::Unif(nesting_level, span_ref, kind_state, debug_name, reference) => {
            let known_constructor = {
                let guard = crate::compiler_diagnostics::lock_for_compile(
                    reference.as_ref(),
                    "unnest constructor unification cell",
                );
                match &*guard {
                    crate::elaborated::CUnif::Known(known) => Some(*known.clone()),
                    crate::elaborated::CUnif::Unknown(_) => None,
                }
            };
            match known_constructor {
                Some(known_constructor_value) => {
                    let lifted = lift_c(nesting_level as i64, 0, known_constructor_value);
                    return squish_c_bound(kb, cb, kfv, cfv, lifted, errors);
                }
                None => {
                    Constructor::Unif(nesting_level, span_ref, kind_state, debug_name, reference)
                }
            }
        }
        Constructor::Enum(arms) => Constructor::Enum(
            arms.into_iter()
                .map(|(tag_name, arguments)| {
                    (
                        tag_name,
                        arguments
                            .into_iter()
                            .map(|argument| squish_c_bound(kb, cb, kfv, cfv, argument, errors))
                            .collect(),
                    )
                })
                .collect(),
        ),
        other => other,
    };
    Located::new(node, span)
}

/// Remap free exp/con/kind variables in `e` to use positions in captured sets.
/// `nr` = number of recursive definitions (already bound, not free).
fn squish_e(
    nr: usize,
    kfv: &[usize],
    cfv: &[usize],
    efv: &[usize],
    e: LocatedExpression,
    errors: &mut ErrorReporter,
) -> LocatedExpression {
    squish_e_bound(0, 0, nr, nr, kfv, cfv, efv, e, errors)
}

fn squish_e_bound(
    kb: usize,
    cb: usize,
    eb: usize,
    nr: usize,
    kfv: &[usize],
    cfv: &[usize],
    efv: &[usize],
    e: LocatedExpression,
    errors: &mut ErrorReporter,
) -> LocatedExpression {
    let span = e.span.clone();
    let node = match e.node {
        Expression::Rel(n) if n >= eb => {
            // Remap to position in efv, then adjust by (eb - nr)
            // Formula from SML: ERel(positionOf (n-eb) efv + eb - nr)
            // Here eb already includes nr (we pass eb=nr initially).
            // Actually let's follow SML: initial call is with eb=nr (the recursive definitions
            // themselves occupy 0..nr-1 and are NOT free). Inside the hoisted function,
            // after applying subs', the remaining free vars need to be renumbered.
            // The squish remaps n-eb → position_of(n-eb, efv), then adds eb-nr back
            // (to account for remaining in-scope bindings above the recursion).
            Expression::Rel(position_of(n - eb, efv, "exp", &span, errors) + eb - nr)
        }
        Expression::Unif(reference) => {
            let known_expression = {
                let guard = crate::compiler_diagnostics::lock_for_compile(
                    reference.as_ref(),
                    "unnest expression unification cell",
                );
                guard.clone()
            };
            match known_expression {
                Some(known_expression_value) => {
                    return squish_e_bound(
                        kb,
                        cb,
                        eb,
                        nr,
                        kfv,
                        cfv,
                        efv,
                        known_expression_value,
                        errors,
                    );
                }
                None => Expression::Unif(reference),
            }
        }
        Expression::App(f, x) => Expression::App(
            Box::new(squish_e_bound(kb, cb, eb, nr, kfv, cfv, efv, *f, errors)),
            Box::new(squish_e_bound(kb, cb, eb, nr, kfv, cfv, efv, *x, errors)),
        ),
        Expression::Abs(name, dom, ran, body) => Expression::Abs(
            name,
            squish_c_bound(kb, cb, kfv, cfv, dom, errors),
            squish_c_bound(kb, cb, kfv, cfv, ran, errors),
            Box::new(squish_e_bound(
                kb,
                cb,
                eb + 1,
                nr,
                kfv,
                cfv,
                efv,
                *body,
                errors,
            )),
        ),
        Expression::CApp(f, c) => Expression::CApp(
            Box::new(squish_e_bound(kb, cb, eb, nr, kfv, cfv, efv, *f, errors)),
            squish_c_bound(kb, cb, kfv, cfv, c, errors),
        ),
        Expression::CAbs(expl, name, k, body) => Expression::CAbs(
            expl,
            name,
            Box::new(squish_k_bound(kb, kfv, *k, errors)),
            Box::new(squish_e_bound(
                kb,
                cb + 1,
                eb,
                nr,
                kfv,
                cfv,
                efv,
                *body,
                errors,
            )),
        ),
        Expression::KAbs(name, body) => Expression::KAbs(
            name,
            Box::new(squish_e_bound(
                kb + 1,
                cb,
                eb,
                nr,
                kfv,
                cfv,
                efv,
                *body,
                errors,
            )),
        ),
        Expression::KApp(f, k) => Expression::KApp(
            Box::new(squish_e_bound(kb, cb, eb, nr, kfv, cfv, efv, *f, errors)),
            Box::new(squish_k_bound(kb, kfv, *k, errors)),
        ),
        Expression::Record(fields) => Expression::Record(
            fields
                .into_iter()
                .map(|(n, v, t)| {
                    (
                        squish_c_bound(kb, cb, kfv, cfv, n, errors),
                        squish_e_bound(kb, cb, eb, nr, kfv, cfv, efv, v, errors),
                        squish_c_bound(kb, cb, kfv, cfv, t, errors),
                    )
                })
                .collect(),
        ),
        Expression::Field(e2, c, meta) => Expression::Field(
            Box::new(squish_e_bound(kb, cb, eb, nr, kfv, cfv, efv, *e2, errors)),
            squish_c_bound(kb, cb, kfv, cfv, c, errors),
            crate::elaborated::FieldMeta {
                field: squish_c_bound(kb, cb, kfv, cfv, meta.field, errors),
                rest: squish_c_bound(kb, cb, kfv, cfv, meta.rest, errors),
            },
        ),
        Expression::Concat(a, c1, b, c2) => Expression::Concat(
            Box::new(squish_e_bound(kb, cb, eb, nr, kfv, cfv, efv, *a, errors)),
            squish_c_bound(kb, cb, kfv, cfv, c1, errors),
            Box::new(squish_e_bound(kb, cb, eb, nr, kfv, cfv, efv, *b, errors)),
            squish_c_bound(kb, cb, kfv, cfv, c2, errors),
        ),
        Expression::Cut(e2, c, meta) => Expression::Cut(
            Box::new(squish_e_bound(kb, cb, eb, nr, kfv, cfv, efv, *e2, errors)),
            squish_c_bound(kb, cb, kfv, cfv, c, errors),
            crate::elaborated::FieldMeta {
                field: squish_c_bound(kb, cb, kfv, cfv, meta.field, errors),
                rest: squish_c_bound(kb, cb, kfv, cfv, meta.rest, errors),
            },
        ),
        Expression::CutMulti(e2, c, meta) => Expression::CutMulti(
            Box::new(squish_e_bound(kb, cb, eb, nr, kfv, cfv, efv, *e2, errors)),
            squish_c_bound(kb, cb, kfv, cfv, c, errors),
            crate::elaborated::RestMeta {
                rest: squish_c_bound(kb, cb, kfv, cfv, meta.rest, errors),
            },
        ),
        Expression::Case(disc, arms, meta) => Expression::Case(
            Box::new(squish_e_bound(kb, cb, eb, nr, kfv, cfv, efv, *disc, errors)),
            arms.into_iter()
                .map(|(p, arm)| {
                    let d = pat_bind_depth(&p);
                    (
                        p,
                        squish_e_bound(kb, cb, eb + d, nr, kfv, cfv, efv, arm, errors),
                    )
                })
                .collect(),
            crate::elaborated::CaseMeta {
                disc: squish_c_bound(kb, cb, kfv, cfv, meta.disc, errors),
                result: squish_c_bound(kb, cb, kfv, cfv, meta.result, errors),
            },
        ),
        Expression::Let(des, body, t) => {
            let mut cur_eb = eb;
            let des2: Vec<_> = des
                .into_iter()
                .map(|de| {
                    let span2 = de.span.clone();
                    let (node2, added) = match de.node {
                        ElaboratedDeclaration::Val(p, ty, e2) => {
                            let d = pat_bind_depth(&p);
                            let e2s = squish_e_bound(kb, cb, cur_eb, nr, kfv, cfv, efv, e2, errors);
                            (ElaboratedDeclaration::Val(p, ty, e2s), d)
                        }
                        ElaboratedDeclaration::ValRec(vis) => {
                            let nr2 = vis.len();
                            let vis2 = vis
                                .into_iter()
                                .map(|(x, ty, e2)| {
                                    (
                                        x,
                                        ty,
                                        squish_e_bound(
                                            kb,
                                            cb,
                                            cur_eb + nr2,
                                            nr,
                                            kfv,
                                            cfv,
                                            efv,
                                            e2,
                                            errors,
                                        ),
                                    )
                                })
                                .collect();
                            (ElaboratedDeclaration::ValRec(vis2), nr2)
                        }
                    };
                    cur_eb += added;
                    Located::new(node2, span2)
                })
                .collect();
            Expression::Let(
                des2,
                Box::new(squish_e_bound(
                    kb, cb, cur_eb, nr, kfv, cfv, efv, *body, errors,
                )),
                squish_c_bound(kb, cb, kfv, cfv, t, errors),
            )
        }
        other => other,
    };
    Located::new(node, span)
}

// ---------------------------------------------------------------------------
// Helper: does the type contain a function (TFun) or transaction at top level?
// ---------------------------------------------------------------------------

fn function_inside(c: &LocatedConstructor, basis_id: Option<usize>) -> bool {
    match &c.node {
        Constructor::TFun(_, _) => true,
        Constructor::App(f, _) => {
            // CApp((CModProj (basis', [], "transaction"), _), _) => basis' = !basis
            if let Constructor::ModProj(id, path, name) = &f.node {
                if path.is_empty() && name == "transaction" {
                    if let Some(bid) = basis_id {
                        return *id == bid;
                    }
                }
            }
            false
        }
        _ => false,
    }
}

/// Build the application `e applied to kfv args then cfv args then efv args`,
/// where kfv are KRel indices, cfv are CRel indices, efv are ERel indices
/// (all in the ORIGINAL scope, before any substitutions).
///
/// `nr` is the number of recursive definitions in scope at the call site
/// (used to compute the correct shifted ERel index).
fn build_call(
    base: LocatedExpression,
    kfv: &[usize],
    cfv: &[usize],
    efv: &[usize],
    nr: usize,
    loc: &crate::error_types::Span,
) -> LocatedExpression {
    let mut e = base;
    // Apply kind args (outermost first → fold left)
    for &kx in kfv {
        e = Located::new(
            Expression::KApp(
                Box::new(e),
                Box::new(Located::new(Kind::Rel(kx), loc.clone())),
            ),
            loc.clone(),
        );
    }
    // Apply con args
    for &cx in cfv {
        e = Located::new(
            Expression::CApp(Box::new(e), Located::new(Constructor::Rel(cx), loc.clone())),
            loc.clone(),
        );
    }
    // Apply exp args: ERel(nr + x) — shifted past the recursive bindings
    for &ex in efv {
        e = Located::new(
            Expression::App(
                Box::new(e),
                Box::new(Located::new(Expression::Rel(nr + ex), loc.clone())),
            ),
            loc.clone(),
        );
    }
    e
}

// ---------------------------------------------------------------------------
// Proper implementation using a self-contained traversal struct
// ---------------------------------------------------------------------------

struct UnnestCtx<'a> {
    /// Kind variable names (innermost first).
    knames: Vec<String>,
    /// Con variables (name, kind) (innermost first).
    cons: Vec<(String, LocatedKind)>,
    /// Exp variables (name, type) (innermost first).
    exps: Vec<(String, LocatedConstructor)>,
    /// ID of Basis structure.
    basis_id: Option<usize>,
    /// Fresh name counter.
    max_name: usize,
    /// Accumulated hoisted declarations.
    hoisted: Vec<(String, usize, LocatedConstructor, LocatedExpression)>,
    errors: &'a mut ErrorReporter,
}

// Type alias for brevity inside this module.
type Exp = Expression;

impl<'a> UnnestCtx<'a> {
    fn new(max_name: usize, errors: &'a mut ErrorReporter) -> Self {
        UnnestCtx {
            knames: vec![],
            cons: vec![],
            exps: vec![],
            basis_id: None,
            max_name,
            hoisted: vec![],
            errors,
        }
    }

    fn fresh(&mut self) -> usize {
        let n = self.max_name;
        self.max_name += 1;
        n
    }

    fn push_k(&mut self, name: String) {
        self.knames.insert(0, name);
    }
    fn pop_k(&mut self) {
        if !self.knames.is_empty() {
            self.knames.remove(0);
        }
    }

    fn push_c(&mut self, name: String, kind: LocatedKind) {
        self.cons.insert(0, (name, kind));
        let exps: Vec<_> = self
            .exps
            .drain(..)
            .map(|(n, t)| (n, lift_c(1, 0, t)))
            .collect();
        self.exps = exps;
    }
    fn pop_c(&mut self) {
        if !self.cons.is_empty() {
            self.cons.remove(0);
        }
        let exps: Vec<_> = self
            .exps
            .drain(..)
            .map(|(n, t)| (n, lift_c(-1, 0, t)))
            .collect();
        self.exps = exps;
    }

    fn push_e(&mut self, name: String, typ: LocatedConstructor) {
        self.exps.insert(0, (name, typ));
    }
    fn pop_e(&mut self) {
        if !self.exps.is_empty() {
            self.exps.remove(0);
        }
    }
    fn push_valrec_bindings(
        &mut self,
        vis: &[(String, LocatedConstructor, LocatedExpression)],
    ) -> usize {
        for (name, typ, _) in vis {
            self.push_e(name.clone(), typ.clone());
        }
        vis.len()
    }
    fn push_pattern_bindings(&mut self, pattern: &LocatedPattern) -> usize {
        let bindings = pattern_bindings_env_order(pattern);
        let added = bindings.len();
        for (name, type_con) in bindings.into_iter().rev() {
            self.push_e(name, type_con);
        }
        added
    }
    fn pop_e_n(&mut self, n: usize) {
        for _ in 0..n {
            if !self.exps.is_empty() {
                self.exps.remove(0);
            }
        }
    }

    fn exp(&mut self, e: LocatedExpression) -> LocatedExpression {
        let span = e.span.clone();
        match e.node {
            Exp::Let(eds, body, t) => {
                let basis_id = self.basis_id;
                let let_scope_start = self.exps.len();

                // Convert EDVal(PVar, fn-type, e) → EDValRec.
                let eds: Vec<_> = eds
                    .into_iter()
                    .map(|de| {
                        let span2 = de.span.clone();
                        match de.node {
                            ElaboratedDeclaration::Val(p, ty, e2) => {
                                if let Pattern::Var(x, _) = &p.node {
                                    if function_inside(&ty, basis_id) {
                                        let e2_l = lift_e(1, 0, e2);
                                        return Located::new(
                                            ElaboratedDeclaration::ValRec(vec![(
                                                x.clone(),
                                                ty,
                                                e2_l,
                                            )]),
                                            span2,
                                        );
                                    }
                                }
                                Located::new(ElaboratedDeclaration::Val(p, ty, e2), span2)
                            }
                            other => Located::new(other, span2),
                        }
                    })
                    .collect();

                // Process each decl.
                let mut remaining: Vec<LocatedElaboratedDeclaration> = Vec::new();
                let mut subs: Vec<(usize, LocatedExpression)> = Vec::new();
                let mut by: usize = 0; // total bindings hoisted (removed from Let)
                let mut let_bound_count: usize = 0;

                for de in eds {
                    let de_span = de.span.clone();
                    match de.node {
                        ElaboratedDeclaration::Val(p, ty, e2) => {
                            // Match the SML bottom-up fold: recurse into the declaration body
                            // under the current scope first, then apply the outer let rewrites.
                            let e2p = self.exp(e2);
                            let e2u = self.do_subst(e2p, &subs, by);
                            let added = self.push_pattern_bindings(&p);
                            remaining.push(Located::new(
                                ElaboratedDeclaration::Val(p, ty.clone(), e2u),
                                de_span.clone(),
                            ));
                            // Track the actual bound variable types so later hoisted
                            // valrecs see the same environment as elaboration.
                            let_bound_count += added;
                            // Match SML `bindMany`: every still-live let-bound variable needs an
                            // identity substitution entry so later declarations/body preserve the
                            // original De Bruijn numbering while hoisted valrecs are removed.
                            for _ in 0..added {
                                let shifted_existing: Vec<_> = subs
                                    .into_iter()
                                    .map(|(xn, rep)| (xn + 1, lift_e(1, 0, rep)))
                                    .collect();
                                let mut rebound_subs =
                                    Vec::with_capacity(shifted_existing.len() + 1);
                                rebound_subs.push((0, Located::new(Exp::Rel(0), de_span.clone())));
                                rebound_subs.extend(shifted_existing);
                                subs = rebound_subs;
                            }
                        }
                        ElaboratedDeclaration::ValRec(vis) => {
                            let nr = vis.len();
                            let pushed = self.push_valrec_bindings(&vis);
                            let vis: Vec<_> = vis
                                .into_iter()
                                .map(|(x, ty, e2)| (x, ty, self.exp(e2)))
                                .collect();
                            self.pop_e_n(pushed);
                            // Apply pending subs to each vi, then hoist.
                            let vis: Vec<_> = vis
                                .into_iter()
                                .map(|(x, ty, e2)| {
                                    let subslocal: Vec<_> = subs
                                        .iter()
                                        .filter(|(_, rep)| !matches!(rep.node, Exp::Rel(_)))
                                        .map(|(xn, rep)| {
                                            (*xn + nr, lift_e(nr as i64, 0, rep.clone()))
                                        })
                                        .collect();
                                    let e2a = apply_subs(&subslocal, e2);
                                    (x, ty, e2a)
                                })
                                .collect();

                            // Compute free vars and hoist.
                            let (new_subs, _nr2, hoisted_exp_bindings) =
                                self.hoist_valrec_inner(vis, &de_span);
                            for (name, typ) in hoisted_exp_bindings {
                                self.push_e(name, typ);
                                let_bound_count += 1;
                            }

                            // The new subs replace ERel(0..nr-1) with Named apps.
                            // Merge with existing subs (shift existing by nr, then add new).
                            let shifted_subs: Vec<_> = subs
                                .into_iter()
                                .map(|(xn, rep)| {
                                    let rep = if matches!(rep.node, Exp::Rel(_)) {
                                        rep
                                    } else {
                                        lift_e(nr as i64, 0, rep)
                                    };
                                    (xn + nr, rep)
                                })
                                .collect();
                            subs = new_subs.into_iter().chain(shifted_subs).collect();
                            by += nr;
                            // No push to remaining (hoisted).
                        }
                    }
                }

                // Apply remaining subs to body.
                let body2 = self.exp(*body);
                let body3 = self.do_subst(body2, &subs, by);
                self.pop_e_n(let_bound_count);
                debug_assert_eq!(self.exps.len(), let_scope_start);

                Located::new(Exp::Let(remaining, Box::new(body3), t), span)
            }
            // Recurse through all other expression forms.
            Exp::App(f, x) => Located::new(
                Exp::App(Box::new(self.exp(*f)), Box::new(self.exp(*x))),
                span,
            ),
            Exp::Abs(name, dom, ran, body) => {
                self.push_e(name.clone(), dom.clone());
                let body2 = self.exp(*body);
                self.pop_e();
                Located::new(Exp::Abs(name, dom, ran, Box::new(body2)), span)
            }
            Exp::CApp(f, c) => Located::new(Exp::CApp(Box::new(self.exp(*f)), c), span),
            Exp::CAbs(expl, name, k, body) => {
                self.push_c(name.clone(), *k.clone());
                let body2 = self.exp(*body);
                self.pop_c();
                Located::new(Exp::CAbs(expl, name, k, Box::new(body2)), span)
            }
            Exp::KAbs(name, body) => {
                self.push_k(name.clone());
                let body2 = self.exp(*body);
                self.pop_k();
                Located::new(Exp::KAbs(name, Box::new(body2)), span)
            }
            Exp::KApp(f, k) => Located::new(Exp::KApp(Box::new(self.exp(*f)), k), span),
            Exp::Record(fields) => Located::new(
                Exp::Record(
                    fields
                        .into_iter()
                        .map(|(n, v, t)| (n, self.exp(v), t))
                        .collect(),
                ),
                span,
            ),
            Exp::Field(e2, c, meta) => {
                Located::new(Exp::Field(Box::new(self.exp(*e2)), c, meta), span)
            }
            Exp::Concat(a, c1, b, c2) => Located::new(
                Exp::Concat(Box::new(self.exp(*a)), c1, Box::new(self.exp(*b)), c2),
                span,
            ),
            Exp::Cut(e2, c, meta) => Located::new(Exp::Cut(Box::new(self.exp(*e2)), c, meta), span),
            Exp::CutMulti(e2, c, meta) => {
                Located::new(Exp::CutMulti(Box::new(self.exp(*e2)), c, meta), span)
            }
            Exp::Case(disc, arms, meta) => {
                let disc2 = self.exp(*disc);
                let arms2 = arms
                    .into_iter()
                    .map(|(p, arm)| {
                        let d = self.push_pattern_bindings(&p);
                        let arm2 = self.exp(arm);
                        self.pop_e_n(d);
                        (p, arm2)
                    })
                    .collect();
                Located::new(Exp::Case(Box::new(disc2), arms2, meta), span)
            }
            other => Located::new(other, span),
        }
    }

    /// Apply substitutions then un-shift by `by`.
    fn do_subst(
        &self,
        e: LocatedExpression,
        subs: &[(usize, LocatedExpression)],
        by: usize,
    ) -> LocatedExpression {
        let e = apply_subs(subs, e);
        lift_e(-(by as i64), subs.len(), e)
    }

    /// Hoist a ValRec group. Returns substitutions (ERel → Named-call) and nr.
    fn hoist_valrec_inner(
        &mut self,
        vis: Vec<(String, LocatedConstructor, LocatedExpression)>,
        loc: &crate::error_types::Span,
    ) -> (
        Vec<(usize, LocatedExpression)>,
        usize,
        Vec<(String, LocatedConstructor)>,
    ) {
        let nr = vis.len();

        // Compute union of free vars.
        let mut kfv_set: BTreeSet<usize> = BTreeSet::new();
        let mut cfv_set: BTreeSet<usize> = BTreeSet::new();
        let mut efv_set: BTreeSet<usize> = BTreeSet::new();

        for (_, ty, body) in &vis {
            let (kv, cv) = fvs_con(0, 0, ty);
            kfv_set.extend(kv);
            cfv_set.extend(cv);
            let (kv2, cv2, ev2) = fvs_exp(0, 0, 0, nr, body);
            kfv_set.extend(kv2);
            cfv_set.extend(cv2);
            efv_set.extend(ev2);
        }

        // Transitively add kind fvs of con vars and of exp var types.
        let mut extra_k: BTreeSet<usize> = BTreeSet::new();
        for &cx in &cfv_set {
            if let Some((_, k)) = self.cons.get(cx) {
                extra_k.extend(fvs_kind(0, k));
            }
        }
        for &ex in &efv_set {
            if let Some((_, t)) = self.exps.get(ex) {
                let (kv, cv) = fvs_con(0, 0, t);
                extra_k.extend(kv);
                cfv_set.extend(cv);
            }
        }
        kfv_set.extend(extra_k);

        let kfv: Vec<usize> = kfv_set.into_iter().collect();
        let cfv: Vec<usize> = cfv_set.into_iter().collect();
        let efv: Vec<usize> = efv_set.into_iter().collect();

        if std::env::var("URWEB_DEBUG_UNNEST_REMAP").ok().as_deref() == Some("1") {
            let capture_names = |indices: &[usize]| -> Vec<String> {
                indices
                    .iter()
                    .map(|&index| {
                        self.exps
                            .get(index)
                            .map(|(name, _)| format!("{index}:{name}"))
                            .unwrap_or_else(|| format!("{index}:<missing-exp>"))
                    })
                    .collect()
            };
            for (name, _, _) in &vis {
                eprintln!(
                    "unnest hoist debug name={} at={}:{} nr={} kfv={:?} cfv={:?} efv={:?} efv_names={:?} exps={:?}",
                    name,
                    loc.file,
                    loc.first.line,
                    nr,
                    kfv,
                    cfv,
                    efv,
                    capture_names(&efv),
                    self.exps
                        .iter()
                        .take(8)
                        .enumerate()
                        .map(|(index, (exp_name, _))| format!("{index}:{exp_name}"))
                        .collect::<Vec<_>>(),
                );
            }
        }

        // Assign fresh IDs.
        let ids: Vec<usize> = vis.iter().map(|_| self.fresh()).collect();

        // Build substitutions (subs'): map ERel(nr-i-1) → Named(id) applied to kfv/cfv/efv.
        let subs: Vec<(usize, LocatedExpression)> = ids
            .iter()
            .enumerate()
            .map(|(i, &id)| {
                let base = Located::new(Exp::Named(id), loc.clone());
                let call = build_call(base, &kfv, &cfv, &efv, nr, loc);
                (nr - i - 1, call)
            })
            .collect();

        // Build hoisted declarations.
        let mut hoisted_exp_bindings = Vec::with_capacity(ids.len());
        for (i, (x, ty, body)) in vis.into_iter().enumerate() {
            let id = ids[i];

            // Apply subs' to body.
            let body = apply_subs(&subs, body);

            // Squish.
            let ty_s = squish_c(&kfv, &cfv, ty, self.errors);
            let body_s = squish_e(nr, &kfv, &cfv, &efv, body, self.errors);

            // Wrap with exp lambdas (innermost efv first, i.e. reverse).
            let (mut we, mut wt) = (body_s, ty_s);
            for &ex in efv.iter().rev() {
                let (aname, atype) = self
                    .exps
                    .get(ex)
                    .map(|(n, t)| (n.clone(), squish_c(&kfv, &cfv, t.clone(), self.errors)))
                    .unwrap_or_else(|| {
                        if std::env::var("URWEB_DEBUG_UNNEST_REMAP").ok().as_deref() == Some("1") {
                            eprintln!(
                                "unnest missing exp capture name={} at={}:{} ex={} env_len={} efv={:?} exps={:?}",
                                x,
                                loc.file,
                                loc.first.line,
                                ex,
                                self.exps.len(),
                                efv,
                                self.exps
                                    .iter()
                                    .take(12)
                                    .enumerate()
                                    .map(|(index, (exp_name, _))| format!("{index}:{exp_name}"))
                                    .collect::<Vec<_>>(),
                            );
                        }
                        ("_".into(), Located::dummy(Constructor::Error))
                    });
                let fun_t = Located::new(
                    Constructor::TFun(Box::new(atype.clone()), Box::new(wt.clone())),
                    loc.clone(),
                );
                we = Located::new(
                    Exp::Abs(aname, atype, fun_t.clone(), Box::new(we)),
                    loc.clone(),
                );
                wt = fun_t;
            }
            // Wrap with con lambdas.
            for &cx in cfv.iter().rev() {
                let (cname, ckind) = self
                    .cons
                    .get(cx)
                    .map(|(n, k)| (n.clone(), k.clone()))
                    .unwrap_or_else(|| ("_".into(), Located::dummy(Kind::Star)));
                we = Located::new(
                    Exp::CAbs(
                        Explicitness::Explicit,
                        cname,
                        Box::new(ckind.clone()),
                        Box::new(we),
                    ),
                    loc.clone(),
                );
                wt = Located::new(
                    Constructor::TCFun(
                        Explicitness::Explicit,
                        "_".into(),
                        Box::new(ckind),
                        Box::new(wt),
                    ),
                    loc.clone(),
                );
            }
            // Wrap with kind lambdas.
            for &kx in kfv.iter().rev() {
                let kname = self.knames.get(kx).cloned().unwrap_or_else(|| "_".into());
                we = Located::new(Exp::KAbs(kname.clone(), Box::new(we)), loc.clone());
                wt = Located::new(Constructor::TKFun(kname, Box::new(wt)), loc.clone());
            }

            hoisted_exp_bindings.push((x.clone(), wt.clone()));
            self.hoisted.push(("$".to_string() + &x, id, wt, we));
        }

        (subs, nr, hoisted_exp_bindings)
    }

    fn decl(&mut self, d: LocatedDeclaration) -> Vec<LocatedDeclaration> {
        let span = d.span.clone();
        match d.node {
            Declaration::Val(x, n, t, e) => {
                let saved = self.hoisted.len();
                let e2 = self.exp(e);
                let new_decls = self.drain_hoisted(saved, &span);
                let mut result = new_decls;
                result.push(Located::new(Declaration::Val(x, n, t, e2), span));
                result
            }
            Declaration::ValRec(vis) => {
                let saved = self.hoisted.len();
                let pushed = self.push_valrec_bindings(
                    &vis.iter()
                        .map(|(x, _n, t, e)| (x.clone(), t.clone(), e.clone()))
                        .collect::<Vec<_>>(),
                );
                let vis2: Vec<_> = vis
                    .into_iter()
                    .map(|(x, n, t, e)| {
                        let e2 = self.exp(e);
                        (x, n, t, e2)
                    })
                    .collect();
                self.pop_e_n(pushed);
                let new_decls = self.drain_hoisted(saved, &span);
                let mut result = new_decls;
                // Merge hoisted into this ValRec.
                let mut all_vis: Vec<(String, usize, LocatedConstructor, LocatedExpression)> =
                    Vec::new();
                for ld in result.iter() {
                    if let Declaration::ValRec(v) = &ld.node {
                        all_vis.extend(v.iter().cloned());
                    }
                }
                // Actually just prepend hoisted decls and then add ValRec.
                // (SML merges into DValRec; we just prepend them.)
                result.push(Located::new(Declaration::ValRec(vis2), span));
                result
            }
            Declaration::Task(e1, e2) => {
                let saved = self.hoisted.len();
                let e1u = self.exp(e1);
                let e2u = self.exp(e2);
                let new_decls = self.drain_hoisted(saved, &span);
                let mut result = new_decls;
                result.push(Located::new(Declaration::Task(e1u, e2u), span));
                result
            }
            Declaration::Policy(e) => {
                let saved = self.hoisted.len();
                let eu = self.exp(e);
                let new_decls = self.drain_hoisted(saved, &span);
                let mut result = new_decls;
                result.push(Located::new(Declaration::Policy(eu), span));
                result
            }
            Declaration::Structure(x, n, sgn, str_) => {
                let saved = self.hoisted.len();
                let str2 = self.str_(str_);
                let new_decls = self.drain_hoisted(saved, &span);
                let mut result = new_decls;
                result.push(Located::new(Declaration::Structure(x, n, sgn, str2), span));
                result
            }
            Declaration::FfiStr(ref x, n, _) if x == "Basis" => {
                self.basis_id = Some(n);
                vec![d]
            }
            other => vec![Located::new(other, span)],
        }
    }

    fn str_(
        &mut self,
        s: crate::elaborated::LocatedStructure,
    ) -> crate::elaborated::LocatedStructure {
        use crate::elaborated::Structure;
        let span = s.span.clone();
        match s.node {
            Structure::Const(ds) => {
                let ds2 = ds.into_iter().flat_map(|d| self.decl(d)).collect();
                Located::new(Structure::Const(ds2), span)
            }
            Structure::Fun(x, n, dom, ran, body) => {
                let body2 = self.str_(*body);
                Located::new(Structure::Fun(x, n, dom, ran, Box::new(body2)), span)
            }
            other => Located::new(other, span),
        }
    }

    fn drain_hoisted(
        &mut self,
        saved: usize,
        span: &crate::error_types::Span,
    ) -> Vec<LocatedDeclaration> {
        let new_ones: Vec<_> = self.hoisted.drain(saved..).collect();
        new_ones
            .into_iter()
            .map(|(x, n, t, e)| Located::new(Declaration::ValRec(vec![(x, n, t, e)]), span.clone()))
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Remove nested function definitions by lambda-lifting (hoist nested `fun` as top-level `val rec`).
///
/// Ported from `unnest.sml`. Must run **after** [`crate::elaborated::elaborate::elab_file`] and **before**
/// [`crate::elaborated::explify::explify`].
///
/// # Arguments
///
/// * `file` — Elaborated module body.
/// * `errors` — Reporter for failures during unnesting (e.g. bad shapes).
///
/// # Returns
///
/// Transformed [`File`] (possibly with extra top-level bindings); errors are recorded in `errors`, not
/// as `Result`.
pub fn unnest(file: File, errors: &mut ErrorReporter) -> File {
    let max_name = {
        // Find the maximum named ID in the file to start fresh IDs above it.
        use crate::elaborated::utilities;
        utilities::file::max_name(&file) + 1
    };

    let mut ctx = UnnestCtx::new(max_name, errors);
    file.into_iter().flat_map(|d| ctx.decl(d)).collect()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elaborated::*;
    use crate::error_types::{ErrorReporter, Located};

    fn dummy_type() -> LocatedConstructor {
        Located::dummy(Constructor::Error)
    }

    fn named_type(id: usize) -> LocatedConstructor {
        Located::dummy(Constructor::Named(id))
    }

    fn dummy_exp() -> LocatedExpression {
        Located::dummy(Expression::Prim(crate::primitives::Prim::Int(0)))
    }

    fn constructor_has_error(constructor: &LocatedConstructor) -> bool {
        match &constructor.node {
            Constructor::Error => true,
            Constructor::TFun(domain, range)
            | Constructor::App(domain, range)
            | Constructor::Concat(domain, range) => {
                constructor_has_error(domain) || constructor_has_error(range)
            }
            Constructor::TCFun(_, _, _, body)
            | Constructor::TRecord(body)
            | Constructor::Abs(_, _, body)
            | Constructor::KAbs(_, body)
            | Constructor::TKFun(_, body) => constructor_has_error(body),
            Constructor::TDisjoint(left, right, body) => {
                constructor_has_error(left)
                    || constructor_has_error(right)
                    || constructor_has_error(body)
            }
            Constructor::KApp(constructor, kind) => {
                constructor_has_error(constructor) || kind_has_error(kind)
            }
            Constructor::Record(kind, fields) => {
                kind_has_error(kind)
                    || fields.iter().any(|(name, field_type)| {
                        constructor_has_error(name) || constructor_has_error(field_type)
                    })
            }
            Constructor::Map(domain, range) => kind_has_error(domain) || kind_has_error(range),
            Constructor::Tuple(items) => items.iter().any(constructor_has_error),
            Constructor::Proj(constructor, _) => constructor_has_error(constructor),
            Constructor::Unif(_, _, _, _, reference) => {
                let guard = crate::compiler_diagnostics::lock_for_compile(
                    reference.as_ref(),
                    "unnest test constructor_has_error",
                );
                match &*guard {
                    CUnif::Known(known) => constructor_has_error(known),
                    CUnif::Unknown(_) => false,
                }
            }
            Constructor::Rel(_)
            | Constructor::Named(_)
            | Constructor::ModProj(_, _, _)
            | Constructor::Name(_)
            | Constructor::Unit
            | Constructor::Enum(_) => false,
        }
    }

    fn kind_has_error(kind: &LocatedKind) -> bool {
        match &kind.node {
            Kind::Typed(Types::Error(_)) => true,
            Kind::Arrow(domain, range) => kind_has_error(domain) || kind_has_error(range),
            Kind::Record(inner) | Kind::KFun(inner) => kind_has_error(inner),
            Kind::Tuple(items) => items.iter().any(kind_has_error),
            Kind::Unif(_, _, reference) | Kind::TupleUnif(_, _, reference) => {
                let guard = crate::compiler_diagnostics::lock_for_compile(
                    reference.as_ref(),
                    "unnest test kind_has_error",
                );
                match &*guard {
                    KUnif::Known(known) => kind_has_error(known),
                    KUnif::Unknown => false,
                }
            }
            Kind::Star | Kind::Typed(_) | Kind::Name | Kind::Unit | Kind::Rel(_) => false,
        }
    }

    fn expression_has_error(expression: &LocatedExpression) -> bool {
        match &expression.node {
            Expression::Rel(_)
            | Expression::Named(_)
            | Expression::ModProj(_, _, _)
            | Expression::Prim(_) => false,
            Expression::App(function, argument) => {
                expression_has_error(function) || expression_has_error(argument)
            }
            Expression::Abs(_, domain, range, body) => {
                constructor_has_error(domain)
                    || constructor_has_error(range)
                    || expression_has_error(body)
            }
            Expression::CApp(expression, constructor) => {
                expression_has_error(expression) || constructor_has_error(constructor)
            }
            Expression::CAbs(_, _, kind, body) => {
                kind_has_error(kind) || expression_has_error(body)
            }
            Expression::KAbs(_, body) => expression_has_error(body),
            Expression::KApp(expression, kind) => {
                expression_has_error(expression) || kind_has_error(kind)
            }
            Expression::Record(fields) => fields.iter().any(|(name, value, field_type)| {
                constructor_has_error(name)
                    || expression_has_error(value)
                    || constructor_has_error(field_type)
            }),
            Expression::Field(expression, constructor, meta)
            | Expression::Cut(expression, constructor, meta) => {
                expression_has_error(expression)
                    || constructor_has_error(constructor)
                    || constructor_has_error(&meta.field)
                    || constructor_has_error(&meta.rest)
            }
            Expression::Concat(left, left_type, right, right_type) => {
                expression_has_error(left)
                    || constructor_has_error(left_type)
                    || expression_has_error(right)
                    || constructor_has_error(right_type)
            }
            Expression::CutMulti(expression, constructor, meta) => {
                expression_has_error(expression)
                    || constructor_has_error(constructor)
                    || constructor_has_error(&meta.rest)
            }
            Expression::Case(discriminant, arms, meta) => {
                expression_has_error(discriminant)
                    || arms.iter().any(|(pattern, arm)| {
                        pattern_has_error(pattern) || expression_has_error(arm)
                    })
                    || constructor_has_error(&meta.disc)
                    || constructor_has_error(&meta.result)
            }
            Expression::Error => true,
            Expression::Unif(reference) => {
                let guard = crate::compiler_diagnostics::lock_for_compile(
                    reference.as_ref(),
                    "unnest test expression_has_error",
                );
                match &*guard {
                    Some(known) => expression_has_error(known),
                    None => false,
                }
            }
            Expression::Let(declarations, body, constructor) => {
                declarations.iter().any(elab_decl_has_error)
                    || expression_has_error(body)
                    || constructor_has_error(constructor)
            }
            Expression::Hole(_) => false,
        }
    }

    fn pattern_has_error(pattern: &LocatedPattern) -> bool {
        match &pattern.node {
            Pattern::Var(_, constructor) => constructor_has_error(constructor),
            Pattern::Prim(_) => false,
            Pattern::Constructor(_, _, constructors, inner) => {
                constructors.iter().any(constructor_has_error)
                    || inner
                        .as_ref()
                        .is_some_and(|pattern| pattern_has_error(pattern))
            }
            Pattern::Record(fields) => fields.iter().any(|(_, pattern, constructor)| {
                pattern_has_error(pattern) || constructor_has_error(constructor)
            }),
        }
    }

    fn elab_decl_has_error(declaration: &LocatedElaboratedDeclaration) -> bool {
        match &declaration.node {
            ElaboratedDeclaration::Val(pattern, constructor, expression) => {
                pattern_has_error(pattern)
                    || constructor_has_error(constructor)
                    || expression_has_error(expression)
            }
            ElaboratedDeclaration::ValRec(bindings) => {
                bindings.iter().any(|(_, constructor, expression)| {
                    constructor_has_error(constructor) || expression_has_error(expression)
                })
            }
        }
    }

    fn decl_has_error(declaration: &LocatedDeclaration) -> bool {
        match &declaration.node {
            Declaration::Constructor(_, _, kind, constructor) => {
                kind_has_error(kind) || constructor_has_error(constructor)
            }
            Declaration::Datatype(datatypes) => datatypes.iter().any(|datatype| {
                datatype.constrs.iter().any(|(_, _, constructor)| {
                    constructor.as_ref().is_some_and(constructor_has_error)
                })
            }),
            Declaration::DatatypeImp { constrs, .. } => constrs
                .iter()
                .any(|(_, _, constructor)| constructor.as_ref().is_some_and(constructor_has_error)),
            Declaration::Val(_, _, constructor, expression) => {
                constructor_has_error(constructor) || expression_has_error(expression)
            }
            Declaration::ValRec(bindings) => {
                bindings.iter().any(|(_, _, constructor, expression)| {
                    constructor_has_error(constructor) || expression_has_error(expression)
                })
            }
            Declaration::Signature(_, _, signature) => signature_has_error(signature),
            Declaration::Structure(_, _, signature, structure)
            | Declaration::Export(_, signature, structure) => {
                signature_has_error(signature) || structure_has_error(structure)
            }
            Declaration::FfiStr(_, _, signature) => signature_has_error(signature),
            Declaration::Constraint(left, right) => {
                constructor_has_error(left) || constructor_has_error(right)
            }
            Declaration::Table {
                con,
                exp,
                pk_con,
                pk_exp,
                unique_con,
                ..
            } => {
                constructor_has_error(con)
                    || expression_has_error(exp)
                    || constructor_has_error(pk_con)
                    || expression_has_error(pk_exp)
                    || constructor_has_error(unique_con)
            }
            Declaration::Sequence(_, _, _)
            | Declaration::Database(_)
            | Declaration::Style(_, _, _)
            | Declaration::OnError(_, _, _) => false,
            Declaration::View(_, _, _, expression, constructor) => {
                expression_has_error(expression) || constructor_has_error(constructor)
            }
            Declaration::Cookie(_, _, _, constructor) => constructor_has_error(constructor),
            Declaration::Index(left, right) | Declaration::Task(left, right) => {
                expression_has_error(left) || expression_has_error(right)
            }
            Declaration::Policy(expression) => expression_has_error(expression),
            Declaration::Ffi(_, _, _, constructor) => constructor_has_error(constructor),
        }
    }

    fn signature_has_error(signature: &LocatedSignature) -> bool {
        match &signature.node {
            Signature::Const(items) => items.iter().any(signature_item_has_error),
            Signature::Fun(_, _, domain, range) => {
                signature_has_error(domain) || signature_has_error(range)
            }
            Signature::Where(signature, _, _, constructor) => {
                signature_has_error(signature) || constructor_has_error(constructor)
            }
            Signature::Var(_) | Signature::Proj(_, _, _) | Signature::Error => false,
        }
    }

    fn signature_item_has_error(item: &LocatedSignatureItem) -> bool {
        match &item.node {
            SignatureItem::ConAbs(_, _, kind) | SignatureItem::ClassAbs(_, _, kind) => {
                kind_has_error(kind)
            }
            SignatureItem::Constructor(_, _, kind, constructor)
            | SignatureItem::Class(_, _, kind, constructor) => {
                kind_has_error(kind) || constructor_has_error(constructor)
            }
            SignatureItem::Datatype(datatypes) => datatypes.iter().any(|datatype| {
                datatype.constrs.iter().any(|(_, _, constructor)| {
                    constructor.as_ref().is_some_and(constructor_has_error)
                })
            }),
            SignatureItem::DatatypeImp { constrs, .. } => constrs
                .iter()
                .any(|(_, _, constructor)| constructor.as_ref().is_some_and(constructor_has_error)),
            SignatureItem::Val(_, _, constructor) => constructor_has_error(constructor),
            SignatureItem::Structure(_, _, _, signature)
            | SignatureItem::Signature(_, _, signature) => signature_has_error(signature),
            SignatureItem::Constraint(left, right) => {
                constructor_has_error(left) || constructor_has_error(right)
            }
        }
    }

    fn structure_has_error(structure: &LocatedStructure) -> bool {
        match &structure.node {
            Structure::Const(declarations) => declarations.iter().any(decl_has_error),
            Structure::Fun(_, _, domain, range, body) => {
                signature_has_error(domain)
                    || signature_has_error(range)
                    || structure_has_error(body)
            }
            Structure::App(function, argument) => {
                structure_has_error(function) || structure_has_error(argument)
            }
            Structure::Var(_) | Structure::Proj(_, _) | Structure::Error => false,
        }
    }

    #[test]
    fn unnest_empty_file() {
        let file: File = vec![];
        let mut errors = ErrorReporter::new();
        let result = unnest(file, &mut errors);
        assert!(result.is_empty());
        assert!(!errors.has_errors());
    }

    #[test]
    fn unnest_simple_val_passthrough() {
        // A simple `val x = 0` should pass through unchanged.
        let file: File = vec![Located::dummy(Declaration::Val(
            "x".into(),
            1,
            dummy_type(),
            dummy_exp(),
        ))];
        let mut errors = ErrorReporter::new();
        let result = unnest(file, &mut errors);
        assert_eq!(result.len(), 1);
        assert!(matches!(result[0].node, Declaration::Val(..)));
        assert!(!errors.has_errors());
    }

    #[test]
    fn unnest_let_without_valrec_passthrough() {
        // `val x = let val y = 0 in y end` should pass through without hoisting.
        let inner_let = Located::dummy(Expression::Let(
            vec![Located::dummy(ElaboratedDeclaration::Val(
                Located::dummy(Pattern::Var("y".into(), dummy_type())),
                dummy_type(),
                dummy_exp(),
            ))],
            Box::new(Located::dummy(Expression::Rel(0))),
            dummy_type(),
        ));
        let file: File = vec![Located::dummy(Declaration::Val(
            "x".into(),
            1,
            dummy_type(),
            inner_let,
        ))];
        let mut errors = ErrorReporter::new();
        let result = unnest(file, &mut errors);
        // Should not panic; inner let without ValRec stays as Let.
        assert_eq!(result.len(), 1);
        assert!(!errors.has_errors());
    }

    #[test]
    fn unnest_hoisted_valrec_preserves_captured_let_binding_type() {
        let captured_type = named_type(7);
        let result_type = named_type(8);
        let inner_let = Located::dummy(Expression::Let(
            vec![
                Located::dummy(ElaboratedDeclaration::Val(
                    Located::dummy(Pattern::Var("captured".into(), captured_type.clone())),
                    captured_type.clone(),
                    dummy_exp(),
                )),
                Located::dummy(ElaboratedDeclaration::ValRec(vec![(
                    "f".into(),
                    result_type.clone(),
                    Located::dummy(Expression::Rel(1)),
                )])),
            ],
            Box::new(Located::dummy(Expression::Rel(0))),
            result_type.clone(),
        ));
        let file: File = vec![Located::dummy(Declaration::Val(
            "top".into(),
            1,
            result_type.clone(),
            inner_let,
        ))];

        let mut errors = ErrorReporter::new();
        let result = unnest(file, &mut errors);

        let (name, _id, hoisted_type, hoisted_body) = result
            .iter()
            .find_map(|declaration| match &declaration.node {
                Declaration::ValRec(bindings) => bindings.first(),
                _ => None,
            })
            .expect("expected a hoisted valrec binding");

        assert_eq!(name, "$f");
        match &hoisted_type.node {
            Constructor::TFun(domain, range) => {
                assert!(
                    matches!(domain.node, Constructor::Named(7)),
                    "captured let-binding type must be preserved in hoisted valrec domain, got {:?}",
                    domain.node
                );
                assert!(
                    matches!(range.node, Constructor::Named(8)),
                    "original result type must remain intact after lambda lifting, got {:?}",
                    range.node
                );
            }
            other => panic!(
                "expected hoisted valrec type to be a function, got {:?}",
                other
            ),
        }
        match &hoisted_body.node {
            Expression::Abs(argument_name, argument_type, _, _) => {
                assert_eq!(argument_name, "captured");
                assert!(
                    matches!(argument_type.node, Constructor::Named(7)),
                    "captured argument type must not degrade to Constructor::Error, got {:?}",
                    argument_type.node
                );
            }
            other => panic!(
                "expected hoisted valrec body to be wrapped in an Abs, got {:?}",
                other
            ),
        }
        assert!(!errors.has_errors());
    }

    #[test]
    fn unnest_later_hoist_can_capture_earlier_hoisted_function() {
        let captured_type = named_type(7);
        let speak_type = named_type(8);
        let do_speak_type = named_type(9);
        let inner_let = Located::dummy(Expression::Let(
            vec![
                Located::dummy(ElaboratedDeclaration::Val(
                    Located::dummy(Pattern::Var("captured".into(), captured_type.clone())),
                    captured_type.clone(),
                    dummy_exp(),
                )),
                Located::dummy(ElaboratedDeclaration::ValRec(vec![(
                    "speak".into(),
                    speak_type.clone(),
                    Located::dummy(Expression::Rel(1)),
                )])),
                Located::dummy(ElaboratedDeclaration::ValRec(vec![(
                    "doSpeak".into(),
                    do_speak_type.clone(),
                    Located::dummy(Expression::Rel(1)),
                )])),
            ],
            Box::new(Located::dummy(Expression::Rel(0))),
            do_speak_type.clone(),
        ));
        let file: File = vec![Located::dummy(Declaration::Val(
            "top".into(),
            1,
            do_speak_type,
            inner_let,
        ))];

        let mut errors = ErrorReporter::new();
        let result = unnest(file, &mut errors);

        assert!(
            result.iter().all(|declaration| !decl_has_error(declaration)),
            "unnest should preserve hoisted function capture types without Constructor::Error placeholders: {result:#?}",
        );
        assert!(!errors.has_errors());
    }
}
