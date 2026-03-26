//! ESpecialize — specialize polymorphic Core *functions* by substituting
//! closed functional arguments at call sites.
//!
//! Unlike `specialize.rs` (which handles datatype monomorphization), this pass
//! handles *expression* specialization: when a named function `f` is called
//! with arguments whose types contain function types (or certain Basis Ffi
//! types), and those arguments are not all simple variable references, a
//! monomorphic copy `f'` is generated with those arguments substituted in.
//!
//! The pass runs in a fixed-point loop: reduce → specialize → (if changed:
//! untangle → shake → repeat).
//!
//! Mirrors `especialize.sml`.

#![allow(dead_code)]

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::core::dead_code_elimination::shake;
use crate::core::environment::pat_binds_n;
use crate::core::local_reduction::reduce;
use crate::core::untangling::untangle;
use crate::core::utilities::constructor as con_util;
use crate::core::utilities::file as file_util;
use crate::core::*;
use crate::error_types::{Located, Span};

// ---------------------------------------------------------------------------
// Lift / substitution helpers
// ---------------------------------------------------------------------------

/// Increment every `Expression::Rel(n)` where `n >= depth` by 1.
/// Used when wrapping a body in a new outer lambda.
fn lift_exp_in_exp(depth: usize, e: LocatedExpression) -> LocatedExpression {
    lift_exp_by(depth, 1, e)
}

fn lift_exp_by(depth: usize, by: usize, e: LocatedExpression) -> LocatedExpression {
    let span = e.span.clone();
    match e.node {
        Expression::Rel(n) => {
            if n >= depth {
                Located::new(Expression::Rel(n + by), span)
            } else {
                Located::new(Expression::Rel(n), span)
            }
        }
        Expression::Prim(_) | Expression::Named(_) | Expression::Ffi(_, _) => e,
        Expression::Constructor(dk, pc, cs, arg) => {
            let arg = arg.map(|a| Box::new(lift_exp_by(depth, by, *a)));
            Located::new(Expression::Constructor(dk, pc, cs, arg), span)
        }
        Expression::FfiApp(m, x, es) => {
            let es = es
                .into_iter()
                .map(|(e, t)| (lift_exp_by(depth, by, e), t))
                .collect();
            Located::new(Expression::FfiApp(m, x, es), span)
        }
        Expression::App(f, a) => Located::new(
            Expression::App(
                Box::new(lift_exp_by(depth, by, *f)),
                Box::new(lift_exp_by(depth, by, *a)),
            ),
            span,
        ),
        Expression::Abs(x, t, rt, body) => Located::new(
            Expression::Abs(x, t, rt, Box::new(lift_exp_by(depth + 1, by, *body))),
            span,
        ),
        Expression::CApp(f, c) => Located::new(
            Expression::CApp(Box::new(lift_exp_by(depth, by, *f)), c),
            span,
        ),
        Expression::CAbs(x, k, body) => Located::new(
            Expression::CAbs(x, k, Box::new(lift_exp_by(depth, by, *body))),
            span,
        ),
        Expression::KAbs(x, body) => Located::new(
            Expression::KAbs(x, Box::new(lift_exp_by(depth, by, *body))),
            span,
        ),
        Expression::KApp(f, k) => Located::new(
            Expression::KApp(Box::new(lift_exp_by(depth, by, *f)), k),
            span,
        ),
        Expression::Record(fields) => {
            let fields = fields
                .into_iter()
                .map(|(c1, e, c2)| (c1, lift_exp_by(depth, by, e), c2))
                .collect();
            Located::new(Expression::Record(fields), span)
        }
        Expression::Field(e, c, meta) => Located::new(
            Expression::Field(Box::new(lift_exp_by(depth, by, *e)), c, meta),
            span,
        ),
        Expression::Concat(e1, c1, e2, c2) => Located::new(
            Expression::Concat(
                Box::new(lift_exp_by(depth, by, *e1)),
                c1,
                Box::new(lift_exp_by(depth, by, *e2)),
                c2,
            ),
            span,
        ),
        Expression::Cut(e, c, meta) => Located::new(
            Expression::Cut(Box::new(lift_exp_by(depth, by, *e)), c, meta),
            span,
        ),
        Expression::CutMulti(e, c, meta) => Located::new(
            Expression::CutMulti(Box::new(lift_exp_by(depth, by, *e)), c, meta),
            span,
        ),
        Expression::Case(e, arms, rt) => {
            let e = Box::new(lift_exp_by(depth, by, *e));
            let arms = arms
                .into_iter()
                .map(|(p, body)| {
                    let n = pat_binds_n(&p);
                    (p, lift_exp_by(depth + n, by, body))
                })
                .collect();
            Located::new(Expression::Case(e, arms, rt), span)
        }
        Expression::Write(e) => Located::new(
            Expression::Write(Box::new(lift_exp_by(depth, by, *e))),
            span,
        ),
        Expression::Closure(n, es) => {
            let es = es.into_iter().map(|e| lift_exp_by(depth, by, e)).collect();
            Located::new(Expression::Closure(n, es), span)
        }
        Expression::Let(x, t, e1, e2) => Located::new(
            Expression::Let(
                x,
                t,
                Box::new(lift_exp_by(depth, by, *e1)),
                Box::new(lift_exp_by(depth + 1, by, *e2)),
            ),
            span,
        ),
        Expression::ServerCall(n, es, t, fm) => {
            let es = es.into_iter().map(|e| lift_exp_by(depth, by, e)).collect();
            Located::new(Expression::ServerCall(n, es, t, fm), span)
        }
    }
}

/// Substitute `rep` for `Expression::Rel(xn)` in `body`.
/// When descending under a binder, increment `xn` and lift `rep`.
/// Decrements `Rel(n)` for `n > xn` (removing the variable from scope).
fn sub_exp_in_exp(
    xn: usize,
    rep: &LocatedExpression,
    body: LocatedExpression,
) -> LocatedExpression {
    let span = body.span.clone();
    match body.node {
        Expression::Rel(n) => match n.cmp(&xn) {
            Ordering::Equal => rep.clone(),
            Ordering::Greater => Located::new(Expression::Rel(n - 1), span),
            Ordering::Less => Located::new(Expression::Rel(n), span),
        },
        Expression::Prim(_) | Expression::Named(_) | Expression::Ffi(_, _) => body,
        Expression::Constructor(dk, pc, cs, arg) => {
            let arg = arg.map(|a| Box::new(sub_exp_in_exp(xn, rep, *a)));
            Located::new(Expression::Constructor(dk, pc, cs, arg), span)
        }
        Expression::FfiApp(m, x, es) => {
            let es = es
                .into_iter()
                .map(|(e, t)| (sub_exp_in_exp(xn, rep, e), t))
                .collect();
            Located::new(Expression::FfiApp(m, x, es), span)
        }
        Expression::App(f, a) => Located::new(
            Expression::App(
                Box::new(sub_exp_in_exp(xn, rep, *f)),
                Box::new(sub_exp_in_exp(xn, rep, *a)),
            ),
            span,
        ),
        Expression::Abs(x, t, rt, b) => {
            // Under a binder: xn → xn+1, rep gets lifted by 1
            let rep2 = lift_exp_in_exp(0, rep.clone());
            Located::new(
                Expression::Abs(x, t, rt, Box::new(sub_exp_in_exp(xn + 1, &rep2, *b))),
                span,
            )
        }
        Expression::CApp(f, c) => Located::new(
            Expression::CApp(Box::new(sub_exp_in_exp(xn, rep, *f)), c),
            span,
        ),
        Expression::CAbs(x, k, b) => {
            // Constructor binder — no exp binder, but lift con refs in rep?
            // The SML does: bind = fn ((xn, rep), U.Exp.RelC _) => (xn, liftConInExp 0 rep)
            // For simplicity we don't lift cons in rep (they're Named, not Rel in this pass)
            Located::new(
                Expression::CAbs(x, k, Box::new(sub_exp_in_exp(xn, rep, *b))),
                span,
            )
        }
        Expression::KAbs(x, b) => Located::new(
            Expression::KAbs(x, Box::new(sub_exp_in_exp(xn, rep, *b))),
            span,
        ),
        Expression::KApp(f, k) => Located::new(
            Expression::KApp(Box::new(sub_exp_in_exp(xn, rep, *f)), k),
            span,
        ),
        Expression::Record(fields) => {
            let fields = fields
                .into_iter()
                .map(|(c1, e, c2)| (c1, sub_exp_in_exp(xn, rep, e), c2))
                .collect();
            Located::new(Expression::Record(fields), span)
        }
        Expression::Field(e, c, meta) => Located::new(
            Expression::Field(Box::new(sub_exp_in_exp(xn, rep, *e)), c, meta),
            span,
        ),
        Expression::Concat(e1, c1, e2, c2) => Located::new(
            Expression::Concat(
                Box::new(sub_exp_in_exp(xn, rep, *e1)),
                c1,
                Box::new(sub_exp_in_exp(xn, rep, *e2)),
                c2,
            ),
            span,
        ),
        Expression::Cut(e, c, meta) => Located::new(
            Expression::Cut(Box::new(sub_exp_in_exp(xn, rep, *e)), c, meta),
            span,
        ),
        Expression::CutMulti(e, c, meta) => Located::new(
            Expression::CutMulti(Box::new(sub_exp_in_exp(xn, rep, *e)), c, meta),
            span,
        ),
        Expression::Case(e, arms, rt) => {
            let e = Box::new(sub_exp_in_exp(xn, rep, *e));
            let arms = arms
                .into_iter()
                .map(|(p, body)| {
                    let n = pat_binds_n(&p);
                    let lifted = lift_exp_by(0, n, rep.clone());
                    (p, sub_exp_in_exp(xn + n, &lifted, body))
                })
                .collect();
            Located::new(Expression::Case(e, arms, rt), span)
        }
        Expression::Write(e) => Located::new(
            Expression::Write(Box::new(sub_exp_in_exp(xn, rep, *e))),
            span,
        ),
        Expression::Closure(n, es) => {
            let es = es.into_iter().map(|e| sub_exp_in_exp(xn, rep, e)).collect();
            Located::new(Expression::Closure(n, es), span)
        }
        Expression::Let(x, t, e1, e2) => {
            let rep2 = lift_exp_in_exp(0, rep.clone());
            Located::new(
                Expression::Let(
                    x,
                    t,
                    Box::new(sub_exp_in_exp(xn, rep, *e1)),
                    Box::new(sub_exp_in_exp(xn + 1, &rep2, *e2)),
                ),
                span,
            )
        }
        Expression::ServerCall(n, es, t, fm) => {
            let es = es.into_iter().map(|e| sub_exp_in_exp(xn, rep, e)).collect();
            Located::new(Expression::ServerCall(n, es, t, fm), span)
        }
    }
}

// ---------------------------------------------------------------------------
// free_vars — collect free variable indices (>= bound adjusted to top level)
// ---------------------------------------------------------------------------

/// Returns the set of *top-level* free variable indices in `e`.
/// A variable `ERel(x)` at binder depth `bound` has top-level index `x - bound`.
fn free_vars(e: &LocatedExpression) -> BTreeSet<usize> {
    let mut acc = BTreeSet::new();
    collect_free_vars(e, 0, &mut acc);
    acc
}

fn collect_free_vars(e: &LocatedExpression, bound: usize, acc: &mut BTreeSet<usize>) {
    match &e.node {
        Expression::Rel(x) => {
            if *x >= bound {
                acc.insert(x - bound);
            }
        }
        Expression::Prim(_) | Expression::Named(_) | Expression::Ffi(_, _) => {}
        Expression::Constructor(_, _, _, Some(arg)) => collect_free_vars(arg, bound, acc),
        Expression::Constructor(_, _, _, None) => {}
        Expression::FfiApp(_, _, es) => {
            for (e, _) in es {
                collect_free_vars(e, bound, acc);
            }
        }
        Expression::App(f, a) => {
            collect_free_vars(f, bound, acc);
            collect_free_vars(a, bound, acc);
        }
        Expression::Abs(_, _, _, body) => collect_free_vars(body, bound + 1, acc),
        Expression::CApp(f, _) => collect_free_vars(f, bound, acc),
        Expression::CAbs(_, _, body) | Expression::KAbs(_, body) => {
            collect_free_vars(body, bound, acc)
        }
        Expression::KApp(f, _) => collect_free_vars(f, bound, acc),
        Expression::Record(fields) => {
            for (_, e, _) in fields {
                collect_free_vars(e, bound, acc);
            }
        }
        Expression::Field(e, _, _) => collect_free_vars(e, bound, acc),
        Expression::Concat(e1, _, e2, _) => {
            collect_free_vars(e1, bound, acc);
            collect_free_vars(e2, bound, acc);
        }
        Expression::Cut(e, _, _) | Expression::CutMulti(e, _, _) => {
            collect_free_vars(e, bound, acc)
        }
        Expression::Case(e, arms, _) => {
            collect_free_vars(e, bound, acc);
            for (p, body) in arms {
                collect_free_vars(body, bound + pat_binds_n(p), acc);
            }
        }
        Expression::Write(e) => collect_free_vars(e, bound, acc),
        Expression::Closure(_, es) => {
            for e in es {
                collect_free_vars(e, bound, acc);
            }
        }
        Expression::Let(_, _, e1, e2) => {
            collect_free_vars(e1, bound, acc);
            collect_free_vars(e2, bound + 1, acc);
        }
        Expression::ServerCall(_, es, _, _) => {
            for e in es {
                collect_free_vars(e, bound, acc);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// squish — remap free variables to consecutive indices
// ---------------------------------------------------------------------------

/// Remap free variables in `e` so that the free var at `fvs[i]` becomes `i`.
///
/// `fvs` must be in sorted (ascending) order. Variables with index < bound
/// are already bound inside the expression and are left unchanged.
fn squish(fvs: &[usize], e: LocatedExpression) -> LocatedExpression {
    squish_at(fvs, 0, e)
}

fn squish_at(fvs: &[usize], bound: usize, e: LocatedExpression) -> LocatedExpression {
    let span = e.span.clone();
    match e.node {
        Expression::Rel(x) => {
            if x >= bound {
                let free_idx = x - bound;
                let pos = fvs.iter().position(|&v| v == free_idx).unwrap_or(0);
                Located::new(Expression::Rel(pos + bound), span)
            } else {
                Located::new(Expression::Rel(x), span)
            }
        }
        Expression::Prim(_) | Expression::Named(_) | Expression::Ffi(_, _) => e,
        Expression::Constructor(dk, pc, cs, arg) => {
            let arg = arg.map(|a| Box::new(squish_at(fvs, bound, *a)));
            Located::new(Expression::Constructor(dk, pc, cs, arg), span)
        }
        Expression::FfiApp(m, x, es) => {
            let es = es
                .into_iter()
                .map(|(e, t)| (squish_at(fvs, bound, e), t))
                .collect();
            Located::new(Expression::FfiApp(m, x, es), span)
        }
        Expression::App(f, a) => Located::new(
            Expression::App(
                Box::new(squish_at(fvs, bound, *f)),
                Box::new(squish_at(fvs, bound, *a)),
            ),
            span,
        ),
        Expression::Abs(x, t, rt, body) => Located::new(
            Expression::Abs(x, t, rt, Box::new(squish_at(fvs, bound + 1, *body))),
            span,
        ),
        Expression::CApp(f, c) => Located::new(
            Expression::CApp(Box::new(squish_at(fvs, bound, *f)), c),
            span,
        ),
        Expression::CAbs(x, k, body) => Located::new(
            Expression::CAbs(x, k, Box::new(squish_at(fvs, bound, *body))),
            span,
        ),
        Expression::KAbs(x, body) => Located::new(
            Expression::KAbs(x, Box::new(squish_at(fvs, bound, *body))),
            span,
        ),
        Expression::KApp(f, k) => Located::new(
            Expression::KApp(Box::new(squish_at(fvs, bound, *f)), k),
            span,
        ),
        Expression::Record(fields) => {
            let fields = fields
                .into_iter()
                .map(|(c1, e, c2)| (c1, squish_at(fvs, bound, e), c2))
                .collect();
            Located::new(Expression::Record(fields), span)
        }
        Expression::Field(e, c, meta) => Located::new(
            Expression::Field(Box::new(squish_at(fvs, bound, *e)), c, meta),
            span,
        ),
        Expression::Concat(e1, c1, e2, c2) => Located::new(
            Expression::Concat(
                Box::new(squish_at(fvs, bound, *e1)),
                c1,
                Box::new(squish_at(fvs, bound, *e2)),
                c2,
            ),
            span,
        ),
        Expression::Cut(e, c, meta) => Located::new(
            Expression::Cut(Box::new(squish_at(fvs, bound, *e)), c, meta),
            span,
        ),
        Expression::CutMulti(e, c, meta) => Located::new(
            Expression::CutMulti(Box::new(squish_at(fvs, bound, *e)), c, meta),
            span,
        ),
        Expression::Case(e, arms, rt) => {
            let e = Box::new(squish_at(fvs, bound, *e));
            let arms = arms
                .into_iter()
                .map(|(p, body)| {
                    let n = pat_binds_n(&p);
                    (p, squish_at(fvs, bound + n, body))
                })
                .collect();
            Located::new(Expression::Case(e, arms, rt), span)
        }
        Expression::Write(e) => {
            Located::new(Expression::Write(Box::new(squish_at(fvs, bound, *e))), span)
        }
        Expression::Closure(n, es) => {
            let es = es.into_iter().map(|e| squish_at(fvs, bound, e)).collect();
            Located::new(Expression::Closure(n, es), span)
        }
        Expression::Let(x, t, e1, e2) => Located::new(
            Expression::Let(
                x,
                t,
                Box::new(squish_at(fvs, bound, *e1)),
                Box::new(squish_at(fvs, bound + 1, *e2)),
            ),
            span,
        ),
        Expression::ServerCall(n, es, t, fm) => {
            let es = es.into_iter().map(|e| squish_at(fvs, bound, e)).collect();
            Located::new(Expression::ServerCall(n, es, t, fm), span)
        }
    }
}

// ---------------------------------------------------------------------------
// is_poly_t / is_poly
// ---------------------------------------------------------------------------

fn is_poly_t(t: &LocatedConstructor) -> bool {
    match &t.node {
        Constructor::TFun(_, ran) => is_poly_t(ran),
        Constructor::TCFun(_, _, _) | Constructor::TKFun(_, _) => true,
        _ => false,
    }
}

fn is_poly(d: &LocatedDeclaration) -> bool {
    match &d.node {
        Declaration::Val(_, _, t, _, _) => is_poly_t(t),
        Declaration::ValRec(vis) => vis.iter().any(|(_, _, t, _, _)| is_poly_t(t)),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// function_inside — does a constructor contain a function or "known" type?
// ---------------------------------------------------------------------------

fn function_inside(known: &HashSet<usize>, c: &LocatedConstructor) -> bool {
    match &c.node {
        Constructor::TFun(_, _) | Constructor::TCFun(_, _, _) => true,
        Constructor::Ffi(m, x)
            if m == "Basis"
                && matches!(
                    x.as_str(),
                    "transaction"
                        | "eq"
                        | "num"
                        | "ord"
                        | "show"
                        | "read"
                        | "sql_injectable_prim"
                        | "sql_injectable"
                ) =>
        {
            true
        }
        Constructor::Named(n) => known.contains(n),
        Constructor::App(f, a) => function_inside(known, f) || function_inside(known, a),
        Constructor::Abs(_, _, b) | Constructor::KAbs(_, b) | Constructor::TKFun(_, b) => {
            function_inside(known, b)
        }
        Constructor::TRecord(inner) => function_inside(known, inner),
        Constructor::KApp(inner, _) => function_inside(known, inner),
        Constructor::Record(_, pairs) => pairs
            .iter()
            .any(|(n, v)| function_inside(known, n) || function_inside(known, v)),
        Constructor::Concat(a, b) => function_inside(known, a) || function_inside(known, b),
        Constructor::Tuple(cs) => cs.iter().any(|c| function_inside(known, c)),
        Constructor::Proj(c, _) => function_inside(known, c),
        Constructor::Rel(_)
        | Constructor::Name(_)
        | Constructor::Unit
        | Constructor::Map(_, _)
        | Constructor::Ffi(_, _) => false,
    }
}

// ---------------------------------------------------------------------------
// get_app — unwrap EApp spine into (named_fn_id, [args])
// ---------------------------------------------------------------------------

/// Unwrap `EApp(EApp(ENamed f, x1), x2)` into `Some((f, [x1, x2]))`.
/// Returns `None` if the head is not `ENamed`, or if there are no args.
fn get_app_inner(e: &LocatedExpression, args: &mut Vec<LocatedExpression>) -> Option<usize> {
    match &e.node {
        Expression::Named(f) => Some(*f),
        Expression::App(f, a) => {
            let id = get_app_inner(f, args)?;
            args.push(*a.clone());
            Some(id)
        }
        _ => None,
    }
}

fn get_app(e: &LocatedExpression) -> Option<(usize, Vec<LocatedExpression>)> {
    let mut args = vec![];
    let id = get_app_inner(e, &mut args)?;
    if args.is_empty() {
        return None;
    }
    // Args are collected innermost-first; reverse to get outermost-first.
    args.reverse();
    Some((id, args))
}

// ---------------------------------------------------------------------------
// calc_const_args
// ---------------------------------------------------------------------------

const MAX_INT: usize = usize::MAX;

/// Compute how many leading arguments of `e` (treated as a lambda) never
/// vary across recursive calls to functions in `enclosing`.
fn calc_const_args(enclosing: &HashSet<usize>, e: &LocatedExpression) -> usize {
    fn enter_abs(enclosing: &HashSet<usize>, depth: usize, e: &LocatedExpression) -> usize {
        match &e.node {
            Expression::Abs(_, _, _, body) => enter_abs(enclosing, depth + 1, body),
            _ => ca(enclosing, depth, e),
        }
    }

    fn ca(enclosing: &HashSet<usize>, depth: usize, e: &LocatedExpression) -> usize {
        match &e.node {
            Expression::Prim(_) => MAX_INT,
            Expression::Rel(_) => MAX_INT,
            Expression::Named(n) => {
                if enclosing.contains(n) {
                    0
                } else {
                    MAX_INT
                }
            }
            Expression::Constructor(_, _, _, None) => MAX_INT,
            Expression::Constructor(_, _, _, Some(arg)) => ca(enclosing, depth, arg),
            Expression::Ffi(_, _) => MAX_INT,
            Expression::FfiApp(_, _, ecs) => ecs
                .iter()
                .fold(MAX_INT, |d, (e, _)| d.min(ca(enclosing, depth, e))),
            Expression::App(e1, e2) => {
                let def = || ca(enclosing, depth, e1).min(ca(enclosing, depth, e2));
                match get_app(e) {
                    None => def(),
                    Some((f, args)) => {
                        if !enclosing.contains(&f) {
                            def()
                        } else {
                            visit_args(enclosing, depth, 0, &args)
                        }
                    }
                }
            }
            Expression::Abs(_, _, _, body) => ca(enclosing, depth + 1, body),
            Expression::CApp(e1, _) | Expression::KApp(e1, _) => ca(enclosing, depth, e1),
            Expression::CAbs(_, _, body) | Expression::KAbs(_, body) => ca(enclosing, depth, body),
            Expression::Record(fields) => fields
                .iter()
                .fold(MAX_INT, |d, (_, e, _)| d.min(ca(enclosing, depth, e))),
            Expression::Field(e1, _, _) => ca(enclosing, depth, e1),
            Expression::Concat(e1, _, e2, _) => {
                ca(enclosing, depth, e1).min(ca(enclosing, depth, e2))
            }
            Expression::Cut(e1, _, _) | Expression::CutMulti(e1, _, _) => ca(enclosing, depth, e1),
            Expression::Case(e1, arms, _) => {
                let mut d = ca(enclosing, depth, e1);
                for (p, body) in arms {
                    let n = pat_binds_n(p);
                    d = d.min(ca(enclosing, depth + n, body));
                }
                d
            }
            Expression::Write(e1) => ca(enclosing, depth, e1),
            Expression::Closure(_, es) => es
                .iter()
                .fold(MAX_INT, |d, e| d.min(ca(enclosing, depth, e))),
            Expression::Let(_, _, e1, e2) => {
                ca(enclosing, depth, e1).min(ca(enclosing, depth + 1, e2))
            }
            Expression::ServerCall(_, es, _, _) => es
                .iter()
                .fold(MAX_INT, |d, e| d.min(ca(enclosing, depth, e))),
        }
    }

    fn visit_args(
        enclosing: &HashSet<usize>,
        depth: usize,
        count: usize,
        args: &[LocatedExpression],
    ) -> usize {
        match args {
            [] => count,
            [arg, rest @ ..] => match &arg.node {
                Expression::Rel(n) if *n == depth.wrapping_sub(1).wrapping_sub(count) => {
                    // depth >= 1 + count
                    if depth > count && *n == depth - 1 - count {
                        visit_args(enclosing, depth, count + 1, rest)
                    } else {
                        // fall through to default
                        rest.iter()
                            .fold(count, |d, e| d.min(ca(enclosing, depth, e)))
                    }
                }
                Expression::Rel(n) if depth > count && *n == depth - 1 - count => {
                    visit_args(enclosing, depth, count + 1, rest)
                }
                _ => rest
                    .iter()
                    .fold(count, |d, e| d.min(ca(enclosing, depth, e))),
            },
        }
    }

    enter_abs(enclosing, 0, e)
}

// ---------------------------------------------------------------------------
// Expression total ordering (for BTreeMap cache key)
// ---------------------------------------------------------------------------

fn cmp_exp(a: &LocatedExpression, b: &LocatedExpression) -> Ordering {
    cmp_exp_node(&a.node, &b.node)
}

fn cmp_exp_node(a: &Expression, b: &Expression) -> Ordering {
    fn disc(e: &Expression) -> u8 {
        match e {
            Expression::Prim(_) => 0,
            Expression::Rel(_) => 1,
            Expression::Named(_) => 2,
            Expression::Ffi(_, _) => 3,
            Expression::Constructor(_, _, _, _) => 4,
            Expression::FfiApp(_, _, _) => 5,
            Expression::App(_, _) => 6,
            Expression::Abs(_, _, _, _) => 7,
            Expression::CApp(_, _) => 8,
            Expression::CAbs(_, _, _) => 9,
            Expression::KAbs(_, _) => 10,
            Expression::KApp(_, _) => 11,
            Expression::Record(_) => 12,
            Expression::Field(_, _, _) => 13,
            Expression::Concat(_, _, _, _) => 14,
            Expression::Cut(_, _, _) => 15,
            Expression::CutMulti(_, _, _) => 16,
            Expression::Case(_, _, _) => 17,
            Expression::Write(_) => 18,
            Expression::Closure(_, _) => 19,
            Expression::Let(_, _, _, _) => 20,
            Expression::ServerCall(_, _, _, _) => 21,
        }
    }
    let da = disc(a);
    let db = disc(b);
    if da != db {
        return da.cmp(&db);
    }
    match (a, b) {
        (Expression::Prim(pa), Expression::Prim(pb)) => {
            // Use debug repr for ordering (simple but correct)
            format!("{pa:?}").cmp(&format!("{pb:?}"))
        }
        (Expression::Rel(x), Expression::Rel(y)) => x.cmp(y),
        (Expression::Named(x), Expression::Named(y)) => x.cmp(y),
        (Expression::Ffi(m1, x1), Expression::Ffi(m2, x2)) => m1.cmp(m2).then_with(|| x1.cmp(x2)),
        (Expression::App(f1, a1), Expression::App(f2, a2)) => {
            cmp_exp(f1, f2).then_with(|| cmp_exp(a1, a2))
        }
        (Expression::Rel(_), _)
        | (Expression::Named(_), _)
        | (Expression::Ffi(_, _), _)
        | (Expression::App(_, _), _) => Ordering::Equal, // same discriminant handled above
        // For other variants just use Equal (they won't appear as spec keys in practice)
        _ => Ordering::Equal,
    }
}

// ---------------------------------------------------------------------------
// Cache key
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct CacheKey {
    var_types: Vec<LocatedConstructor>,
    spec_args: Vec<LocatedExpression>,
}

impl PartialEq for CacheKey {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}
impl Eq for CacheKey {}

impl PartialOrd for CacheKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CacheKey {
    fn cmp(&self, other: &Self) -> Ordering {
        let n1 = self.var_types.len();
        let n2 = other.var_types.len();
        n1.cmp(&n2)
            .then_with(|| {
                for (a, b) in self.var_types.iter().zip(&other.var_types) {
                    let o = con_util::compare(a, b);
                    if o != Ordering::Equal {
                        return o;
                    }
                }
                Ordering::Equal
            })
            .then_with(|| {
                let m1 = self.spec_args.len();
                let m2 = other.spec_args.len();
                m1.cmp(&m2)
            })
            .then_with(|| {
                for (a, b) in self.spec_args.iter().zip(&other.spec_args) {
                    let o = cmp_exp(a, b);
                    if o != Ordering::Equal {
                        return o;
                    }
                }
                Ordering::Equal
            })
    }
}

// ---------------------------------------------------------------------------
// FuncInfo / State
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct FuncInfo {
    name: String,
    /// Cache: key → specialized function id.
    args: BTreeMap<CacheKey, usize>,
    body: LocatedExpression,
    typ: LocatedConstructor,
    tag: String,
    const_args: usize,
}

struct State {
    max_name: usize,
    funcs: HashMap<usize, FuncInfo>,
    /// Accumulated new DVal decls (name, id, typ, body, tag).
    decls: Vec<(String, usize, LocatedConstructor, LocatedExpression, String)>,
    specialized: HashSet<usize>,
}

// ---------------------------------------------------------------------------
// build_known — set of Named type ids that contain function types
// ---------------------------------------------------------------------------

fn build_known(file: &File) -> HashSet<usize> {
    // Collect Named constructors that contain function types or already-known Named ids.
    // Fixed-point: iterate until stable (bounded to prevent runaway mutants).
    const MAX_BUILD_KNOWN_ITERATIONS: usize = 10_000;
    let mut known: HashSet<usize> = HashSet::new();
    let mut iterations = 0;
    loop {
        let mut changed = false;
        for d in file {
            match &d.node {
                Declaration::Constructor(_, n, _, c) => {
                    if !known.contains(n) && function_inside(&known, c) {
                        known.insert(*n);
                        changed = true;
                    }
                }
                Declaration::Datatype(dts) => {
                    for dt in dts {
                        if !known.contains(&dt.id) {
                            let has_fn = dt.constrs.iter().any(|(_, _, ot)| {
                                ot.as_ref().is_some_and(|t| function_inside(&known, t))
                            });
                            if has_fn {
                                known.insert(dt.id);
                                changed = true;
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        iterations += 1;
        if !changed || iterations >= MAX_BUILD_KNOWN_ITERATIONS {
            break;
        }
    }
    known
}

// ---------------------------------------------------------------------------
// sub_body — substitute specialization args into a lambda body
// ---------------------------------------------------------------------------

/// Strip `n` outer `EAbs` layers from `body`/`typ`, substituting `args[i]`
/// for `Rel 0` at each step.
fn sub_body(
    body: LocatedExpression,
    typ: LocatedConstructor,
    args: &[LocatedExpression],
) -> Option<(LocatedExpression, LocatedConstructor)> {
    if args.is_empty() {
        return Some((body, typ));
    }
    match (body.node, typ.node, args) {
        (Expression::Abs(_, _, _, inner_body), Constructor::TFun(_, ran), [x, rest @ ..]) => {
            let new_body = sub_exp_in_exp(0, x, *inner_body);
            sub_body(new_body, *ran, rest)
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// The main rewrite: exp
// ---------------------------------------------------------------------------

/// Rewrite expression `e` in environment `env` (innermost-first list of
/// (name, type) pairs), threading state.
fn rewrite_exp(
    env: &[(String, LocatedConstructor)],
    e: LocatedExpression,
    known: &HashSet<usize>,
    st: &mut State,
) -> LocatedExpression {
    let _span = e.span.clone();

    // Check if this is an application of a known specialized function.
    match get_app(&e) {
        Some((f, xs)) if st.funcs.contains_key(&f) => {
            // Rewrite all args first.
            let xs: Vec<LocatedExpression> = xs
                .into_iter()
                .map(|x| rewrite_exp(env, x, known, st))
                .collect();

            let Some(fi) = st.funcs.get(&f).cloned() else {
                eprintln!(
                    "{}",
                    crate::compiler_diagnostics::internal_compiler_error(
                        "especialize::rewrite_exp",
                        "missing specialization metadata for a function that was just in the cache",
                    )
                );
                return rewrite_exp_default(env, e, known, st);
            };
            let const_args = fi.const_args;
            let typ = fi.typ.clone();

            let old_xs = xs.clone();

            // Find the prefix of args to specialize on.
            let (fxs, remaining_xs, fvs) = find_split(&typ, const_args, &xs, known, old_xs.clone());

            let fvs_sorted: Vec<usize> = fvs.iter().cloned().collect(); // already sorted (BTreeSet)

            // Types of free variables (looked up from env).
            let vts: Vec<LocatedConstructor> =
                fvs_sorted.iter().map(|&n| env[n].1.clone()).collect();

            // Squished specialized args.
            let fxs_prime: Vec<LocatedExpression> =
                fxs.iter().map(|x| squish(&fvs_sorted, x.clone())).collect();

            // If all squished args are just variables → don't specialize.
            let all_rel = fxs_prime
                .iter()
                .all(|e| matches!(e.node, Expression::Rel(_)));

            if all_rel || fxs_prime.is_empty() {
                return rewrite_exp_default(env, e, known, st);
            }

            let key = CacheKey {
                var_types: vts.clone(),
                spec_args: fxs_prime.clone(),
            };

            // Check memoization cache.
            let dummy = Span::dummy();
            if let Some(&f_prime) = st
                .funcs
                .get(&f)
                .and_then(|fi_cache| fi_cache.args.get(&key))
            {
                // Reuse existing specialization.
                let mut result = Located::new(Expression::Named(f_prime), dummy.clone());
                // Apply free vars in decreasing order (foldr on sorted set).
                for &arg in fvs_sorted.iter().rev() {
                    result = Located::new(
                        Expression::App(
                            Box::new(result),
                            Box::new(Located::new(Expression::Rel(arg), dummy.clone())),
                        ),
                        dummy.clone(),
                    );
                }
                // Apply remaining args.
                for arg in remaining_xs {
                    result = Located::new(
                        Expression::App(Box::new(result), Box::new(arg)),
                        dummy.clone(),
                    );
                }
                return result;
            }

            // Create new specialization.
            let f_prime = st.max_name;
            st.max_name += 1;

            // Update funcs cache for f.
            if let Some(fi_mut) = st.funcs.get_mut(&f) {
                fi_mut.args.insert(key, f_prime);
            }
            // Mark as specialized.
            st.specialized.insert(f_prime);

            // Substitute fxs_prime into the body.
            let body = fi.body.clone();
            let typ_fi = fi.typ.clone();
            let name = fi.name.clone();
            let tag = fi.tag.clone();

            let sub_result = sub_body(body, typ_fi, &fxs_prime);
            let Some((mut new_body, mut new_typ)) = sub_result else {
                return rewrite_exp_default(env, e, known, st);
            };

            // Wrap in lambdas for the captured free variables (foldl → increasing order).
            for &n in &fvs_sorted {
                let (var_name, xt) = env[n].clone();
                let wrapped_body = Located::new(
                    Expression::Abs(var_name, xt.clone(), new_typ.clone(), Box::new(new_body)),
                    dummy.clone(),
                );
                let wrapped_typ = Located::new(
                    Constructor::TFun(Box::new(xt), Box::new(new_typ)),
                    dummy.clone(),
                );
                new_body = wrapped_body;
                new_typ = wrapped_typ;
            }

            // Reduce body.
            // (mirrors ReduceLocal.reduceExp body')
            // We use the file-level reduce on a synthetic file.
            // For now use the expression-level reduce from local_reduction.
            new_body = crate::core::local_reduction::reduce_exp(new_body);

            // Recursively rewrite the new body.
            new_body = rewrite_exp(env, new_body, known, st);

            // Emit as new decl.
            st.decls.push((name, f_prime, new_typ, new_body, tag));

            // Build result expression.
            let mut result = Located::new(Expression::Named(f_prime), dummy.clone());
            for &arg in fvs_sorted.iter().rev() {
                result = Located::new(
                    Expression::App(
                        Box::new(result),
                        Box::new(Located::new(Expression::Rel(arg), dummy.clone())),
                    ),
                    dummy.clone(),
                );
            }
            for arg in remaining_xs {
                result = Located::new(
                    Expression::App(Box::new(result), Box::new(arg)),
                    dummy.clone(),
                );
            }
            result
        }
        _ => rewrite_exp_default(env, e, known, st),
    }
}

/// The "default" rewrite: just recurse into sub-expressions.
fn rewrite_exp_default(
    env: &[(String, LocatedConstructor)],
    e: LocatedExpression,
    known: &HashSet<usize>,
    st: &mut State,
) -> LocatedExpression {
    let span = e.span.clone();
    match e.node {
        Expression::Prim(_) | Expression::Rel(_) | Expression::Named(_) | Expression::Ffi(_, _) => {
            e
        }
        Expression::Constructor(dk, pc, cs, None) => {
            Located::new(Expression::Constructor(dk, pc, cs, None), span)
        }
        Expression::Constructor(dk, pc, cs, Some(arg)) => {
            let arg = rewrite_exp(env, *arg, known, st);
            Located::new(
                Expression::Constructor(dk, pc, cs, Some(Box::new(arg))),
                span,
            )
        }
        Expression::FfiApp(m, x, es) => {
            let es = es
                .into_iter()
                .map(|(e, t)| (rewrite_exp(env, e, known, st), t))
                .collect();
            Located::new(Expression::FfiApp(m, x, es), span)
        }
        Expression::App(f, a) => {
            let f = rewrite_exp(env, *f, known, st);
            let a = rewrite_exp(env, *a, known, st);
            Located::new(Expression::App(Box::new(f), Box::new(a)), span)
        }
        Expression::Abs(x, t, rt, body) => {
            let mut new_env = vec![(x.clone(), t.clone())];
            new_env.extend_from_slice(env);
            let body = rewrite_exp(&new_env, *body, known, st);
            Located::new(Expression::Abs(x, t, rt, Box::new(body)), span)
        }
        Expression::CApp(f, c) => {
            let f = rewrite_exp(env, *f, known, st);
            Located::new(Expression::CApp(Box::new(f), c), span)
        }
        Expression::CAbs(x, k, body) => {
            // CAbs doesn't bind an expression variable.
            let body = rewrite_exp(env, *body, known, st);
            Located::new(Expression::CAbs(x, k, Box::new(body)), span)
        }
        Expression::KAbs(x, body) => {
            let body = rewrite_exp(env, *body, known, st);
            Located::new(Expression::KAbs(x, Box::new(body)), span)
        }
        Expression::KApp(f, k) => {
            let f = rewrite_exp(env, *f, known, st);
            Located::new(Expression::KApp(Box::new(f), k), span)
        }
        Expression::Record(fields) => {
            let fields = fields
                .into_iter()
                .map(|(c1, e, c2)| (c1, rewrite_exp(env, e, known, st), c2))
                .collect();
            Located::new(Expression::Record(fields), span)
        }
        Expression::Field(e, c, meta) => {
            let e = rewrite_exp(env, *e, known, st);
            Located::new(Expression::Field(Box::new(e), c, meta), span)
        }
        Expression::Concat(e1, c1, e2, c2) => {
            let e1 = rewrite_exp(env, *e1, known, st);
            let e2 = rewrite_exp(env, *e2, known, st);
            Located::new(Expression::Concat(Box::new(e1), c1, Box::new(e2), c2), span)
        }
        Expression::Cut(e, c, meta) => {
            let e = rewrite_exp(env, *e, known, st);
            Located::new(Expression::Cut(Box::new(e), c, meta), span)
        }
        Expression::CutMulti(e, c, meta) => {
            let e = rewrite_exp(env, *e, known, st);
            Located::new(Expression::CutMulti(Box::new(e), c, meta), span)
        }
        Expression::Case(e, arms, rt) => {
            let e = rewrite_exp(env, *e, known, st);
            let arms = arms
                .into_iter()
                .map(|(p, body)| {
                    // Pattern binds go onto the front of env.
                    let pat_binds = crate::core::environment::pat_binds_list(&p);
                    let mut new_env: Vec<(String, LocatedConstructor)> =
                        pat_binds.into_iter().rev().collect();
                    new_env.extend_from_slice(env);
                    let body = rewrite_exp(&new_env, body, known, st);
                    (p, body)
                })
                .collect();
            Located::new(Expression::Case(Box::new(e), arms, rt), span)
        }
        Expression::Write(e) => {
            let e = rewrite_exp(env, *e, known, st);
            Located::new(Expression::Write(Box::new(e)), span)
        }
        Expression::Closure(n, es) => {
            let es = es
                .into_iter()
                .map(|e| rewrite_exp(env, e, known, st))
                .collect();
            Located::new(Expression::Closure(n, es), span)
        }
        Expression::Let(x, t, e1, e2) => {
            let e1 = rewrite_exp(env, *e1, known, st);
            let mut new_env = vec![(x.clone(), t.clone())];
            new_env.extend_from_slice(env);
            let e2 = rewrite_exp(&new_env, *e2, known, st);
            Located::new(Expression::Let(x, t, Box::new(e1), Box::new(e2)), span)
        }
        Expression::ServerCall(n, es, t, fm) => {
            let es = es
                .into_iter()
                .map(|e| rewrite_exp(env, e, known, st))
                .collect();
            Located::new(Expression::ServerCall(n, es, t, fm), span)
        }
    }
}

// ---------------------------------------------------------------------------
// find_split — identify constant specialized args
// ---------------------------------------------------------------------------

/// Returns `(fxs, remaining_xs, fvs)`:
/// - `fxs`: the prefix of `xs` to specialize on
/// - `remaining_xs`: the rest (passed through)
/// - `fvs`: union of free variables in `fxs`
fn find_split(
    typ: &LocatedConstructor,
    const_args: usize,
    xs: &[LocatedExpression],
    known: &HashSet<usize>,
    old_xs: Vec<LocatedExpression>,
) -> (
    Vec<LocatedExpression>,
    Vec<LocatedExpression>,
    BTreeSet<usize>,
) {
    find_split_rec(
        typ,
        const_args,
        xs,
        known,
        &old_xs,
        true,
        vec![],
        BTreeSet::new(),
    )
}

#[allow(clippy::too_many_arguments)]
fn find_split_rec(
    typ: &LocatedConstructor,
    const_args: usize,
    xs: &[LocatedExpression],
    known: &HashSet<usize>,
    old_xs: &[LocatedExpression],
    initial_part: bool,
    fxs: Vec<LocatedExpression>,
    fvs: BTreeSet<usize>,
) -> (
    Vec<LocatedExpression>,
    Vec<LocatedExpression>,
    BTreeSet<usize>,
) {
    // Default: stop here.
    let default = || {
        if initial_part {
            (vec![], old_xs.to_vec(), BTreeSet::new())
        } else {
            (fxs.clone(), xs.to_vec(), fvs.clone())
        }
    };

    match (&typ.node, xs) {
        (Constructor::TFun(dom, ran), [e, rest @ ..]) if const_args > 0 => {
            let fi = function_inside(known, dom);
            if initial_part || fi {
                let mut new_fvs = fvs.clone();
                new_fvs.extend(free_vars(e));
                let mut new_fxs = fxs;
                new_fxs.push(e.clone());
                let new_initial_part = !fi && initial_part;
                find_split_rec(
                    ran,
                    const_args - 1,
                    rest,
                    known,
                    old_xs,
                    new_initial_part,
                    new_fxs,
                    new_fvs,
                )
            } else {
                default()
            }
        }
        _ => default(),
    }
}

// ---------------------------------------------------------------------------
// specialize_pass — single pass over a file
// ---------------------------------------------------------------------------

fn specialize_pass(
    funcs: HashMap<usize, FuncInfo>,
    specialized: HashSet<usize>,
    file: File,
) -> (bool, File, HashMap<usize, FuncInfo>, HashSet<usize>) {
    let known = build_known(&file);
    let max_name = file_util::max_name(&file) + 1;

    let mut st = State {
        max_name,
        funcs,
        decls: vec![],
        specialized,
    };

    let mut changed = false;
    let mut out: File = vec![];

    for d in file {
        let span = d.span.clone();

        // Pre-register DValRec functions.
        if let Declaration::ValRec(vis) = &d.node {
            let enclosing: HashSet<usize> = vis.iter().map(|(_, n, _, _, _)| *n).collect();
            let ca = vis
                .iter()
                .map(|(_, _, _, e, _)| calc_const_args(&enclosing, e))
                .min()
                .unwrap_or(0);
            for (x, n, c, e, tag) in vis {
                st.funcs.insert(
                    *n,
                    FuncInfo {
                        name: x.clone(),
                        args: BTreeMap::new(),
                        body: e.clone(),
                        typ: c.clone(),
                        tag: tag.clone(),
                        const_args: ca,
                    },
                );
            }
        }

        // Reset accumulated decls for this declaration.
        st.decls.clear();

        // Rewrite non-polymorphic declarations.
        let d_prime = if is_poly(&d) {
            d.clone()
        } else {
            match d.node.clone() {
                Declaration::Val(x, n, t, e, s) => {
                    let e2 = rewrite_exp(&[], e, &known, &mut st);
                    Located::new(Declaration::Val(x, n, t, e2, s), span.clone())
                }
                Declaration::ValRec(vis) => {
                    let vis2 = vis
                        .into_iter()
                        .map(|(x, n, t, e, s)| {
                            let e2 = rewrite_exp(&[], e, &known, &mut st);
                            (x, n, t, e2, s)
                        })
                        .collect();
                    Located::new(Declaration::ValRec(vis2), span.clone())
                }
                Declaration::Table {
                    sql_name,
                    id,
                    con,
                    sql_con,
                    exp,
                    pk_con,
                    pk_exp,
                    unique_con,
                } => {
                    let exp_b = rewrite_exp(&[], exp, &known, &mut st);
                    let pk_exp_b = rewrite_exp(&[], pk_exp, &known, &mut st);
                    Located::new(
                        Declaration::Table {
                            sql_name,
                            id,
                            con,
                            sql_con,
                            exp: exp_b,
                            pk_con,
                            pk_exp: pk_exp_b,
                            unique_con,
                        },
                        span.clone(),
                    )
                }
                Declaration::View(x, n, s, e, t) => {
                    let eb = rewrite_exp(&[], e, &known, &mut st);
                    Located::new(Declaration::View(x, n, s, eb, t), span.clone())
                }
                Declaration::Task(e1, e2) => {
                    let e1b = rewrite_exp(&[], e1, &known, &mut st);
                    let e2b = rewrite_exp(&[], e2, &known, &mut st);
                    Located::new(Declaration::Task(e1b, e2b), span.clone())
                }
                other => Located::new(other, span.clone()),
            }
        };

        // Post-register DVal functions (after rewrite).
        let funcs_update = match &d.node {
            Declaration::Val(x, n, c, e, tag) => {
                if matches!(e.node, Expression::Abs(_, _, _, _)) {
                    let enclosing: HashSet<usize> = std::iter::once(*n).collect();
                    let ca = calc_const_args(&enclosing, e);
                    Some((
                        *n,
                        FuncInfo {
                            name: x.clone(),
                            args: BTreeMap::new(),
                            body: e.clone(),
                            typ: c.clone(),
                            tag: tag.clone(),
                            const_args: ca,
                        },
                    ))
                } else if let Expression::Named(n2) = e.node {
                    // Alias: copy the func info from n2.
                    st.funcs.get(&n2).cloned().map(|fi| (*n, fi))
                } else {
                    None
                }
            }
            _ => None,
        };
        if let Some((n, fi)) = funcs_update {
            st.funcs.insert(n, fi);
        }

        // Merge accumulated decls.
        let new_decls = std::mem::take(&mut st.decls);
        if new_decls.is_empty() {
            out.push(d_prime);
        } else {
            changed = true;
            let dummy_span = Span::dummy();
            // Build DValRec from new_decls and merge with d_prime.
            let vis_new: Vec<(String, usize, LocatedConstructor, LocatedExpression, String)> =
                new_decls;
            match &d_prime.node {
                Declaration::ValRec(existing) => {
                    let mut merged = vis_new;
                    merged.extend(existing.clone());
                    out.push(Located::new(Declaration::ValRec(merged), dummy_span));
                }
                _ => {
                    out.push(Located::new(Declaration::ValRec(vis_new), dummy_span));
                    out.push(d_prime);
                }
            }
        }
    }

    (changed, out, st.funcs, st.specialized)
}

// ---------------------------------------------------------------------------
// Fixed-point loop
// ---------------------------------------------------------------------------

const MAX_ESPECIALIZE_ITERATIONS: usize = 1000;

fn especialize_loop(
    funcs: HashMap<usize, FuncInfo>,
    specialized: HashSet<usize>,
    file: File,
    iterations: usize,
) -> File {
    if iterations >= MAX_ESPECIALIZE_ITERATIONS {
        return file;
    }
    let file = reduce(file);
    let (changed, file, funcs, specialized) = specialize_pass(funcs, specialized, file);
    if changed {
        let file = untangle(file);
        let file = shake(file);
        especialize_loop(funcs, specialized, file, iterations + 1)
    } else {
        file
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Run the expression specialization pass to a fixed point.
pub fn especialize(file: File) -> File {
    especialize_loop(HashMap::new(), HashSet::new(), file, 0)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error_types::Located;

    fn dummy<T>(node: T) -> Located<T> {
        Located::dummy(node)
    }

    fn dummy_kind() -> LocatedKind {
        dummy(Kind::Type)
    }

    fn dummy_con() -> LocatedConstructor {
        dummy(Constructor::Unit)
    }

    fn dummy_span() -> Span {
        Span::dummy()
    }

    /// Empty file passes through unchanged.
    #[test]
    fn test_empty_file() {
        let result = especialize(vec![]);
        assert!(result.is_empty());
    }

    /// A non-functional declaration passes through unchanged.
    #[test]
    fn test_non_val_passthrough() {
        let file: File = vec![dummy(Declaration::Database("mydb".into()))];
        let result = especialize(file);
        assert_eq!(result.len(), 1);
        assert!(matches!(result[0].node, Declaration::Database(_)));
    }

    /// A simple non-polymorphic Val declaration passes through.
    #[test]
    fn test_simple_val_passthrough() {
        let file: File = vec![dummy(Declaration::Val(
            "x".into(),
            1,
            dummy(Constructor::Unit),
            dummy(Expression::Named(0)),
            String::new(),
        ))];
        let result = especialize(file);
        assert_eq!(result.len(), 1);
        assert!(matches!(result[0].node, Declaration::Val(_, 1, _, _, _)));
    }

    /// lift_exp_in_exp increments free Rel indices.
    #[test]
    fn test_lift_exp() {
        let e = dummy(Expression::Rel(0));
        let lifted = lift_exp_in_exp(0, e);
        assert!(matches!(lifted.node, Expression::Rel(1)));
    }

    /// lift_exp_in_exp leaves bound Rel indices alone.
    #[test]
    fn test_lift_exp_bound() {
        // depth=1: Rel(0) is bound, Rel(1) is free.
        let e = dummy(Expression::Rel(0));
        let lifted = lift_exp_by(1, 1, e);
        assert!(matches!(lifted.node, Expression::Rel(0)));
    }

    /// lift_exp_by uses + not - or * for free vars. Rel(2) at depth 1, by=1 => Rel(3).
    /// Catches mutants: replace n+by with n-by (would give Rel(1)) or n*by (would give Rel(2)).
    #[test]
    fn test_lift_exp_by_uses_plus() {
        let e = dummy(Expression::Rel(2));
        let lifted = lift_exp_by(1, 1, e);
        assert!(
            matches!(lifted.node, Expression::Rel(3)),
            "Rel(2) at depth 1 with by=1 must become Rel(3) (n+by), not Rel(1) (n-by) or Rel(2) (n*by)"
        );
    }

    /// sub_exp_in_exp replaces the target variable.
    #[test]
    fn test_sub_exp_basic() {
        let rep = dummy(Expression::Named(42));
        let body = dummy(Expression::Rel(0));
        let result = sub_exp_in_exp(0, &rep, body);
        assert!(matches!(result.node, Expression::Named(42)));
    }

    /// sub_exp_in_exp decrements Rel(n > xn).
    #[test]
    fn test_sub_exp_decrement() {
        let rep = dummy(Expression::Named(42));
        let body = dummy(Expression::Rel(1)); // xn=0, so 1 > 0 → Rel(0)
        let result = sub_exp_in_exp(0, &rep, body);
        assert!(matches!(result.node, Expression::Rel(0)));
    }

    /// free_vars correctly identifies free variables.
    #[test]
    fn test_free_vars_rel() {
        let e = dummy(Expression::Rel(2));
        let fvs = free_vars(&e);
        assert_eq!(fvs, BTreeSet::from([2]));
    }

    /// free_vars excludes bound variables.
    #[test]
    fn test_free_vars_bound() {
        // Under an Abs, Rel(0) is bound.
        let inner = dummy(Expression::Rel(0));
        let e = dummy(Expression::Abs(
            "x".into(),
            dummy_con(),
            dummy_con(),
            Box::new(inner),
        ));
        let fvs = free_vars(&e);
        assert!(fvs.is_empty());
    }

    /// squish remaps a single free var to position 0.
    #[test]
    fn test_squish_single() {
        let e = dummy(Expression::Rel(3));
        let result = squish(&[3], e);
        assert!(matches!(result.node, Expression::Rel(0)));
    }

    /// is_poly_t recognizes polymorphic types.
    #[test]
    fn test_is_poly_t() {
        let tc = dummy(Constructor::TCFun(
            "a".into(),
            Box::new(dummy(Kind::Type)),
            Box::new(dummy(Constructor::Unit)),
        ));
        assert!(is_poly_t(&tc));
        assert!(!is_poly_t(&dummy(Constructor::Unit)));
    }

    /// function_inside detects TFun.
    #[test]
    fn test_function_inside_tfun() {
        let known = HashSet::new();
        let c = dummy(Constructor::TFun(
            Box::new(dummy(Constructor::Unit)),
            Box::new(dummy(Constructor::Unit)),
        ));
        assert!(function_inside(&known, &c));
    }

    /// function_inside false for Unit.
    #[test]
    fn test_function_inside_unit() {
        let known = HashSet::new();
        assert!(!function_inside(&known, &dummy(Constructor::Unit)));
    }

    /// get_app unwraps a single application.
    #[test]
    fn test_get_app_single() {
        let arg = dummy(Expression::Named(99));
        let e = dummy(Expression::App(
            Box::new(dummy(Expression::Named(1))),
            Box::new(arg.clone()),
        ));
        let result = get_app(&e);
        assert!(result.is_some());
        let (f, args) = result.unwrap();
        assert_eq!(f, 1);
        assert_eq!(args.len(), 1);
    }

    /// get_app returns None for bare Named (no args).
    #[test]
    fn test_get_app_no_args() {
        let e = dummy(Expression::Named(1));
        assert!(get_app(&e).is_none());
    }

    // --- Plan: Catch Missed Mutants - especialize ---

    #[test]
    fn test_lift_exp_by_abs_increments_depth() {
        // Kills: depth+1 -> depth-1 in Abs. Abs body Rel(1) at depth 0 -> Rel(2).
        let body = dummy(Expression::Rel(1));
        let abs = dummy(Expression::Abs(
            "x".into(),
            dummy_con(),
            dummy_con(),
            Box::new(body),
        ));
        let lifted = lift_exp_by(0, 1, abs);
        let Expression::Abs(_, _, _, inner) = lifted.node else {
            panic!("expected Abs")
        };
        assert!(matches!(inner.node, Expression::Rel(2)));
    }

    #[test]
    fn test_lift_exp_by_let_increments_rhs() {
        // Kills: depth+1 in Let. Rel(1) in e2 (free) at depth 0 -> Rel(2).
        let e2 = dummy(Expression::Rel(1));
        let let_exp = dummy(Expression::Let(
            "x".into(),
            dummy_con(),
            Box::new(dummy(Expression::Prim(Prim::Int(0)))),
            Box::new(e2),
        ));
        let lifted = lift_exp_by(0, 1, let_exp);
        let Expression::Let(_, _, _, e2_out) = lifted.node else {
            panic!("expected Let")
        };
        assert!(matches!(e2_out.node, Expression::Rel(2)));
    }

    #[test]
    fn test_sub_exp_decrements_not_increment() {
        // Kills: n-1 -> n+1. Rel(2) with xn=0 -> Rel(1).
        let rep = dummy(Expression::Named(0));
        let body = dummy(Expression::Rel(2));
        let result = sub_exp_in_exp(0, &rep, body);
        assert!(matches!(result.node, Expression::Rel(1)));
    }

    #[test]
    fn test_free_vars_union() {
        // Kills: insert (union) in collect_free_vars. App(Rel(0), Rel(1)) -> {0, 1}.
        let e = dummy(Expression::App(
            Box::new(dummy(Expression::Rel(0))),
            Box::new(dummy(Expression::Rel(1))),
        ));
        let fvs = free_vars(&e);
        assert_eq!(fvs.len(), 2);
        assert!(fvs.contains(&0));
        assert!(fvs.contains(&1));
    }

    #[test]
    fn test_is_poly_t_tfun() {
        // Kills: delete TFun arm. TFun(_, TCFun) recurses and returns true.
        let tfun = dummy(Constructor::TFun(
            Box::new(dummy(Constructor::Unit)),
            Box::new(dummy(Constructor::TCFun(
                "a".into(),
                Box::new(dummy(Kind::Type)),
                Box::new(dummy(Constructor::Unit)),
            ))),
        ));
        assert!(is_poly_t(&tfun));
    }

    #[test]
    fn test_function_inside_basis_transaction() {
        // Kills: guard m=="Basis" && matches transaction.
        let c = dummy(Constructor::Ffi("Basis".into(), "transaction".into()));
        assert!(function_inside(&HashSet::new(), &c));
    }

    #[test]
    fn test_function_inside_other_false() {
        // Kills: guard. Other.foo is not "function inside".
        let c = dummy(Constructor::Ffi("Other".into(), "foo".into()));
        assert!(!function_inside(&HashSet::new(), &c));
    }

    #[test]
    fn test_squish_at_decrements() {
        // Kills: bound+pos in squish_at. fvs=[1,0], bound=2, Rel(3): free_idx=1, pos=0, -> Rel(2).
        let e = dummy(Expression::Rel(3));
        let result = squish_at(&[1, 0], 2, e);
        assert!(matches!(result.node, Expression::Rel(2)));
    }

    #[test]
    fn test_collect_free_vars_case() {
        use crate::core::Pattern;
        use crate::primitives::Prim;
        // Case with arm binding 1 var: body Rel(1) is free at top level 0.
        let body = dummy(Expression::Rel(1));
        let pat = dummy(Pattern::Var("x".into(), dummy(Constructor::Unit)));
        let case = dummy(Expression::Case(
            Box::new(dummy(Expression::Prim(Prim::Int(0)))),
            vec![(pat, body)],
            crate::core::CaseMeta {
                disc: dummy_con(),
                result: dummy_con(),
            },
        ));
        let fvs = free_vars(&case);
        assert_eq!(fvs, BTreeSet::from([0]));
    }

    #[test]
    fn test_calc_const_args_prim() {
        // Prim -> MAX_INT (never const).
        let e = dummy(Expression::Prim(crate::primitives::Prim::Int(42)));
        let enclosing = HashSet::new();
        let n = calc_const_args(&enclosing, &e);
        assert_eq!(n, usize::MAX);
    }

    #[test]
    fn test_calc_const_args_enclosing_named() {
        // Named in enclosing -> 0 const args.
        let e = dummy(Expression::Named(5));
        let enclosing = HashSet::from([5]);
        let n = calc_const_args(&enclosing, &e);
        assert_eq!(n, 0);
    }

    #[test]
    fn test_cmp_exp_node_prim_ordering() {
        use crate::primitives::Prim;
        use std::cmp::Ordering;
        let a = Expression::Prim(Prim::Int(0));
        let b = Expression::Prim(Prim::Int(1));
        assert_eq!(cmp_exp_node(&a, &b), Ordering::Less);
        assert_eq!(cmp_exp_node(&b, &a), Ordering::Greater);
        assert_eq!(cmp_exp_node(&a, &a), Ordering::Equal);
    }

    #[test]
    fn test_cmp_exp_node_rel_ordering() {
        use std::cmp::Ordering;
        assert_eq!(
            cmp_exp_node(&Expression::Rel(0), &Expression::Rel(1)),
            Ordering::Less
        );
        assert_eq!(
            cmp_exp_node(&Expression::Rel(2), &Expression::Rel(1)),
            Ordering::Greater
        );
    }

    #[test]
    fn test_cmp_exp_node_discriminant_order() {
        use std::cmp::Ordering;
        // Prim(0) < Rel(0) by disc.
        assert_eq!(
            cmp_exp_node(
                &Expression::Prim(crate::primitives::Prim::Int(0)),
                &Expression::Rel(0)
            ),
            Ordering::Less
        );
    }

    #[test]
    fn test_build_known_constructor_tfun() {
        // Constructor(id, TFun(...)) -> id in known.
        let tfun = dummy(Constructor::TFun(
            Box::new(dummy_con()),
            Box::new(dummy_con()),
        ));
        let file: File = vec![dummy(Declaration::Constructor(
            "F".into(),
            7,
            dummy(Kind::Type),
            tfun,
        ))];
        let known = build_known(&file);
        assert!(known.contains(&7));
    }

    #[test]
    fn test_build_known_datatype_tfun() {
        // Datatype with constructor type TFun -> id in known.
        let dt = crate::core::DatatypeDecl {
            name: "T".into(),
            id: 10,
            params: vec![],
            constrs: vec![(
                "C".into(),
                11,
                Some(dummy(Constructor::TFun(
                    Box::new(dummy_con()),
                    Box::new(dummy_con()),
                ))),
            )],
        };
        let file: File = vec![dummy(Declaration::Datatype(vec![dt]))];
        let known = build_known(&file);
        assert!(known.contains(&10));
    }

    #[test]
    fn test_sub_body_one_arg() {
        let inner = dummy(Expression::Named(99));
        let body = dummy(Expression::Abs(
            "x".into(),
            dummy_con(),
            dummy_con(),
            Box::new(inner),
        ));
        let typ = dummy(Constructor::TFun(
            Box::new(dummy_con()),
            Box::new(dummy_con()),
        ));
        let arg = dummy(Expression::Prim(crate::primitives::Prim::Int(42)));
        let result = sub_body(body, typ, &[arg]);
        assert!(result.is_some());
        let (new_body, _) = result.unwrap();
        assert!(matches!(new_body.node, Expression::Named(99)));
    }

    #[test]
    fn test_sub_body_empty_args() {
        let body = dummy(Expression::Rel(0));
        let typ = dummy_con();
        let result = sub_body(body, typ, &[]);
        assert!(result.is_some());
        let (b, _) = result.unwrap();
        assert!(matches!(b.node, Expression::Rel(0)));
    }

    #[test]
    fn test_find_split_tfun_function_dom() {
        // Domain is TFun -> function_inside true, so we collect the arg.
        let dom = dummy(Constructor::TFun(
            Box::new(dummy_con()),
            Box::new(dummy_con()),
        ));
        let typ = dummy(Constructor::TFun(Box::new(dom), Box::new(dummy_con())));
        let arg = dummy(Expression::Prim(crate::primitives::Prim::Int(1)));
        let known = HashSet::new();
        let (fxs, remaining, _fvs) = find_split(
            &typ,
            1,
            std::slice::from_ref(&arg),
            &known,
            vec![arg.clone()],
        );
        assert_eq!(fxs.len(), 1, "function domain should collect one arg");
        assert!(remaining.is_empty());
    }
}
