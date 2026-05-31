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

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::compiler_diagnostics::report_core_recovery;
use crate::core::dead_code_elimination::shake;
use crate::core::environment::pat_binds_n;
use crate::core::local_reduction::{reduce_con, reduce_with_errors};
use crate::core::unpoly::instantiate_cargs;
use crate::core::untangling::untangle;
use crate::core::utilities::constructor as con_util;
use crate::core::utilities::file as file_util;
use crate::core::utilities::kind as kind_util;
use crate::core::*;
use crate::diagnostics::{DiagnosticId, DiagnosticLocale, DiagnosticPayload};
use crate::error_types::{ErrorReporter, Located, Span};

// ---------------------------------------------------------------------------
// Lift / substitution helpers
// ---------------------------------------------------------------------------

/// Increment every `Expression::Rel(n)` where `n >= depth` by 1.
/// Used when wrapping a body in a new outer lambda.
fn lift_exp_in_exp(depth: usize, e: LocatedExpression) -> LocatedExpression {
    lift_exp_by(depth, 1, e)
}

fn lift_con_in_exp(e: LocatedExpression) -> LocatedExpression {
    crate::core::local_reduction::shift_exp(e, 0, 0, 0, 1)
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
            let rep2 = lift_con_in_exp(rep.clone());
            Located::new(
                Expression::CAbs(x, k, Box::new(sub_exp_in_exp(xn, &rep2, *b))),
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

struct AppSpine {
    function_id: usize,
    constructor_args: Vec<LocatedConstructor>,
    value_args: Vec<LocatedExpression>,
}

/// Unwrap a mixed application spine like `((f [T1]) [T2]) x1 x2` into
/// `Some((f, [T1, T2], [x1, x2]))`.
/// Returns `None` if the head is not `Named`, or if there are no value args.
fn get_app_inner(
    e: &LocatedExpression,
    constructor_args: &mut Vec<LocatedConstructor>,
    value_args: &mut Vec<LocatedExpression>,
) -> Option<usize> {
    match &e.node {
        Expression::Named(f) => Some(*f),
        Expression::App(f, a) => {
            let id = get_app_inner(f, constructor_args, value_args)?;
            value_args.push(*a.clone());
            Some(id)
        }
        Expression::CApp(f, c) => {
            let id = get_app_inner(f, constructor_args, value_args)?;
            constructor_args.push(c.clone());
            Some(id)
        }
        _ => None,
    }
}

fn get_app(e: &LocatedExpression) -> Option<AppSpine> {
    let mut constructor_args = vec![];
    let mut value_args = vec![];
    let function_id = get_app_inner(e, &mut constructor_args, &mut value_args)?;
    if value_args.is_empty() {
        return None;
    }
    Some(AppSpine {
        function_id,
        constructor_args,
        value_args,
    })
}

fn count_value_fun_args(typ: &LocatedConstructor) -> usize {
    let mut count = 0;
    let mut current = typ;
    while let Constructor::TFun(_, ran) = &current.node {
        count += 1;
        current = ran;
    }
    count
}

fn is_extraneous_erased_zero_witness_arg(arg: &LocatedExpression) -> bool {
    matches!(arg.node, Expression::Prim(Prim::Int(0)))
}

fn strip_extraneous_erased_zero_witness_args(
    typ: &LocatedConstructor,
    xs: Vec<LocatedExpression>,
) -> Vec<LocatedExpression> {
    let arity = count_value_fun_args(typ);
    if xs.len() <= arity {
        return xs;
    }

    let mut extras_to_drop = xs.len() - arity;
    let mut filtered = Vec::with_capacity(arity);
    for arg in xs {
        if extras_to_drop > 0 && is_extraneous_erased_zero_witness_arg(&arg) {
            extras_to_drop -= 1;
            continue;
        }
        filtered.push(arg);
    }
    filtered
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
                    Some(app) => {
                        if !enclosing.contains(&app.function_id) {
                            def()
                        } else {
                            visit_args(enclosing, depth, 0, &app.value_args)
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

fn cmp_datatype_kind(a: DatatypeKind, b: DatatypeKind) -> Ordering {
    fn disc(kind: DatatypeKind) -> u8 {
        match kind {
            DatatypeKind::Enum => 0,
            DatatypeKind::Option => 1,
            DatatypeKind::Default => 2,
        }
    }

    disc(a).cmp(&disc(b))
}

fn cmp_failure_mode(a: FailureMode, b: FailureMode) -> Ordering {
    fn disc(mode: FailureMode) -> u8 {
        match mode {
            FailureMode::Error => 0,
            FailureMode::None => 1,
        }
    }

    disc(a).cmp(&disc(b))
}

fn cmp_slice_by<T>(a: &[T], b: &[T], mut cmp: impl FnMut(&T, &T) -> Ordering) -> Ordering {
    a.len().cmp(&b.len()).then_with(|| {
        for (left, right) in a.iter().zip(b.iter()) {
            let ord = cmp(left, right);
            if ord != Ordering::Equal {
                return ord;
            }
        }
        Ordering::Equal
    })
}

fn cmp_option_by<T>(a: Option<&T>, b: Option<&T>, cmp: impl Fn(&T, &T) -> Ordering) -> Ordering {
    match (a, b) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Less,
        (Some(_), None) => Ordering::Greater,
        (Some(left), Some(right)) => cmp(left, right),
    }
}

fn cmp_pattern_constructor(a: &PatternConstructor, b: &PatternConstructor) -> Ordering {
    fn disc(pattern_constructor: &PatternConstructor) -> u8 {
        match pattern_constructor {
            PatternConstructor::Var(_) => 0,
            PatternConstructor::Ffi { .. } => 1,
        }
    }

    let da = disc(a);
    let db = disc(b);
    if da != db {
        return da.cmp(&db);
    }

    match (a, b) {
        (PatternConstructor::Var(x), PatternConstructor::Var(y)) => x.cmp(y),
        (
            PatternConstructor::Ffi {
                module: module_left,
                datatyp: datatype_left,
                params: params_left,
                con: con_left,
                arg: arg_left,
                kind: kind_left,
            },
            PatternConstructor::Ffi {
                module: module_right,
                datatyp: datatype_right,
                params: params_right,
                con: con_right,
                arg: arg_right,
                kind: kind_right,
            },
        ) => module_left
            .cmp(module_right)
            .then_with(|| datatype_left.cmp(datatype_right))
            .then_with(|| cmp_slice_by(params_left, params_right, |left, right| left.cmp(right)))
            .then_with(|| con_left.cmp(con_right))
            .then_with(|| cmp_option_by(arg_left.as_ref(), arg_right.as_ref(), con_util::compare))
            .then_with(|| cmp_datatype_kind(*kind_left, *kind_right)),
        _ => Ordering::Equal,
    }
}

fn cmp_pattern(a: &LocatedPattern, b: &LocatedPattern) -> Ordering {
    fn disc(pattern: &Pattern) -> u8 {
        match pattern {
            Pattern::Var(_, _) => 0,
            Pattern::Prim(_) => 1,
            Pattern::Constructor(_, _, _, _) => 2,
            Pattern::Record(_) => 3,
        }
    }

    let da = disc(&a.node);
    let db = disc(&b.node);
    if da != db {
        return da.cmp(&db);
    }

    match (&a.node, &b.node) {
        (Pattern::Var(name_left, ty_left), Pattern::Var(name_right, ty_right)) => name_left
            .cmp(name_right)
            .then_with(|| con_util::compare(ty_left, ty_right)),
        (Pattern::Prim(left), Pattern::Prim(right)) => left.cmp(right),
        (
            Pattern::Constructor(kind_left, pc_left, args_left, sub_left),
            Pattern::Constructor(kind_right, pc_right, args_right, sub_right),
        ) => cmp_datatype_kind(*kind_left, *kind_right)
            .then_with(|| cmp_pattern_constructor(pc_left, pc_right))
            .then_with(|| cmp_slice_by(args_left, args_right, con_util::compare))
            .then_with(|| cmp_option_by(sub_left.as_deref(), sub_right.as_deref(), cmp_pattern)),
        (Pattern::Record(fields_left), Pattern::Record(fields_right)) => {
            cmp_slice_by(fields_left, fields_right, |left, right| {
                left.0
                    .cmp(&right.0)
                    .then_with(|| cmp_pattern(&left.1, &right.1))
                    .then_with(|| con_util::compare(&left.2, &right.2))
            })
        }
        _ => Ordering::Equal,
    }
}

fn cmp_field_meta(a: &FieldMeta, b: &FieldMeta) -> Ordering {
    con_util::compare(&a.field, &b.field).then_with(|| con_util::compare(&a.rest, &b.rest))
}

fn cmp_rest_meta(a: &RestMeta, b: &RestMeta) -> Ordering {
    con_util::compare(&a.rest, &b.rest)
}

fn cmp_case_meta(a: &CaseMeta, b: &CaseMeta) -> Ordering {
    con_util::compare(&a.disc, &b.disc).then_with(|| con_util::compare(&a.result, &b.result))
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
        (Expression::Prim(pa), Expression::Prim(pb)) => pa.cmp(pb),
        (Expression::Rel(x), Expression::Rel(y)) => x.cmp(y),
        (Expression::Named(x), Expression::Named(y)) => x.cmp(y),
        (
            Expression::Constructor(kind_left, pc_left, args_left, arg_left),
            Expression::Constructor(kind_right, pc_right, args_right, arg_right),
        ) => cmp_datatype_kind(*kind_left, *kind_right)
            .then_with(|| cmp_pattern_constructor(pc_left, pc_right))
            .then_with(|| cmp_slice_by(args_left, args_right, con_util::compare))
            .then_with(|| cmp_option_by(arg_left.as_deref(), arg_right.as_deref(), cmp_exp)),
        (Expression::Ffi(m1, x1), Expression::Ffi(m2, x2)) => m1.cmp(m2).then_with(|| x1.cmp(x2)),
        (Expression::FfiApp(m1, x1, es1), Expression::FfiApp(m2, x2, es2)) => {
            m1.cmp(m2).then_with(|| x1.cmp(x2)).then_with(|| {
                cmp_slice_by(es1, es2, |left, right| {
                    cmp_exp(&left.0, &right.0).then_with(|| con_util::compare(&left.1, &right.1))
                })
            })
        }
        (Expression::App(f1, a1), Expression::App(f2, a2)) => {
            cmp_exp(f1, f2).then_with(|| cmp_exp(a1, a2))
        }
        (Expression::Abs(x1, t1, rt1, body1), Expression::Abs(x2, t2, rt2, body2)) => x1
            .cmp(x2)
            .then_with(|| con_util::compare(t1, t2))
            .then_with(|| con_util::compare(rt1, rt2))
            .then_with(|| cmp_exp(body1, body2)),
        (Expression::CApp(f1, c1), Expression::CApp(f2, c2)) => {
            cmp_exp(f1, f2).then_with(|| con_util::compare(c1, c2))
        }
        (Expression::CAbs(x1, k1, body1), Expression::CAbs(x2, k2, body2)) => x1
            .cmp(x2)
            .then_with(|| kind_util::compare(k1, k2))
            .then_with(|| cmp_exp(body1, body2)),
        (Expression::KAbs(x1, body1), Expression::KAbs(x2, body2)) => {
            x1.cmp(x2).then_with(|| cmp_exp(body1, body2))
        }
        (Expression::KApp(f1, k1), Expression::KApp(f2, k2)) => {
            cmp_exp(f1, f2).then_with(|| kind_util::compare(k1, k2))
        }
        (Expression::Record(fields1), Expression::Record(fields2)) => {
            cmp_slice_by(fields1, fields2, |left, right| {
                con_util::compare(&left.0, &right.0)
                    .then_with(|| cmp_exp(&left.1, &right.1))
                    .then_with(|| con_util::compare(&left.2, &right.2))
            })
        }
        (Expression::Field(e1, c1, meta1), Expression::Field(e2, c2, meta2)) => cmp_exp(e1, e2)
            .then_with(|| con_util::compare(c1, c2))
            .then_with(|| cmp_field_meta(meta1, meta2)),
        (Expression::Concat(e1a, c1a, e1b, c1b), Expression::Concat(e2a, c2a, e2b, c2b)) => {
            cmp_exp(e1a, e2a)
                .then_with(|| con_util::compare(c1a, c2a))
                .then_with(|| cmp_exp(e1b, e2b))
                .then_with(|| con_util::compare(c1b, c2b))
        }
        (Expression::Cut(e1, c1, meta1), Expression::Cut(e2, c2, meta2)) => cmp_exp(e1, e2)
            .then_with(|| con_util::compare(c1, c2))
            .then_with(|| cmp_field_meta(meta1, meta2)),
        (Expression::CutMulti(e1, c1, meta1), Expression::CutMulti(e2, c2, meta2)) => {
            cmp_exp(e1, e2)
                .then_with(|| con_util::compare(c1, c2))
                .then_with(|| cmp_rest_meta(meta1, meta2))
        }
        (Expression::Case(e1, arms1, meta1), Expression::Case(e2, arms2, meta2)) => cmp_exp(e1, e2)
            .then_with(|| {
                cmp_slice_by(arms1, arms2, |left, right| {
                    cmp_pattern(&left.0, &right.0).then_with(|| cmp_exp(&left.1, &right.1))
                })
            })
            .then_with(|| cmp_case_meta(meta1, meta2)),
        (Expression::Write(e1), Expression::Write(e2)) => cmp_exp(e1, e2),
        (Expression::Closure(f1, xs1), Expression::Closure(f2, xs2)) => {
            f1.cmp(f2).then_with(|| cmp_slice_by(xs1, xs2, cmp_exp))
        }
        (Expression::Let(x1, t1, e11, e12), Expression::Let(x2, t2, e21, e22)) => x1
            .cmp(x2)
            .then_with(|| con_util::compare(t1, t2))
            .then_with(|| cmp_exp(e11, e21))
            .then_with(|| cmp_exp(e12, e22)),
        (
            Expression::ServerCall(f1, xs1, t1, mode1),
            Expression::ServerCall(f2, xs2, t2, mode2),
        ) => f1
            .cmp(f2)
            .then_with(|| cmp_slice_by(xs1, xs2, cmp_exp))
            .then_with(|| con_util::compare(t1, t2))
            .then_with(|| cmp_failure_mode(*mode1, *mode2)),
        _ => Ordering::Equal,
    }
}

// ---------------------------------------------------------------------------
// Cache key
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct CacheKey {
    var_types: Vec<LocatedConstructor>,
    constructor_args: Vec<LocatedConstructor>,
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
                let k1 = self.constructor_args.len();
                let k2 = other.constructor_args.len();
                k1.cmp(&k2)
            })
            .then_with(|| {
                for (a, b) in self.constructor_args.iter().zip(&other.constructor_args) {
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

fn debug_especialize_fold_enabled() -> bool {
    std::env::var("URWEB_DEBUG_ESPECIALIZE_FOLD")
        .ok()
        .as_deref()
        == Some("1")
}

fn debug_especialize_args_enabled() -> bool {
    std::env::var("URWEB_DEBUG_ESPECIALIZE_ARGS")
        .ok()
        .as_deref()
        == Some("1")
}

fn debug_especialize_fold(name: &str, span: &Span, stage: &str, detail: impl FnOnce() -> String) {
    let in_top_fold = span.file.ends_with("/lib/ur/top.ur")
        && matches!(
            span.first.line,
            143 | 144
                | 145
                | 146
                | 147
                | 148
                | 149
                | 150
                | 151
                | 152
                | 153
                | 154
                | 155
                | 156
                | 157
                | 158
                | 159
                | 160
                | 161
                | 162
        );
    if !debug_especialize_fold_enabled() || !(matches!(name, "foldR" | "foldR2") || in_top_fold) {
        return;
    }
    eprintln!(
        "URWEB_DEBUG_ESPECIALIZE_FOLD {name} {stage} {}:{} {}",
        span.file,
        span.first.line,
        detail()
    );
}

fn debug_especialize_args(
    name: &str,
    span: &Span,
    stage: &str,
    typ: &LocatedConstructor,
    xs: &[LocatedExpression],
) {
    if !debug_especialize_args_enabled() {
        return;
    }
    if !(span.file.ends_with("/lib/ur/top.ur") || span.file.ends_with("/demo/crud.ur")) {
        return;
    }
    eprintln!(
        "URWEB_DEBUG_ESPECIALIZE_ARGS {name} {stage} {}:{} arity={} xs=[{}]",
        span.file,
        span.first.line,
        count_value_fun_args(typ),
        xs.iter()
            .map(|arg| format!("{:?}", arg.node))
            .collect::<Vec<_>>()
            .join(" | "),
    );
}

fn live_value_ids(file: &File) -> HashSet<usize> {
    let mut live = HashSet::new();
    for decl in file {
        match &decl.node {
            Declaration::Val(_, id, _, _, _)
            | Declaration::Sequence(_, id, _)
            | Declaration::View(_, id, _, _, _)
            | Declaration::Cookie(_, id, _, _)
            | Declaration::Style(_, id, _) => {
                live.insert(*id);
            }
            Declaration::ValRec(bindings) => {
                for (_, id, _, _, _) in bindings {
                    live.insert(*id);
                }
            }
            Declaration::Table { id, .. } => {
                live.insert(*id);
            }
            Declaration::Constructor(_, _, _, _)
            | Declaration::Datatype(_)
            | Declaration::Export(_, _, _)
            | Declaration::Index(_, _)
            | Declaration::Database(_)
            | Declaration::Task(_, _)
            | Declaration::Policy(_)
            | Declaration::OnError(_) => {}
        }
    }
    live
}

fn prune_specialization_state(
    file: &File,
    funcs: &mut HashMap<usize, FuncInfo>,
    specialized: &mut HashSet<usize>,
) {
    let live = live_value_ids(file);
    funcs.retain(|id, _| live.contains(id));
    for func in funcs.values_mut() {
        func.args
            .retain(|_, specialized_id| live.contains(specialized_id));
    }
    specialized.retain(|id| live.contains(id));
}

// ---------------------------------------------------------------------------
// build_known — set of Named type ids that contain function types
// ---------------------------------------------------------------------------

fn build_known(file: &File) -> HashSet<usize> {
    // Collect Named constructors that contain function types or already-known Named ids.
    // Fixed-point: iterate until stable (bounded to prevent runaway mutants).
    const MAX_BUILD_KNOWN_ITERATIONS: usize = 10_000;
    let mut known: HashSet<usize> = HashSet::new();
    for _ in 0..MAX_BUILD_KNOWN_ITERATIONS {
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
        if !changed {
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

fn refresh_abs_result_type_from_body(
    fallback: LocatedConstructor,
    body: &LocatedExpression,
) -> LocatedConstructor {
    match &body.node {
        Expression::Abs(_, dom, ran, _) => Located::new(
            Constructor::TFun(Box::new(dom.clone()), Box::new(ran.clone())),
            body.span.clone(),
        ),
        _ => fallback,
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
    errors: &mut Option<&mut ErrorReporter>,
) -> LocatedExpression {
    let detail_span = e.span.clone();
    let locale_fallback = errors
        .as_ref()
        .map(|reporter| reporter.diagnostic_locale)
        .unwrap_or(DiagnosticLocale::En);

    // Check if this is an application of a known specialized function.
    match get_app(&e) {
        Some(AppSpine {
            function_id: f,
            constructor_args,
            value_args: xs,
        }) if st.funcs.contains_key(&f) => {
            // Rewrite all args first.
            let xs: Vec<LocatedExpression> = xs
                .into_iter()
                .map(|x| rewrite_exp(env, x, known, st, errors))
                .collect();

            let constructor_args: Vec<LocatedConstructor> =
                constructor_args.into_iter().map(reduce_con).collect();

            let Some(fi) = st.funcs.get(&f).cloned() else {
                report_core_recovery(
                    errors,
                    detail_span,
                    DiagnosticPayload::new(
                        DiagnosticId::CoreEspecializeMissingSpecializationMetadata,
                        vec![format!("name_id={f}")],
                    ),
                    locale_fallback,
                );
                return rewrite_exp_default(env, e, known, st, errors);
            };
            let const_args = fi.const_args;
            let Some((typ, body)) =
                instantiate_cargs(fi.typ.clone(), fi.body.clone(), &constructor_args)
            else {
                return rewrite_exp_default(env, e, known, st, errors);
            };

            debug_especialize_args(&fi.name, &detail_span, "raw", &typ, &xs);
            let xs = strip_extraneous_erased_zero_witness_args(&typ, xs);
            debug_especialize_args(&fi.name, &detail_span, "filtered", &typ, &xs);
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
                return rewrite_exp_default(env, e, known, st, errors);
            }

            let key = CacheKey {
                var_types: vts.clone(),
                constructor_args: constructor_args.clone(),
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
            let name = fi.name.clone();
            let tag = fi.tag.clone();

            let sub_result = sub_body(body, typ, &fxs_prime);
            let Some((mut new_body, mut new_typ)) = sub_result else {
                return rewrite_exp_default(env, e, known, st, errors);
            };
            debug_especialize_fold(&name, &new_body.span, "sub_body", || {
                format!(
                    "f_prime={f_prime} fxs={:?} remaining={:?} body={:?} typ={:?}",
                    fxs_prime, remaining_xs, new_body.node, new_typ.node
                )
            });

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
            new_body = crate::core::local_reduction::reduce_exp_with_errors(new_body, errors);
            debug_especialize_fold(&name, &new_body.span, "reduced", || {
                format!(
                    "f_prime={f_prime} body={:?} typ={:?}",
                    new_body.node, new_typ.node
                )
            });

            // Recursively rewrite the new body.
            new_body = rewrite_exp(env, new_body, known, st, errors);
            debug_especialize_fold(&name, &new_body.span, "rewritten", || {
                format!(
                    "f_prime={f_prime} body={:?} typ={:?}",
                    new_body.node, new_typ.node
                )
            });

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
        _ => rewrite_exp_default(env, e, known, st, errors),
    }
}

/// The "default" rewrite: just recurse into sub-expressions.
fn rewrite_exp_default(
    env: &[(String, LocatedConstructor)],
    e: LocatedExpression,
    known: &HashSet<usize>,
    st: &mut State,
    errors: &mut Option<&mut ErrorReporter>,
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
            let arg = rewrite_exp(env, *arg, known, st, errors);
            Located::new(
                Expression::Constructor(dk, pc, cs, Some(Box::new(arg))),
                span,
            )
        }
        Expression::FfiApp(m, x, es) => {
            let es = es
                .into_iter()
                .map(|(e, t)| (rewrite_exp(env, e, known, st, errors), t))
                .collect();
            Located::new(Expression::FfiApp(m, x, es), span)
        }
        Expression::App(f, a) => {
            let f = rewrite_exp(env, *f, known, st, errors);
            let a = rewrite_exp(env, *a, known, st, errors);
            Located::new(Expression::App(Box::new(f), Box::new(a)), span)
        }
        Expression::Abs(x, t, rt, body) => {
            let mut new_env = vec![(x.clone(), t.clone())];
            new_env.extend_from_slice(env);
            let body = rewrite_exp(&new_env, *body, known, st, errors);
            let rt = refresh_abs_result_type_from_body(rt, &body);
            Located::new(Expression::Abs(x, t, rt, Box::new(body)), span)
        }
        Expression::CApp(f, c) => {
            let f = rewrite_exp(env, *f, known, st, errors);
            Located::new(Expression::CApp(Box::new(f), c), span)
        }
        Expression::CAbs(x, k, body) => {
            // CAbs doesn't bind an expression variable.
            let body = rewrite_exp(env, *body, known, st, errors);
            Located::new(Expression::CAbs(x, k, Box::new(body)), span)
        }
        Expression::KAbs(x, body) => {
            let body = rewrite_exp(env, *body, known, st, errors);
            Located::new(Expression::KAbs(x, Box::new(body)), span)
        }
        Expression::KApp(f, k) => {
            let f = rewrite_exp(env, *f, known, st, errors);
            Located::new(Expression::KApp(Box::new(f), k), span)
        }
        Expression::Record(fields) => {
            let fields = fields
                .into_iter()
                .map(|(c1, e, c2)| (c1, rewrite_exp(env, e, known, st, errors), c2))
                .collect();
            Located::new(Expression::Record(fields), span)
        }
        Expression::Field(e, c, meta) => {
            let e = rewrite_exp(env, *e, known, st, errors);
            Located::new(Expression::Field(Box::new(e), c, meta), span)
        }
        Expression::Concat(e1, c1, e2, c2) => {
            let e1 = rewrite_exp(env, *e1, known, st, errors);
            let e2 = rewrite_exp(env, *e2, known, st, errors);
            Located::new(Expression::Concat(Box::new(e1), c1, Box::new(e2), c2), span)
        }
        Expression::Cut(e, c, meta) => {
            let e = rewrite_exp(env, *e, known, st, errors);
            Located::new(Expression::Cut(Box::new(e), c, meta), span)
        }
        Expression::CutMulti(e, c, meta) => {
            let e = rewrite_exp(env, *e, known, st, errors);
            Located::new(Expression::CutMulti(Box::new(e), c, meta), span)
        }
        Expression::Case(e, arms, rt) => {
            let e = rewrite_exp(env, *e, known, st, errors);
            let arms = arms
                .into_iter()
                .map(|(p, body)| {
                    // Pattern binds go onto the front of env.
                    let pat_binds = crate::core::environment::pat_binds_list(&p);
                    let mut new_env: Vec<(String, LocatedConstructor)> =
                        pat_binds.into_iter().rev().collect();
                    new_env.extend_from_slice(env);
                    let body = rewrite_exp(&new_env, body, known, st, errors);
                    (p, body)
                })
                .collect();
            Located::new(Expression::Case(Box::new(e), arms, rt), span)
        }
        Expression::Write(e) => {
            let e = rewrite_exp(env, *e, known, st, errors);
            Located::new(Expression::Write(Box::new(e)), span)
        }
        Expression::Closure(n, es) => {
            let es = es
                .into_iter()
                .map(|e| rewrite_exp(env, e, known, st, errors))
                .collect();
            Located::new(Expression::Closure(n, es), span)
        }
        Expression::Let(x, t, e1, e2) => {
            let e1 = rewrite_exp(env, *e1, known, st, errors);
            let mut new_env = vec![(x.clone(), t.clone())];
            new_env.extend_from_slice(env);
            let e2 = rewrite_exp(&new_env, *e2, known, st, errors);
            Located::new(Expression::Let(x, t, Box::new(e1), Box::new(e2)), span)
        }
        Expression::ServerCall(n, es, t, fm) => {
            let es = es
                .into_iter()
                .map(|e| rewrite_exp(env, e, known, st, errors))
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
        FindSplitAcc {
            initial_part: true,
            fxs: vec![],
            fvs: BTreeSet::new(),
        },
    )
}

/// Accumulates specialized-prefix expressions and their free variables while [`find_split_rec`] walks a type spine.
struct FindSplitAcc {
    initial_part: bool,
    fxs: Vec<LocatedExpression>,
    fvs: BTreeSet<usize>,
}

fn find_split_rec(
    typ: &LocatedConstructor,
    const_args: usize,
    xs: &[LocatedExpression],
    known: &HashSet<usize>,
    old_xs: &[LocatedExpression],
    acc: FindSplitAcc,
) -> (
    Vec<LocatedExpression>,
    Vec<LocatedExpression>,
    BTreeSet<usize>,
) {
    // Default: stop here.
    let default = || {
        if acc.initial_part {
            (vec![], old_xs.to_vec(), BTreeSet::new())
        } else {
            (acc.fxs.clone(), xs.to_vec(), acc.fvs.clone())
        }
    };

    match (&typ.node, xs) {
        (Constructor::TFun(dom, ran), [e, rest @ ..]) if const_args > 0 => {
            let fi = function_inside(known, dom);
            if acc.initial_part || fi {
                let mut new_fvs = acc.fvs.clone();
                new_fvs.extend(free_vars(e));
                let mut new_fxs = acc.fxs;
                new_fxs.push(e.clone());
                let new_initial_part = !fi && acc.initial_part;
                find_split_rec(
                    ran,
                    const_args - 1,
                    rest,
                    known,
                    old_xs,
                    FindSplitAcc {
                        initial_part: new_initial_part,
                        fxs: new_fxs,
                        fvs: new_fvs,
                    },
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
    errors: &mut Option<&mut ErrorReporter>,
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
                    let e2 = rewrite_exp(&[], e, &known, &mut st, errors);
                    Located::new(Declaration::Val(x, n, t, e2, s), span.clone())
                }
                Declaration::ValRec(vis) => {
                    let vis2 = vis
                        .into_iter()
                        .map(|(x, n, t, e, s)| {
                            let e2 = rewrite_exp(&[], e, &known, &mut st, errors);
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
                    let exp_b = rewrite_exp(&[], exp, &known, &mut st, errors);
                    let pk_exp_b = rewrite_exp(&[], pk_exp, &known, &mut st, errors);
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
                    let eb = rewrite_exp(&[], e, &known, &mut st, errors);
                    Located::new(Declaration::View(x, n, s, eb, t), span.clone())
                }
                Declaration::Task(e1, e2) => {
                    let e1b = rewrite_exp(&[], e1, &known, &mut st, errors);
                    let e2b = rewrite_exp(&[], e2, &known, &mut st, errors);
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
    errors: &mut Option<&mut ErrorReporter>,
) -> File {
    if iterations >= MAX_ESPECIALIZE_ITERATIONS {
        return file;
    }
    let file = reduce_with_errors(file, errors);
    let (changed, file, funcs, specialized) = specialize_pass(funcs, specialized, file, errors);
    if changed {
        let file = untangle(file);
        let file = shake(file);
        let mut funcs = funcs;
        let mut specialized = specialized;
        prune_specialization_state(&file, &mut funcs, &mut specialized);
        especialize_loop(funcs, specialized, file, iterations + 1, errors)
    } else {
        file
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Run the expression specialization pass to a fixed point.
pub fn especialize(file: File) -> File {
    let mut no_errors = None;
    especialize_with_reporter(file, &mut no_errors)
}

/// Like [`especialize`] but records recoverable internal diagnostics on `errors` when provided.
pub fn especialize_with_reporter(file: File, errors: &mut Option<&mut ErrorReporter>) -> File {
    especialize_loop(HashMap::new(), HashSet::new(), file, 0, errors)
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

    fn dummy_con() -> LocatedConstructor {
        dummy(Constructor::Unit)
    }

    fn ffi_con(name: &str) -> LocatedConstructor {
        dummy(Constructor::Ffi("Basis".into(), name.into()))
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
        // Unwrap the get_app result; panic with a message if it is None.
        let app = match result {
            Some(v) => v,
            None => panic!("get_app returned None unexpectedly"),
        };
        assert_eq!(app.function_id, 1);
        assert_eq!(app.value_args.len(), 1);
        assert!(app.constructor_args.is_empty());
    }

    /// get_app returns None for bare Named (no args).
    #[test]
    fn test_get_app_no_args() {
        let e = dummy(Expression::Named(1));
        assert!(get_app(&e).is_none());
    }

    #[test]
    fn test_get_app_preserves_value_application_order() {
        let x = dummy(Expression::Named(10));
        let y = dummy(Expression::Named(20));
        let e = dummy(Expression::App(
            Box::new(dummy(Expression::App(
                Box::new(dummy(Expression::Named(1))),
                Box::new(x),
            ))),
            Box::new(y),
        ));

        let app = get_app(&e).expect("expected application spine");
        assert_eq!(app.function_id, 1);
        assert_eq!(app.value_args.len(), 2);
        assert!(matches!(app.value_args[0].node, Expression::Named(10)));
        assert!(matches!(app.value_args[1].node, Expression::Named(20)));
    }

    #[test]
    fn test_get_app_collects_constructor_args_before_value_args() {
        let t1 = dummy(Constructor::Named(11));
        let t2 = dummy(Constructor::Named(22));
        let arg = dummy(Expression::Named(33));
        let e = dummy(Expression::App(
            Box::new(dummy(Expression::CApp(
                Box::new(dummy(Expression::CApp(
                    Box::new(dummy(Expression::Named(1))),
                    t1,
                ))),
                t2,
            ))),
            Box::new(arg),
        ));

        let app = get_app(&e).expect("expected mixed application spine");
        assert_eq!(app.function_id, 1);
        assert_eq!(app.constructor_args.len(), 2);
        assert!(matches!(
            app.constructor_args[0].node,
            Constructor::Named(11)
        ));
        assert!(matches!(
            app.constructor_args[1].node,
            Constructor::Named(22)
        ));
        assert_eq!(app.value_args.len(), 1);
        assert!(matches!(app.value_args[0].node, Expression::Named(33)));
    }

    #[test]
    fn strip_extraneous_erased_zero_witness_args_drops_leading_zero() {
        let typ = dummy(Constructor::TFun(
            Box::new(ffi_con("int")),
            Box::new(dummy(Constructor::TFun(
                Box::new(ffi_con("string")),
                Box::new(dummy_con()),
            ))),
        ));
        let xs = vec![
            dummy(Expression::Prim(crate::primitives::Prim::Int(0))),
            dummy(Expression::Named(10)),
            dummy(Expression::Named(20)),
        ];

        let filtered = strip_extraneous_erased_zero_witness_args(&typ, xs);
        assert_eq!(filtered.len(), 2);
        assert!(matches!(filtered[0].node, Expression::Named(10)));
        assert!(matches!(filtered[1].node, Expression::Named(20)));
    }

    #[test]
    fn strip_extraneous_erased_zero_witness_args_keeps_runtime_zero_when_arity_matches() {
        let typ = dummy(Constructor::TFun(
            Box::new(ffi_con("int")),
            Box::new(dummy_con()),
        ));
        let xs = vec![dummy(Expression::Prim(crate::primitives::Prim::Int(0)))];

        let filtered = strip_extraneous_erased_zero_witness_args(&typ, xs);
        assert_eq!(filtered.len(), 1);
        assert!(matches!(
            filtered[0].node,
            Expression::Prim(crate::primitives::Prim::Int(0))
        ));
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
    fn test_sub_exp_lifts_constructor_refs_under_cabs() {
        let meta = FieldMeta {
            field: dummy_con(),
            rest: dummy_con(),
        };
        let rep = dummy(Expression::Field(
            Box::new(dummy(Expression::Rel(0))),
            dummy(Constructor::Rel(0)),
            meta,
        ));
        let body = dummy(Expression::CAbs(
            "nm".into(),
            Box::new(dummy(Kind::Name)),
            Box::new(dummy(Expression::Rel(0))),
        ));

        let result = sub_exp_in_exp(0, &rep, body);
        let Expression::CAbs(_, _, inner) = result.node else {
            panic!("expected CAbs")
        };
        let Expression::Field(_, field_c, _) = inner.node else {
            panic!("expected field projection")
        };
        assert!(
            matches!(field_c.node, Constructor::Rel(1)),
            "constructor references in the substituted expression must lift under CAbs"
        );
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
    fn test_cmp_exp_node_distinguishes_distinct_abs_bodies() {
        use std::cmp::Ordering;

        let left = Expression::Abs(
            "x".into(),
            dummy_con(),
            dummy_con(),
            Box::new(dummy(Expression::Rel(0))),
        );
        let right = Expression::Abs(
            "x".into(),
            dummy_con(),
            dummy_con(),
            Box::new(dummy(Expression::Rel(1))),
        );

        assert_ne!(cmp_exp_node(&left, &right), Ordering::Equal);
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
        // Unwrap sub_body result; panic with a message if it is None.
        let (new_body, _) = match result {
            Some(v) => v,
            None => panic!("sub_body returned None unexpectedly"),
        };
        assert!(matches!(new_body.node, Expression::Named(99)));
    }

    #[test]
    fn test_sub_body_empty_args() {
        let body = dummy(Expression::Rel(0));
        let typ = dummy_con();
        let result = sub_body(body, typ, &[]);
        assert!(result.is_some());
        // Unwrap sub_body result for empty args; panic with a message if it is None.
        let (b, _) = match result {
            Some(v) => v,
            None => panic!("sub_body with empty args returned None unexpectedly"),
        };
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

    #[test]
    fn rewrite_exp_default_refreshes_abs_result_type_from_rewritten_body() {
        let int_t = ffi_con("int");
        let string_t = ffi_con("string");
        let unit_t = dummy_con();
        let inner = dummy(Expression::Abs(
            "line".into(),
            string_t.clone(),
            unit_t.clone(),
            Box::new(dummy(Expression::Named(1))),
        ));
        let stale_ran = dummy(Constructor::TFun(
            Box::new(int_t.clone()),
            Box::new(dummy(Constructor::TFun(
                Box::new(string_t.clone()),
                Box::new(unit_t.clone()),
            ))),
        ));
        let outer = dummy(Expression::Abs(
            "id".into(),
            int_t,
            stale_ran,
            Box::new(inner),
        ));

        let known = HashSet::new();
        let mut st = State {
            max_name: 0,
            funcs: HashMap::from([(
                1,
                FuncInfo {
                    name: "unit".into(),
                    args: BTreeMap::new(),
                    body: dummy(Expression::Record(vec![])),
                    typ: unit_t.clone(),
                    tag: String::new(),
                    const_args: 0,
                },
            )]),
            decls: vec![],
            specialized: HashSet::new(),
        };
        let mut errors = None;
        let rewritten = rewrite_exp_default(&[], outer, &known, &mut st, &mut errors);

        let Expression::Abs(_, _, ran, _) = rewritten.node else {
            panic!("expected outer lambda");
        };
        let Constructor::TFun(dom, body_ran) = ran.node else {
            panic!("expected repaired function result type");
        };
        assert!(
            matches!(&dom.node, Constructor::Ffi(module, name) if module == "Basis" && name == "string")
        );
        assert!(matches!(body_ran.node, Constructor::Unit));
    }
}
