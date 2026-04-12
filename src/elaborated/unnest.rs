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
        Constructor::Tuple(cs) => {
            Constructor::Tuple(cs.into_iter().map(|c2| lift_c(by, bound, c2)).collect())
        }
        Constructor::Proj(c2, n) => Constructor::Proj(Box::new(lift_c(by, bound, *c2)), n),
        other => other,
    };
    Located::new(node, span)
}

/// Shift all `Expression::Rel(n >= bound)` by `by` in an expression.
fn lift_e(by: i64, bound: usize, e: LocatedExpression) -> LocatedExpression {
    let span = e.span.clone();
    let node = match e.node {
        Expression::Rel(n) if n >= bound => Expression::Rel((n as i64 + by) as usize),
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
///
/// This deliberately matches the local `subExpInExp` in `unnest.sml`, not the
/// general environment substitution helpers: we replace the chosen variable
/// but do not shift larger `ERel`s down here. The later `do_subst` pass
/// performs the explicit un-shift after all substitutions are in place.
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
            Expression::CAbs(expl, name, k, Box::new(sub_e_bound(xn, depth, rep, *body)))
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

fn pattern_bindings_acc(p: &LocatedPattern, out: &mut Vec<(String, LocatedConstructor)>) {
    match &p.node {
        Pattern::Var(name, typ) => out.push((name.clone(), typ.clone())),
        Pattern::Prim(_) => {}
        Pattern::Constructor(_, _, _, inner) => {
            if let Some(inner) = inner {
                pattern_bindings_acc(inner, out);
            }
        }
        Pattern::Record(fields) => {
            for (_, p, _) in fields {
                pattern_bindings_acc(p, out);
            }
        }
    }
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
            fvs_kind_acc(kbound, a, out);
            fvs_kind_acc(kbound, b, out);
        }
        Kind::Record(k2) => fvs_kind_acc(kbound, k2, out),
        Kind::Tuple(ks) => ks.iter().for_each(|k2| fvs_kind_acc(kbound, k2, out)),
        Kind::Fun(_, body) => fvs_kind_acc(kbound + 1, body, out),
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
        Constructor::KAbs(_, body) => fvs_con_acc(kb, cb, body, kvs, cvs),
        Constructor::KApp(f, k) => {
            fvs_con_acc(kb, cb, f, kvs, cvs);
            fvs_kind_acc(kb, k, kvs);
        }
        Constructor::TKFun(_, body) => fvs_con_acc(kb, cb, body, kvs, cvs),
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
        Constructor::Tuple(cs) => cs.iter().for_each(|c2| fvs_con_acc(kb, cb, c2, kvs, cvs)),
        Constructor::Proj(c2, _) => fvs_con_acc(kb, cb, c2, kvs, cvs),
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
    span: &crate::error_types::Span,
    errors: &mut ErrorReporter,
) -> usize {
    list.iter().position(|&v| v == x).unwrap_or_else(|| {
        if std::env::var("URWEB_DEBUG_UNNEST").ok().as_deref() == Some("1") {
            eprintln!(
                "unnest remap miss span={}:{} x={} list={:?}",
                span.file, span.first.line, x, list
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
    _kb: usize,
    cb: usize,
    _kfv: &[usize],
    cfv: &[usize],
    c: LocatedConstructor,
    errors: &mut ErrorReporter,
) -> LocatedConstructor {
    let span = c.span.clone();
    let node = match c.node {
        Constructor::Rel(n) if n >= cb => {
            Constructor::Rel(position_of(n - cb, cfv, &span, errors) + cb)
        }
        Constructor::TFun(a, b) => Constructor::TFun(
            Box::new(squish_c_bound(_kb, cb, _kfv, cfv, *a, errors)),
            Box::new(squish_c_bound(_kb, cb, _kfv, cfv, *b, errors)),
        ),
        Constructor::TCFun(expl, name, k, body) => Constructor::TCFun(
            expl,
            name,
            k,
            Box::new(squish_c_bound(_kb, cb + 1, _kfv, cfv, *body, errors)),
        ),
        Constructor::TRecord(c2) => {
            Constructor::TRecord(Box::new(squish_c_bound(_kb, cb, _kfv, cfv, *c2, errors)))
        }
        Constructor::TDisjoint(a, b, c2) => Constructor::TDisjoint(
            Box::new(squish_c_bound(_kb, cb, _kfv, cfv, *a, errors)),
            Box::new(squish_c_bound(_kb, cb, _kfv, cfv, *b, errors)),
            Box::new(squish_c_bound(_kb, cb, _kfv, cfv, *c2, errors)),
        ),
        Constructor::App(f, x) => Constructor::App(
            Box::new(squish_c_bound(_kb, cb, _kfv, cfv, *f, errors)),
            Box::new(squish_c_bound(_kb, cb, _kfv, cfv, *x, errors)),
        ),
        Constructor::Abs(name, k, body) => Constructor::Abs(
            name,
            k,
            Box::new(squish_c_bound(_kb, cb + 1, _kfv, cfv, *body, errors)),
        ),
        Constructor::KAbs(name, body) => Constructor::KAbs(
            name,
            Box::new(squish_c_bound(_kb, cb, _kfv, cfv, *body, errors)),
        ),
        Constructor::KApp(f, k) => {
            Constructor::KApp(Box::new(squish_c_bound(_kb, cb, _kfv, cfv, *f, errors)), k)
        }
        Constructor::TKFun(name, body) => Constructor::TKFun(
            name,
            Box::new(squish_c_bound(_kb, cb, _kfv, cfv, *body, errors)),
        ),
        Constructor::Record(k, fields) => Constructor::Record(
            k,
            fields
                .into_iter()
                .map(|(n, v)| {
                    (
                        squish_c_bound(_kb, cb, _kfv, cfv, n, errors),
                        squish_c_bound(_kb, cb, _kfv, cfv, v, errors),
                    )
                })
                .collect(),
        ),
        Constructor::Concat(a, b) => Constructor::Concat(
            Box::new(squish_c_bound(_kb, cb, _kfv, cfv, *a, errors)),
            Box::new(squish_c_bound(_kb, cb, _kfv, cfv, *b, errors)),
        ),
        Constructor::Tuple(cs) => Constructor::Tuple(
            cs.into_iter()
                .map(|c2| squish_c_bound(_kb, cb, _kfv, cfv, c2, errors))
                .collect(),
        ),
        Constructor::Proj(c2, n) => {
            Constructor::Proj(Box::new(squish_c_bound(_kb, cb, _kfv, cfv, *c2, errors)), n)
        }
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
    squish_e_bound(nr, 0, 0, nr, kfv, cfv, efv, e, errors)
}

fn squish_e_bound(
    nr: usize,
    kb: usize,
    cb: usize,
    eb: usize,
    kfv: &[usize],
    cfv: &[usize],
    efv: &[usize],
    e: LocatedExpression,
    errors: &mut ErrorReporter,
) -> LocatedExpression {
    let span = e.span.clone();
    let node = match e.node {
        Expression::Rel(n) if n >= eb => {
            // Match SML `squishExp`: keep the surrounding binder depth (`eb - nr`)
            // when remapping a free variable into the captured environment.
            Expression::Rel(position_of(n - eb, efv, &span, errors) + eb - nr)
        }
        Expression::App(f, x) => Expression::App(
            Box::new(squish_e_bound(nr, kb, cb, eb, kfv, cfv, efv, *f, errors)),
            Box::new(squish_e_bound(nr, kb, cb, eb, kfv, cfv, efv, *x, errors)),
        ),
        Expression::Abs(name, dom, ran, body) => Expression::Abs(
            name,
            squish_c_bound(kb, cb, kfv, cfv, dom, errors),
            squish_c_bound(kb, cb, kfv, cfv, ran, errors),
            Box::new(squish_e_bound(
                nr,
                kb,
                cb,
                eb + 1,
                kfv,
                cfv,
                efv,
                *body,
                errors,
            )),
        ),
        Expression::CApp(f, c) => Expression::CApp(
            Box::new(squish_e_bound(nr, kb, cb, eb, kfv, cfv, efv, *f, errors)),
            squish_c_bound(kb, cb, kfv, cfv, c, errors),
        ),
        Expression::CAbs(expl, name, k, body) => Expression::CAbs(
            expl,
            name,
            k,
            Box::new(squish_e_bound(
                nr,
                kb,
                cb + 1,
                eb,
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
                nr,
                kb + 1,
                cb,
                eb,
                kfv,
                cfv,
                efv,
                *body,
                errors,
            )),
        ),
        Expression::KApp(f, k) => Expression::KApp(
            Box::new(squish_e_bound(nr, kb, cb, eb, kfv, cfv, efv, *f, errors)),
            k,
        ),
        Expression::Record(fields) => Expression::Record(
            fields
                .into_iter()
                .map(|(n, v, t)| {
                    (
                        n,
                        squish_e_bound(nr, kb, cb, eb, kfv, cfv, efv, v, errors),
                        t,
                    )
                })
                .collect(),
        ),
        Expression::Field(e2, c, meta) => Expression::Field(
            Box::new(squish_e_bound(nr, kb, cb, eb, kfv, cfv, efv, *e2, errors)),
            c,
            meta,
        ),
        Expression::Concat(a, c1, b, c2) => Expression::Concat(
            Box::new(squish_e_bound(nr, kb, cb, eb, kfv, cfv, efv, *a, errors)),
            c1,
            Box::new(squish_e_bound(nr, kb, cb, eb, kfv, cfv, efv, *b, errors)),
            c2,
        ),
        Expression::Cut(e2, c, meta) => Expression::Cut(
            Box::new(squish_e_bound(nr, kb, cb, eb, kfv, cfv, efv, *e2, errors)),
            c,
            meta,
        ),
        Expression::CutMulti(e2, c, meta) => Expression::CutMulti(
            Box::new(squish_e_bound(nr, kb, cb, eb, kfv, cfv, efv, *e2, errors)),
            c,
            meta,
        ),
        Expression::Case(disc, arms, meta) => Expression::Case(
            Box::new(squish_e_bound(nr, kb, cb, eb, kfv, cfv, efv, *disc, errors)),
            arms.into_iter()
                .map(|(p, arm)| {
                    let d = pat_bind_depth(&p);
                    (
                        p,
                        squish_e_bound(nr, kb, cb, eb + d, kfv, cfv, efv, arm, errors),
                    )
                })
                .collect(),
            meta,
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
                            let e2s = squish_e_bound(nr, kb, cb, cur_eb, kfv, cfv, efv, e2, errors);
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
                                            nr,
                                            kb,
                                            cb,
                                            cur_eb + nr2,
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
                    nr, kb, cb, cur_eb, kfv, cfv, efv, *body, errors,
                )),
                t,
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
    // Match the SML `foldr`: apply outermost binders first.
    for &kx in kfv.iter().rev() {
        e = Located::new(
            Expression::KApp(
                Box::new(e),
                Box::new(Located::new(Kind::Rel(kx), loc.clone())),
            ),
            loc.clone(),
        );
    }
    // Apply con args
    for &cx in cfv.iter().rev() {
        e = Located::new(
            Expression::CApp(Box::new(e), Located::new(Constructor::Rel(cx), loc.clone())),
            loc.clone(),
        );
    }
    // Apply exp args: ERel(nr + x) — shifted past the recursive bindings
    for &ex in efv.iter().rev() {
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
    fn push_e_n(&mut self, n: usize) {
        for _ in 0..n {
            self.exps
                .insert(0, ("_".into(), Located::dummy(Constructor::Error)));
        }
    }
    fn push_pattern_bindings(&mut self, p: &LocatedPattern) {
        let mut bindings = Vec::new();
        pattern_bindings_acc(p, &mut bindings);
        for (name, typ) in bindings {
            self.push_e(name, typ);
        }
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
                let let_base = self.exps.len();

                // Match the SML foldMapB traversal order: recursively transform nested
                // bodies first, with the original let-bound context in scope, before
                // this let decides which immediate bindings to hoist.
                let mut eds_pre: Vec<LocatedElaboratedDeclaration> = Vec::new();
                for de in eds {
                    let de_span = de.span.clone();
                    match de.node {
                        ElaboratedDeclaration::Val(p, ty, e2) => {
                            let e2u = self.exp(e2);
                            eds_pre.push(Located::new(
                                ElaboratedDeclaration::Val(p.clone(), ty, e2u),
                                de_span,
                            ));
                            self.push_pattern_bindings(&p);
                        }
                        ElaboratedDeclaration::ValRec(vis) => {
                            for (x, ty, _) in &vis {
                                self.push_e(x.clone(), ty.clone());
                            }
                            let vis2 = vis
                                .into_iter()
                                .map(|(x, ty, e2)| (x, ty, self.exp(e2)))
                                .collect();
                            eds_pre
                                .push(Located::new(ElaboratedDeclaration::ValRec(vis2), de_span));
                        }
                    }
                }
                let body_pre = self.exp(*body);
                self.exps.truncate(let_base);

                // Convert EDVal(PVar, fn-type, e) → EDValRec.
                let eds: Vec<_> = eds_pre
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

                // Process each decl after nested bodies have already been transformed.
                let mut remaining: Vec<LocatedElaboratedDeclaration> = Vec::new();
                let mut subs: Vec<(usize, LocatedExpression)> = Vec::new();
                let mut by: usize = 0; // total bindings hoisted (removed from Let)

                for de in eds {
                    let de_span = de.span.clone();
                    match de.node {
                        ElaboratedDeclaration::Val(p, ty, e2) => {
                            // Apply pending subs, then keep the transformed binding.
                            let e2a = self.do_subst(e2, &subs, by);
                            let d = pat_bind_depth(&p);
                            self.push_pattern_bindings(&p);
                            remaining.push(Located::new(
                                ElaboratedDeclaration::Val(p, ty.clone(), e2a),
                                de_span,
                            ));
                            // Update subs: each existing sub shifts by d.
                            subs = subs
                                .into_iter()
                                .map(|(xn, rep)| (xn + d, lift_e(d as i64, 0, rep)))
                                .collect();
                        }
                        ElaboratedDeclaration::ValRec(vis) => {
                            let nr = vis.len();
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
                            let vis_binders: Vec<_> = vis
                                .iter()
                                .map(|(x, ty, _)| (x.clone(), ty.clone()))
                                .collect();

                            // Compute free vars and hoist.
                            let (new_subs, _nr2) = self.hoist_valrec_inner(vis, &de_span);

                            // The new subs replace ERel(0..nr-1) with Named apps.
                            // Merge with existing subs (shift existing by nr, then add new).
                            let shifted_subs: Vec<_> = subs
                                .into_iter()
                                .map(|(xn, rep)| (xn + nr, lift_e(nr as i64, 0, rep)))
                                .collect();
                            subs = new_subs.into_iter().chain(shifted_subs).collect();
                            by += nr;
                            for (x, ty) in vis_binders {
                                self.push_e(x, ty);
                            }
                            // No push to remaining (hoisted).
                        }
                    }
                }

                // Apply remaining subs to body.
                let body3 = self.do_subst(body_pre, &subs, by);
                self.exps.truncate(let_base);

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
                        let d = pat_bind_depth(&p);
                        self.push_e_n(d);
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
    ) -> (Vec<(usize, LocatedExpression)>, usize) {
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

        if std::env::var("URWEB_DEBUG_UNNEST").ok().as_deref() == Some("1") {
            let exp_names: Vec<String> = self
                .exps
                .iter()
                .enumerate()
                .map(|(i, (name, _))| format!("{i}:{name}"))
                .collect();
            eprintln!(
                "unnest hoist span={}:{} nr={} efv={:?} exps=[{}]",
                loc.file,
                loc.first.line,
                nr,
                efv,
                exp_names.join(", ")
            );
            for (name, _, body) in &vis {
                eprintln!(
                    "unnest hoist body {} = {}",
                    name,
                    crate::elaborated::type_display::format_expression(body)
                );
                eprintln!("unnest hoist body-debug {} = {:?}", name, body);
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
        for (i, (x, ty, body)) in vis.into_iter().enumerate() {
            let id = ids[i];

            // Apply subs' to body.
            let body = apply_subs(&subs, body);

            // Squish.
            let ty_s = squish_c(&kfv, &cfv, ty, self.errors);
            let body_s = squish_e(nr, &kfv, &cfv, &efv, body, self.errors);

            // Wrap with exp lambdas (innermost efv first, i.e. reverse).
            let (mut we, mut wt) = (body_s, ty_s);
            for &ex in &efv {
                let (aname, atype) = self
                    .exps
                    .get(ex)
                    .map(|(n, t)| (n.clone(), squish_c(&kfv, &cfv, t.clone(), self.errors)))
                    .unwrap_or_else(|| ("_".into(), Located::dummy(Constructor::Error)));
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
            for &cx in &cfv {
                let (cname, ckind) = self
                    .cons
                    .get(cx)
                    .map(|(n, k)| (n.clone(), k.clone()))
                    .unwrap_or_else(|| ("_".into(), Located::dummy(Kind::Type)));
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
            for &kx in &kfv {
                let kname = self.knames.get(kx).cloned().unwrap_or_else(|| "_".into());
                we = Located::new(Exp::KAbs(kname.clone(), Box::new(we)), loc.clone());
                wt = Located::new(Constructor::TKFun(kname, Box::new(wt)), loc.clone());
            }

            self.hoisted.push(("$".to_string() + &x, id, wt, we));
        }

        (subs, nr)
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
                let vis2: Vec<_> = vis
                    .into_iter()
                    .map(|(x, n, t, e)| {
                        let e2 = self.exp(e);
                        (x, n, t, e2)
                    })
                    .collect();
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

    fn dummy_exp() -> LocatedExpression {
        Located::dummy(Expression::Prim(crate::primitives::Prim::Int(0)))
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
}
