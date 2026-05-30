//! Utility traversals over the Mono AST.
//!
//! Ports `mono_util.sml`.
//!
//! Also provides the **Level 3 bridge**: functions that convert [`crate::primitives::Prim`]
//! literals into [`crate::elaborated::types::TypedValue`] / [`crate::elaborated::types::ScalarValue`]
//! for type-aware constant folding and analysis.

use crate::datatype_kind::DatatypeKind;
use crate::elaborated::types::{ScalarTypeTag, ScalarValue, TypeHierarchy, TypedValue, Values};
use crate::monomorphized::{
    CaseMeta, Decl, Exp, JavaScriptMode, LocDecl, LocExp, LocPat, LocTyp, Pat, Policy, QueryMeta,
    Typ,
};
use crate::primitives::{Prim, StringMode};

// ---------------------------------------------------------------------------
// Helper: sort record fields alphabetically (mirrors `sortFields` in SML)
// ---------------------------------------------------------------------------

/// Sort `fields` in-place by field name, ascending.
pub fn sort_fields<T>(fields: &mut [(String, T)]) {
    fields.sort_by(|(a, _), (b, _)| a.cmp(b));
}

// ---------------------------------------------------------------------------
// classify_datatype — same logic as core::utilities::classify_datatype
// ---------------------------------------------------------------------------

fn typ_mentions_datatype_id(t: &LocTyp, datatype_id: usize) -> bool {
    match &t.node {
        Typ::Fun(dom, ran) => {
            typ_mentions_datatype_id(dom, datatype_id) || typ_mentions_datatype_id(ran, datatype_id)
        }
        Typ::Record(fields) => fields
            .iter()
            .any(|(_, field_t)| typ_mentions_datatype_id(field_t, datatype_id)),
        Typ::Datatype(id, _) => *id == datatype_id,
        Typ::Ffi(..) | Typ::Source => false,
        Typ::Option(inner) | Typ::List(inner) | Typ::Signal(inner) | Typ::Transaction(inner) => {
            typ_mentions_datatype_id(inner, datatype_id)
        }
    }
}

/// Classify a Mono datatype's representation kind from its constructor list.
pub fn classify_datatype(
    datatype_id: usize,
    constrs: &[(String, usize, Option<LocTyp>)],
) -> DatatypeKind {
    let mut nullary = 0usize;
    let mut unary = 0usize;
    for (_, _, arg) in constrs {
        if arg.is_none() {
            nullary += 1;
        } else {
            unary += 1;
        }
    }
    if unary == 0 {
        DatatypeKind::Enum
    } else if nullary == 1
        && unary == 1
        && !constrs
            .iter()
            .filter_map(|(_, _, arg)| arg.as_ref())
            .any(|arg| typ_mentions_datatype_id(arg, datatype_id))
    {
        DatatypeKind::Option
    } else {
        DatatypeKind::Default
    }
}

// ---------------------------------------------------------------------------
// pub mod typ
// ---------------------------------------------------------------------------

pub mod typ {
    use super::*;
    use std::cmp::Ordering;

    // -----------------------------------------------------------------------
    // compare — total ordering on Typ (for use in BTreeMap keys)
    // -----------------------------------------------------------------------

    /// Assign a numeric tag for variant ordering (same order as the enum
    /// definition in `mono/mod.rs`).
    fn tag(type_node: &Typ) -> u8 {
        match type_node {
            Typ::Fun(..) => 0,
            Typ::Record(..) => 1,
            Typ::Datatype(..) => 2,
            Typ::Ffi(..) => 3,
            Typ::Option(..) => 4,
            Typ::List(..) => 5,
            Typ::Source => 6,
            Typ::Signal(..) => 7,
            Typ::Transaction(..) => 8, // Transaction has the highest tag for ordering stability
        }
    }

    /// Total ordering on `LocTyp`, following the SML `compare` with
    /// `Order.join` chaining.
    pub fn compare(t1: &LocTyp, t2: &LocTyp) -> Ordering {
        compare_typ(&t1.node, &t2.node)
    }

    fn compare_typ(left: &Typ, right: &Typ) -> Ordering {
        match (left, right) {
            (Typ::Fun(d1, r1), Typ::Fun(d2, r2)) => compare(d1, d2).then_with(|| compare(r1, r2)),
            (Typ::Record(xts1), Typ::Record(xts2)) => {
                let mut s1 = xts1.clone();
                let mut s2 = xts2.clone();
                sort_fields(&mut s1);
                sort_fields(&mut s2);
                compare_field_lists(&s1, &s2)
            }
            (Typ::Datatype(n1, _), Typ::Datatype(n2, _)) => n1.cmp(n2),
            (Typ::Ffi(m1, x1), Typ::Ffi(m2, x2)) => m1.cmp(m2).then_with(|| x1.cmp(x2)),
            (Typ::Option(t1), Typ::Option(t2)) => compare(t1, t2),
            (Typ::List(t1), Typ::List(t2)) => compare(t1, t2),
            (Typ::Source, Typ::Source) => Ordering::Equal,
            (Typ::Signal(t1), Typ::Signal(t2)) => compare(t1, t2),
            // Compare two Transaction types by their result type.
            (Typ::Transaction(t1), Typ::Transaction(t2)) => compare(t1, t2),
            _ => tag(left).cmp(&tag(right)),
        }
    }

    fn compare_field_lists(left: &[(String, LocTyp)], right: &[(String, LocTyp)]) -> Ordering {
        let len_ord = left.len().cmp(&right.len());
        if len_ord != Ordering::Equal {
            return len_ord;
        }
        for ((left_name, left_type), (right_name, right_type)) in left.iter().zip(right.iter()) {
            let order = left_name
                .cmp(right_name)
                .then_with(|| compare(left_type, right_type));
            if order != Ordering::Equal {
                return order;
            }
        }
        Ordering::Equal
    }

    // -----------------------------------------------------------------------
    // map — transform every sub-type, bottom-up
    // -----------------------------------------------------------------------

    pub fn map<F>(typ: LocTyp, visitor: &mut F) -> LocTyp
    where
        F: FnMut(Typ) -> Typ,
    {
        let span = typ.span.clone();
        let inner = map_node(typ.node, visitor);
        let transformed = visitor(inner);
        crate::error_types::Located::new(transformed, span)
    }

    fn map_node<F>(t: Typ, f: &mut F) -> Typ
    where
        F: FnMut(Typ) -> Typ,
    {
        match t {
            Typ::Fun(d, r) => Typ::Fun(Box::new(map(*d, f)), Box::new(map(*r, f))),
            Typ::Record(xts) => {
                let xts2 = xts.into_iter().map(|(x, t)| (x, map(t, f))).collect();
                Typ::Record(xts2)
            }
            Typ::Option(t) => Typ::Option(Box::new(map(*t, f))),
            Typ::List(t) => Typ::List(Box::new(map(*t, f))),
            Typ::Signal(t) => Typ::Signal(Box::new(map(*t, f))),
            // Recurse into the result type of a transaction.
            Typ::Transaction(t) => Typ::Transaction(Box::new(map(*t, f))),
            other => other,
        }
    }

    // -----------------------------------------------------------------------
    // map_b — transform with a binder context (unused in Mono, provided for
    // API parity)
    // -----------------------------------------------------------------------

    pub fn map_b<Ctx, F>(t: LocTyp, ctx: Ctx, f: &F) -> LocTyp
    where
        F: Fn(Ctx, Typ) -> Typ,
        Ctx: Clone,
    {
        let mut visitor = |node| f(ctx.clone(), node);
        map(t, &mut visitor)
    }

    // -----------------------------------------------------------------------
    // exists — check if any sub-type satisfies a predicate
    // -----------------------------------------------------------------------

    pub fn exists<F>(typ: &LocTyp, predicate: &F) -> bool
    where
        F: Fn(&Typ) -> bool,
    {
        if predicate(&typ.node) {
            return true;
        }
        match &typ.node {
            Typ::Fun(domain, range) => exists(domain, predicate) || exists(range, predicate),
            Typ::Record(field_list) => field_list
                .iter()
                .any(|(_, field_type)| exists(field_type, predicate)),
            Typ::Option(inner) => exists(inner, predicate),
            Typ::List(inner) => exists(inner, predicate),
            Typ::Signal(inner) => exists(inner, predicate),
            // Check inside the result type of a transaction.
            Typ::Transaction(inner) => exists(inner, predicate),
            _ => false,
        }
    }

    // -----------------------------------------------------------------------
    // fold — accumulate state over every sub-type, top-down pre-order
    // -----------------------------------------------------------------------

    pub fn fold<S, F>(typ: &LocTyp, init: S, folder: &F) -> S
    where
        F: Fn(&Typ, S) -> S,
    {
        let accumulator = folder(&typ.node, init);
        match &typ.node {
            Typ::Fun(domain, range) => {
                let accumulator = fold(domain, accumulator, folder);
                fold(range, accumulator, folder)
            }
            Typ::Record(field_list) => {
                field_list.iter().fold(accumulator, |acc, (_, field_type)| {
                    fold(field_type, acc, folder)
                })
            }
            Typ::Option(inner) => fold(inner, accumulator, folder),
            Typ::List(inner) => fold(inner, accumulator, folder),
            Typ::Signal(inner) => fold(inner, accumulator, folder),
            // Fold over the result type of a transaction.
            Typ::Transaction(inner) => fold(inner, accumulator, folder),
            _ => accumulator,
        }
    }
}

// ---------------------------------------------------------------------------
// pub mod exp
// ---------------------------------------------------------------------------

pub mod exp {
    use super::*;

    // Binder variants that can extend the traversal context.
    #[derive(Debug, Clone)]
    pub enum Binder {
        /// A bound datatype: `(name, id, constructors)`.
        Datatype(String, usize, Vec<(String, usize, Option<LocTyp>)>),
        /// A relative (lambda) binding: `(name, type)`.
        RelE(String, LocTyp),
        /// A named (top-level) binding: `(name, id, type, optional_body, module_path)`.
        NamedE(String, usize, LocTyp, Option<LocExp>, String),
    }

    // -----------------------------------------------------------------------
    // map — transform every sub-expression and sub-type, bottom-up
    // -----------------------------------------------------------------------

    pub fn map<FT, FE>(e: LocExp, ft: &FT, fe: &FE) -> LocExp
    where
        FT: Fn(Typ) -> Typ,
        FE: Fn(Exp) -> Exp,
    {
        map_b(e, &mut (), &|_, t| ft(t), &|_, e| fe(e), &|_, _| {})
    }

    // -----------------------------------------------------------------------
    // map_b — transform with a mutable binder context
    // -----------------------------------------------------------------------

    pub fn map_b<Ctx, FT, FE, FB>(e: LocExp, ctx: &mut Ctx, ft: &FT, fe: &FE, bind: &FB) -> LocExp
    where
        FT: Fn(&mut Ctx, Typ) -> Typ,
        FE: Fn(&mut Ctx, Exp) -> Exp,
        FB: Fn(&mut Ctx, &Binder),
        Ctx: Clone,
    {
        let span = e.span.clone();
        let inner = map_b_node(e.node, ctx, ft, fe, bind);
        let transformed = fe(ctx, inner);
        crate::error_types::Located::new(transformed, span)
    }

    fn map_typ_with_ctx<Ctx, FT>(t: LocTyp, ctx: &mut Ctx, ft: &FT) -> LocTyp
    where
        FT: Fn(&mut Ctx, Typ) -> Typ,
    {
        typ::map(t, &mut |node| ft(ctx, node))
    }

    fn map_b_node<Ctx, FT, FE, FB>(e: Exp, ctx: &mut Ctx, ft: &FT, fe: &FE, bind: &FB) -> Exp
    where
        FT: Fn(&mut Ctx, Typ) -> Typ,
        FE: Fn(&mut Ctx, Exp) -> Exp,
        FB: Fn(&mut Ctx, &Binder),
        Ctx: Clone,
    {
        match e {
            Exp::Prim(_) | Exp::Rel(_) | Exp::Named(_) | Exp::Ffi(_, _) => e,

            Exp::Con(dk, pc, arg) => {
                let arg2 = arg.map(|a| Box::new(map_b(*a, ctx, ft, fe, bind)));
                Exp::Con(dk, pc, arg2)
            }

            Exp::None(t) => Exp::None(map_typ_with_ctx(t, ctx, ft)),

            Exp::Some(t, inner) => {
                let t2 = map_typ_with_ctx(t, ctx, ft);
                let inner2 = map_b(*inner, ctx, ft, fe, bind);
                Exp::Some(t2, Box::new(inner2))
            }

            Exp::FfiApp(m, x, args) => {
                let args2 = args
                    .into_iter()
                    .map(|(e, t)| {
                        let e2 = map_b(e, ctx, ft, fe, bind);
                        let t2 = map_typ_with_ctx(t, ctx, ft);
                        (e2, t2)
                    })
                    .collect();
                Exp::FfiApp(m, x, args2)
            }

            Exp::App(e1, e2) => {
                let e1b = map_b(*e1, ctx, ft, fe, bind);
                let e2b = map_b(*e2, ctx, ft, fe, bind);
                Exp::App(Box::new(e1b), Box::new(e2b))
            }

            Exp::Abs(x, dom, ran, body) => {
                let dom2 = map_typ_with_ctx(dom.clone(), ctx, ft);
                let ran2 = map_typ_with_ctx(ran, ctx, ft);
                let b = Binder::RelE(x.clone(), dom2.clone());
                bind(ctx, &b);
                let body2 = map_b(*body, ctx, ft, fe, bind);
                Exp::Abs(x, dom2, ran2, Box::new(body2))
            }

            Exp::Unop(s, e1) => {
                let e1b = map_b(*e1, ctx, ft, fe, bind);
                Exp::Unop(s, Box::new(e1b))
            }

            Exp::Binop(bi, s, e1, e2) => {
                let e1b = map_b(*e1, ctx, ft, fe, bind);
                let e2b = map_b(*e2, ctx, ft, fe, bind);
                Exp::Binop(bi, s, Box::new(e1b), Box::new(e2b))
            }

            Exp::Record(xets) => {
                let xets2 = xets
                    .into_iter()
                    .map(|(x, e, t)| {
                        let e2 = map_b(e, ctx, ft, fe, bind);
                        let t2 = map_typ_with_ctx(t, ctx, ft);
                        (x, e2, t2)
                    })
                    .collect();
                Exp::Record(xets2)
            }

            Exp::Field(e1, x) => {
                let e1b = map_b(*e1, ctx, ft, fe, bind);
                Exp::Field(Box::new(e1b), x)
            }

            Exp::Case(disc, arms, meta) => {
                let disc2 = map_b(*disc, ctx, ft, fe, bind);
                let arms2: Vec<(LocPat, LocExp)> = arms
                    .into_iter()
                    .map(|(p, arm_e)| {
                        pat_extend_ctx(&p, ctx, bind);
                        let arm_e2 = map_b(arm_e, ctx, ft, fe, bind);
                        (p, arm_e2)
                    })
                    .collect();
                let disc_t = map_typ_with_ctx(meta.disc, ctx, ft);
                let result_t = map_typ_with_ctx(meta.result, ctx, ft);
                Exp::Case(
                    Box::new(disc2),
                    arms2,
                    CaseMeta {
                        disc: disc_t,
                        result: result_t,
                    },
                )
            }

            Exp::Strcat(e1, e2) => {
                let e1b = map_b(*e1, ctx, ft, fe, bind);
                let e2b = map_b(*e2, ctx, ft, fe, bind);
                Exp::Strcat(Box::new(e1b), Box::new(e2b))
            }

            Exp::Error(e1, t) => {
                let e1b = map_b(*e1, ctx, ft, fe, bind);
                let t2 = map_typ_with_ctx(t, ctx, ft);
                Exp::Error(Box::new(e1b), t2)
            }

            Exp::ReturnBlob { blob, mime_type, t } => {
                let blob2 = blob.map(|b| Box::new(map_b(*b, ctx, ft, fe, bind)));
                let mime2 = map_b(*mime_type, ctx, ft, fe, bind);
                let t2 = map_typ_with_ctx(t, ctx, ft);
                Exp::ReturnBlob {
                    blob: blob2,
                    mime_type: Box::new(mime2),
                    t: t2,
                }
            }

            Exp::Redirect(e1, t) => {
                let e1b = map_b(*e1, ctx, ft, fe, bind);
                let t2 = map_typ_with_ctx(t, ctx, ft);
                Exp::Redirect(Box::new(e1b), t2)
            }

            Exp::Write(e1) => {
                let e1b = map_b(*e1, ctx, ft, fe, bind);
                Exp::Write(Box::new(e1b))
            }

            Exp::Seq(e1, e2) => {
                let e1b = map_b(*e1, ctx, ft, fe, bind);
                let e2b = map_b(*e2, ctx, ft, fe, bind);
                Exp::Seq(Box::new(e1b), Box::new(e2b))
            }

            Exp::Let(x, t, e1, e2) => {
                let t2 = map_typ_with_ctx(t.clone(), ctx, ft);
                let e1b = map_b(*e1, ctx, ft, fe, bind);
                let binder = Binder::RelE(x.clone(), t2.clone());
                bind(ctx, &binder);
                let e2b = map_b(*e2, ctx, ft, fe, bind);
                Exp::Let(x, t2, Box::new(e1b), Box::new(e2b))
            }

            Exp::Closure(n, envs) => {
                let envs2 = envs
                    .into_iter()
                    .map(|e| map_b(e, ctx, ft, fe, bind))
                    .collect();
                Exp::Closure(n, envs2)
            }

            Exp::Query(qm) => {
                let exps2: Vec<(String, LocTyp)> = qm
                    .exps
                    .into_iter()
                    .map(|(x, t)| (x, map_typ_with_ctx(t, ctx, ft)))
                    .collect();
                let tables2: Vec<(String, Vec<(String, LocTyp)>)> = qm
                    .tables
                    .into_iter()
                    .map(|(x, xts)| {
                        let xts2 = xts
                            .into_iter()
                            .map(|(f, t)| (f, map_typ_with_ctx(t, ctx, ft)))
                            .collect();
                        (x, xts2)
                    })
                    .collect();
                let state2 = map_typ_with_ctx(qm.state, ctx, ft);
                let query2 = map_b(*qm.query, ctx, ft, fe, bind);
                // body is evaluated with two extra bindings for "r" and "acc"
                let row_t = crate::error_types::Located::new(
                    Typ::Record(
                        exps2
                            .iter()
                            .cloned()
                            .chain(tables2.iter().map(|(x, xts)| {
                                (
                                    x.clone(),
                                    crate::error_types::Located::new(
                                        Typ::Record(xts.clone()),
                                        state2.span.clone(),
                                    ),
                                )
                            }))
                            .collect(),
                    ),
                    state2.span.clone(),
                );
                let mut body_ctx = ctx.clone();
                bind(&mut body_ctx, &Binder::RelE("r".into(), row_t));
                bind(&mut body_ctx, &Binder::RelE("acc".into(), state2.clone()));
                let body2 = map_b(*qm.body, &mut body_ctx, ft, fe, bind);
                let initial2 = map_b(*qm.initial, ctx, ft, fe, bind);
                Exp::Query(QueryMeta {
                    exps: exps2,
                    tables: tables2,
                    state: state2,
                    query: Box::new(query2),
                    body: Box::new(body2),
                    initial: Box::new(initial2),
                })
            }

            Exp::Dml(e1, fm) => {
                let e1b = map_b(*e1, ctx, ft, fe, bind);
                Exp::Dml(Box::new(e1b), fm)
            }

            Exp::Nextval(e1) => {
                let e1b = map_b(*e1, ctx, ft, fe, bind);
                Exp::Nextval(Box::new(e1b))
            }

            Exp::Setval(e1, e2) => {
                let e1b = map_b(*e1, ctx, ft, fe, bind);
                let e2b = map_b(*e2, ctx, ft, fe, bind);
                Exp::Setval(Box::new(e1b), Box::new(e2b))
            }

            Exp::Uurlify(e1, t, b) => {
                let e1b = map_b(*e1, ctx, ft, fe, bind);
                let t2 = map_typ_with_ctx(t, ctx, ft);
                Exp::Uurlify(Box::new(e1b), t2, b)
            }

            Exp::JavaScript(mode, e1) => {
                let mode2 = match mode {
                    JavaScriptMode::Source(t) => {
                        JavaScriptMode::Source(map_typ_with_ctx(t, ctx, ft))
                    }
                    other => other,
                };
                let e1b = map_b(*e1, ctx, ft, fe, bind);
                Exp::JavaScript(mode2, Box::new(e1b))
            }

            Exp::SignalReturn(e1) => {
                let e1b = map_b(*e1, ctx, ft, fe, bind);
                Exp::SignalReturn(Box::new(e1b))
            }

            Exp::SignalBind(e1, e2) => {
                let e1b = map_b(*e1, ctx, ft, fe, bind);
                let e2b = map_b(*e2, ctx, ft, fe, bind);
                Exp::SignalBind(Box::new(e1b), Box::new(e2b))
            }

            Exp::SignalSource(e1) => {
                let e1b = map_b(*e1, ctx, ft, fe, bind);
                Exp::SignalSource(Box::new(e1b))
            }

            Exp::ServerCall(e1, t, eff, fm) => {
                let e1b = map_b(*e1, ctx, ft, fe, bind);
                let t2 = map_typ_with_ctx(t, ctx, ft);
                Exp::ServerCall(Box::new(e1b), t2, eff, fm)
            }

            Exp::Recv(e1, t) => {
                let e1b = map_b(*e1, ctx, ft, fe, bind);
                let t2 = map_typ_with_ctx(t, ctx, ft);
                Exp::Recv(Box::new(e1b), t2)
            }

            Exp::Sleep(e1) => {
                let e1b = map_b(*e1, ctx, ft, fe, bind);
                Exp::Sleep(Box::new(e1b))
            }

            Exp::Spawn(e1) => {
                let e1b = map_b(*e1, ctx, ft, fe, bind);
                Exp::Spawn(Box::new(e1b))
            }
        }
    }

    /// Walk the pattern and call `bind` for every variable it introduces.
    fn pat_extend_ctx<Ctx, FB>(p: &LocPat, ctx: &mut Ctx, bind: &FB)
    where
        FB: Fn(&mut Ctx, &Binder),
    {
        match &p.node {
            Pat::Var(x, t) => {
                bind(ctx, &Binder::RelE(x.clone(), t.clone()));
            }
            Pat::Prim(_) => {}
            Pat::Con(_, _, inner) => {
                if let Some(inner_p) = inner {
                    pat_extend_ctx(inner_p, ctx, bind);
                }
            }
            Pat::Record(xpts) => {
                for (_, p, _) in xpts {
                    pat_extend_ctx(p, ctx, bind);
                }
            }
            Pat::None(_) => {}
            Pat::Some(_, inner) => {
                pat_extend_ctx(inner, ctx, bind);
            }
        }
    }

    // -----------------------------------------------------------------------
    // exists — check if any sub-expression or sub-type satisfies a predicate
    // -----------------------------------------------------------------------

    pub fn exists<FT, FE>(e: &LocExp, ft: &FT, fe: &FE) -> bool
    where
        FT: Fn(&Typ) -> bool,
        FE: Fn(&Exp) -> bool,
    {
        if fe(&e.node) {
            return true;
        }
        match &e.node {
            Exp::Prim(_) | Exp::Rel(_) | Exp::Named(_) | Exp::Ffi(_, _) => false,

            Exp::Con(_, _, arg) => arg.as_ref().is_some_and(|a| exists(a, ft, fe)),

            Exp::None(t) => typ::exists(t, ft),
            Exp::Some(t, inner) => typ::exists(t, ft) || exists(inner, ft, fe),

            Exp::FfiApp(_, _, args) => args
                .iter()
                .any(|(e, t)| exists(e, ft, fe) || typ::exists(t, ft)),

            Exp::App(e1, e2) => exists(e1, ft, fe) || exists(e2, ft, fe),

            Exp::Abs(_, dom, ran, body) => {
                typ::exists(dom, ft) || typ::exists(ran, ft) || exists(body, ft, fe)
            }

            Exp::Unop(_, e1) => exists(e1, ft, fe),

            Exp::Binop(_, _, e1, e2) => exists(e1, ft, fe) || exists(e2, ft, fe),

            Exp::Record(xets) => xets
                .iter()
                .any(|(_, e, t)| exists(e, ft, fe) || typ::exists(t, ft)),

            Exp::Field(e1, _) => exists(e1, ft, fe),

            Exp::Case(disc, arms, meta) => {
                exists(disc, ft, fe)
                    || arms.iter().any(|(_, e)| exists(e, ft, fe))
                    || typ::exists(&meta.disc, ft)
                    || typ::exists(&meta.result, ft)
            }

            Exp::Strcat(e1, e2) => exists(e1, ft, fe) || exists(e2, ft, fe),

            Exp::Error(e1, t) => exists(e1, ft, fe) || typ::exists(t, ft),

            Exp::ReturnBlob { blob, mime_type, t } => {
                blob.as_ref().is_some_and(|b| exists(b, ft, fe))
                    || exists(mime_type, ft, fe)
                    || typ::exists(t, ft)
            }

            Exp::Redirect(e1, t) => exists(e1, ft, fe) || typ::exists(t, ft),

            Exp::Write(e1) => exists(e1, ft, fe),
            Exp::Seq(e1, e2) => exists(e1, ft, fe) || exists(e2, ft, fe),

            Exp::Let(_, t, e1, e2) => {
                typ::exists(t, ft) || exists(e1, ft, fe) || exists(e2, ft, fe)
            }

            Exp::Closure(_, envs) => envs.iter().any(|e| exists(e, ft, fe)),

            Exp::Query(qm) => {
                qm.exps.iter().any(|(_, t)| typ::exists(t, ft))
                    || qm
                        .tables
                        .iter()
                        .any(|(_, xts)| xts.iter().any(|(_, t)| typ::exists(t, ft)))
                    || typ::exists(&qm.state, ft)
                    || exists(&qm.query, ft, fe)
                    || exists(&qm.body, ft, fe)
                    || exists(&qm.initial, ft, fe)
            }

            Exp::Dml(e1, _) => exists(e1, ft, fe),
            Exp::Nextval(e1) => exists(e1, ft, fe),
            Exp::Setval(e1, e2) => exists(e1, ft, fe) || exists(e2, ft, fe),

            Exp::Uurlify(e1, t, _) => exists(e1, ft, fe) || typ::exists(t, ft),

            Exp::JavaScript(mode, e1) => {
                (match mode {
                    JavaScriptMode::Source(t) => typ::exists(t, ft),
                    _ => false,
                }) || exists(e1, ft, fe)
            }

            Exp::SignalReturn(e1) => exists(e1, ft, fe),
            Exp::SignalBind(e1, e2) => exists(e1, ft, fe) || exists(e2, ft, fe),
            Exp::SignalSource(e1) => exists(e1, ft, fe),

            Exp::ServerCall(e1, t, _, _) => exists(e1, ft, fe) || typ::exists(t, ft),
            Exp::Recv(e1, t) => exists(e1, ft, fe) || typ::exists(t, ft),
            Exp::Sleep(e1) => exists(e1, ft, fe),
            Exp::Spawn(e1) => exists(e1, ft, fe),
        }
    }

    // -----------------------------------------------------------------------
    // fold — accumulate state over every sub-expression and sub-type
    // -----------------------------------------------------------------------

    pub fn fold<S, FT, FE>(e: &LocExp, init: S, ft: &FT, fe: &FE) -> S
    where
        FT: Fn(&Typ, S) -> S,
        FE: Fn(&Exp, S) -> S,
    {
        let s = fe(&e.node, init);
        match &e.node {
            Exp::Prim(_) | Exp::Rel(_) | Exp::Named(_) | Exp::Ffi(_, _) => s,

            Exp::Con(_, _, arg) => {
                if let Some(a) = arg.as_ref() {
                    fold(a, s, ft, fe)
                } else {
                    s
                }
            }

            Exp::None(t) => typ::fold(t, s, ft),
            Exp::Some(t, inner) => {
                let s = typ::fold(t, s, ft);
                fold(inner, s, ft, fe)
            }

            Exp::FfiApp(_, _, args) => args.iter().fold(s, |s, (e, t)| {
                let s = fold(e, s, ft, fe);
                typ::fold(t, s, ft)
            }),

            Exp::App(e1, e2) => {
                let s = fold(e1, s, ft, fe);
                fold(e2, s, ft, fe)
            }

            Exp::Abs(_, dom, ran, body) => {
                let s = typ::fold(dom, s, ft);
                let s = typ::fold(ran, s, ft);
                fold(body, s, ft, fe)
            }

            Exp::Unop(_, e1) => fold(e1, s, ft, fe),

            Exp::Binop(_, _, e1, e2) => {
                let s = fold(e1, s, ft, fe);
                fold(e2, s, ft, fe)
            }

            Exp::Record(xets) => xets.iter().fold(s, |s, (_, e, t)| {
                let s = fold(e, s, ft, fe);
                typ::fold(t, s, ft)
            }),

            Exp::Field(e1, _) => fold(e1, s, ft, fe),

            Exp::Case(disc, arms, meta) => {
                let s = fold(disc, s, ft, fe);
                let s = arms.iter().fold(s, |s, (_, e)| fold(e, s, ft, fe));
                let s = typ::fold(&meta.disc, s, ft);
                typ::fold(&meta.result, s, ft)
            }

            Exp::Strcat(e1, e2) => {
                let s = fold(e1, s, ft, fe);
                fold(e2, s, ft, fe)
            }

            Exp::Error(e1, t) => {
                let s = fold(e1, s, ft, fe);
                typ::fold(t, s, ft)
            }

            Exp::ReturnBlob { blob, mime_type, t } => {
                let s = if let Some(b) = blob.as_ref() {
                    fold(b, s, ft, fe)
                } else {
                    s
                };
                let s = fold(mime_type, s, ft, fe);
                typ::fold(t, s, ft)
            }

            Exp::Redirect(e1, t) => {
                let s = fold(e1, s, ft, fe);
                typ::fold(t, s, ft)
            }

            Exp::Write(e1) => fold(e1, s, ft, fe),
            Exp::Seq(e1, e2) => {
                let s = fold(e1, s, ft, fe);
                fold(e2, s, ft, fe)
            }

            Exp::Let(_, t, e1, e2) => {
                let s = typ::fold(t, s, ft);
                let s = fold(e1, s, ft, fe);
                fold(e2, s, ft, fe)
            }

            Exp::Closure(_, envs) => envs.iter().fold(s, |s, e| fold(e, s, ft, fe)),

            Exp::Query(qm) => {
                let s = qm.exps.iter().fold(s, |s, (_, t)| typ::fold(t, s, ft));
                let s = qm.tables.iter().fold(s, |s, (_, xts)| {
                    xts.iter().fold(s, |s, (_, t)| typ::fold(t, s, ft))
                });
                let s = typ::fold(&qm.state, s, ft);
                let s = fold(&qm.query, s, ft, fe);
                let s = fold(&qm.body, s, ft, fe);
                fold(&qm.initial, s, ft, fe)
            }

            Exp::Dml(e1, _) => fold(e1, s, ft, fe),
            Exp::Nextval(e1) => fold(e1, s, ft, fe),
            Exp::Setval(e1, e2) => {
                let s = fold(e1, s, ft, fe);
                fold(e2, s, ft, fe)
            }

            Exp::Uurlify(e1, t, _) => {
                let s = fold(e1, s, ft, fe);
                typ::fold(t, s, ft)
            }

            Exp::JavaScript(mode, e1) => {
                let s = match mode {
                    JavaScriptMode::Source(t) => typ::fold(t, s, ft),
                    _ => s,
                };
                fold(e1, s, ft, fe)
            }

            Exp::SignalReturn(e1) => fold(e1, s, ft, fe),
            Exp::SignalBind(e1, e2) => {
                let s = fold(e1, s, ft, fe);
                fold(e2, s, ft, fe)
            }
            Exp::SignalSource(e1) => fold(e1, s, ft, fe),

            Exp::ServerCall(e1, t, _, _) => {
                let s = fold(e1, s, ft, fe);
                typ::fold(t, s, ft)
            }
            Exp::Recv(e1, t) => {
                let s = fold(e1, s, ft, fe);
                typ::fold(t, s, ft)
            }
            Exp::Sleep(e1) => fold(e1, s, ft, fe),
            Exp::Spawn(e1) => fold(e1, s, ft, fe),
        }
    }
}

// ---------------------------------------------------------------------------
// pub mod decl
// ---------------------------------------------------------------------------

pub mod decl {
    use super::*;

    // -----------------------------------------------------------------------
    // map — transform a LocDecl's sub-expressions and sub-types
    // -----------------------------------------------------------------------

    pub fn map<FT, FE, FD>(d: LocDecl, ft: &FT, fe: &FE, fd: &FD) -> LocDecl
    where
        FT: Fn(Typ) -> Typ,
        FE: Fn(Exp) -> Exp,
        FD: Fn(Decl) -> Decl,
    {
        let span = d.span.clone();
        let inner = map_node(d.node, ft, fe);
        let transformed = fd(inner);
        crate::error_types::Located::new(transformed, span)
    }

    fn map_typ<FT>(t: LocTyp, ft: &FT) -> LocTyp
    where
        FT: Fn(Typ) -> Typ,
    {
        let mut ft_ref = ft;
        typ::map(t, &mut ft_ref)
    }

    fn map_exp<FT, FE>(e: LocExp, ft: &FT, fe: &FE) -> LocExp
    where
        FT: Fn(Typ) -> Typ,
        FE: Fn(Exp) -> Exp,
    {
        exp::map(e, ft, fe)
    }

    fn map_policy<FT, FE>(pol: Policy, ft: &FT, fe: &FE) -> Policy
    where
        FT: Fn(Typ) -> Typ,
        FE: Fn(Exp) -> Exp,
    {
        match pol {
            Policy::Client(e) => Policy::Client(map_exp(e, ft, fe)),
            Policy::Insert(e) => Policy::Insert(map_exp(e, ft, fe)),
            Policy::Delete(e) => Policy::Delete(map_exp(e, ft, fe)),
            Policy::Update(e) => Policy::Update(map_exp(e, ft, fe)),
            Policy::Sequence(e) => Policy::Sequence(map_exp(e, ft, fe)),
        }
    }

    fn map_node<FT, FE>(d: Decl, ft: &FT, fe: &FE) -> Decl
    where
        FT: Fn(Typ) -> Typ,
        FE: Fn(Exp) -> Exp,
    {
        match d {
            Decl::Datatype(dts) => {
                let dts2 = dts
                    .into_iter()
                    .map(|mut dt| {
                        dt.constrs = dt
                            .constrs
                            .into_iter()
                            .map(|(x, n, t)| (x, n, t.map(|t| map_typ(t, ft))))
                            .collect();
                        dt
                    })
                    .collect();
                Decl::Datatype(dts2)
            }

            Decl::Val(x, n, t, e, s) => {
                let t2 = map_typ(t, ft);
                let e2 = map_exp(e, ft, fe);
                Decl::Val(x, n, t2, e2, s)
            }

            Decl::ValRec(vis) => {
                let vis2 = vis
                    .into_iter()
                    .map(|(x, n, t, e, s)| (x, n, map_typ(t, ft), map_exp(e, ft, fe), s))
                    .collect();
                Decl::ValRec(vis2)
            }

            Decl::Export(ek, s, n, ts, t, b) => {
                let ts2 = ts.into_iter().map(|t| map_typ(t, ft)).collect();
                let t2 = map_typ(t, ft);
                Decl::Export(ek, s, n, ts2, t2, b)
            }

            Decl::Table(s, xts, pe, ce) => {
                let xts2 = xts.into_iter().map(|(x, t)| (x, map_typ(t, ft))).collect();
                let pe2 = map_exp(pe, ft, fe);
                let ce2 = map_exp(ce, ft, fe);
                Decl::Table(s, xts2, pe2, ce2)
            }

            Decl::View(s, xts, e) => {
                let xts2 = xts.into_iter().map(|(x, t)| (x, map_typ(t, ft))).collect();
                let e2 = map_exp(e, ft, fe);
                Decl::View(s, xts2, e2)
            }

            Decl::Task(e1, e2) => Decl::Task(map_exp(e1, ft, fe), map_exp(e2, ft, fe)),

            Decl::Policy(pol) => Decl::Policy(map_policy(pol, ft, fe)),

            // Leaf decls — no sub-types or sub-expressions to transform.
            other => other,
        }
    }

    // -----------------------------------------------------------------------
    // fold — accumulate state over a LocDecl
    // -----------------------------------------------------------------------

    pub fn fold<S, FT, FE, FD>(d: &LocDecl, init: S, ft: &FT, fe: &FE, fd: &FD) -> S
    where
        FT: Fn(&Typ, S) -> S,
        FE: Fn(&Exp, S) -> S,
        FD: Fn(&Decl, S) -> S,
    {
        let s = fd(&d.node, init);
        fold_node(&d.node, s, ft, fe)
    }

    fn fold_typ<S, FT>(t: &LocTyp, init: S, ft: &FT) -> S
    where
        FT: Fn(&Typ, S) -> S,
    {
        typ::fold(t, init, ft)
    }

    fn fold_exp<S, FT, FE>(e: &LocExp, init: S, ft: &FT, fe: &FE) -> S
    where
        FT: Fn(&Typ, S) -> S,
        FE: Fn(&Exp, S) -> S,
    {
        exp::fold(e, init, ft, fe)
    }

    fn fold_policy<S, FT, FE>(pol: &Policy, init: S, ft: &FT, fe: &FE) -> S
    where
        FT: Fn(&Typ, S) -> S,
        FE: Fn(&Exp, S) -> S,
    {
        match pol {
            Policy::Client(e)
            | Policy::Insert(e)
            | Policy::Delete(e)
            | Policy::Update(e)
            | Policy::Sequence(e) => fold_exp(e, init, ft, fe),
        }
    }

    fn fold_node<S, FT, FE>(d: &Decl, init: S, ft: &FT, fe: &FE) -> S
    where
        FT: Fn(&Typ, S) -> S,
        FE: Fn(&Exp, S) -> S,
    {
        match d {
            Decl::Datatype(dts) => dts.iter().fold(init, |s, dt| {
                dt.constrs.iter().fold(s, |s, (_, _, t)| {
                    if let Some(t) = t.as_ref() {
                        fold_typ(t, s, ft)
                    } else {
                        s
                    }
                })
            }),

            Decl::Val(_, _, t, e, _) => {
                let s = fold_typ(t, init, ft);
                fold_exp(e, s, ft, fe)
            }

            Decl::ValRec(vis) => vis.iter().fold(init, |s, (_, _, t, e, _)| {
                let s = fold_typ(t, s, ft);
                fold_exp(e, s, ft, fe)
            }),

            Decl::Export(_, _, _, ts, t, _) => {
                let s = ts.iter().fold(init, |s, t| fold_typ(t, s, ft));
                fold_typ(t, s, ft)
            }

            Decl::Table(_, xts, pe, ce) => {
                let s = xts.iter().fold(init, |s, (_, t)| fold_typ(t, s, ft));
                let s = fold_exp(pe, s, ft, fe);
                fold_exp(ce, s, ft, fe)
            }

            Decl::View(_, xts, e) => {
                let s = xts.iter().fold(init, |s, (_, t)| fold_typ(t, s, ft));
                fold_exp(e, s, ft, fe)
            }

            Decl::Task(e1, e2) => {
                let s = fold_exp(e1, init, ft, fe);
                fold_exp(e2, s, ft, fe)
            }

            Decl::Policy(pol) => fold_policy(pol, init, ft, fe),

            _ => init,
        }
    }

    // -----------------------------------------------------------------------
    // exists — check if any sub-expression or sub-type satisfies a predicate
    // -----------------------------------------------------------------------

    pub fn exists<FT, FE, FD>(d: &LocDecl, ft: &FT, fe: &FE, fd: &FD) -> bool
    where
        FT: Fn(&Typ) -> bool,
        FE: Fn(&Exp) -> bool,
        FD: Fn(&Decl) -> bool,
    {
        if fd(&d.node) {
            return true;
        }
        exists_node(&d.node, ft, fe)
    }

    fn exists_typ<FT>(t: &LocTyp, ft: &FT) -> bool
    where
        FT: Fn(&Typ) -> bool,
    {
        typ::exists(t, ft)
    }

    fn exists_exp<FT, FE>(e: &LocExp, ft: &FT, fe: &FE) -> bool
    where
        FT: Fn(&Typ) -> bool,
        FE: Fn(&Exp) -> bool,
    {
        exp::exists(e, ft, fe)
    }

    fn exists_policy<FT, FE>(pol: &Policy, ft: &FT, fe: &FE) -> bool
    where
        FT: Fn(&Typ) -> bool,
        FE: Fn(&Exp) -> bool,
    {
        match pol {
            Policy::Client(e)
            | Policy::Insert(e)
            | Policy::Delete(e)
            | Policy::Update(e)
            | Policy::Sequence(e) => exists_exp(e, ft, fe),
        }
    }

    fn exists_node<FT, FE>(d: &Decl, ft: &FT, fe: &FE) -> bool
    where
        FT: Fn(&Typ) -> bool,
        FE: Fn(&Exp) -> bool,
    {
        match d {
            Decl::Datatype(dts) => dts.iter().any(|dt| {
                dt.constrs
                    .iter()
                    .any(|(_, _, t)| t.as_ref().is_some_and(|t| exists_typ(t, ft)))
            }),

            Decl::Val(_, _, t, e, _) => exists_typ(t, ft) || exists_exp(e, ft, fe),

            Decl::ValRec(vis) => vis
                .iter()
                .any(|(_, _, t, e, _)| exists_typ(t, ft) || exists_exp(e, ft, fe)),

            Decl::Export(_, _, _, ts, t, _) => {
                ts.iter().any(|t| exists_typ(t, ft)) || exists_typ(t, ft)
            }

            Decl::Table(_, xts, pe, ce) => {
                xts.iter().any(|(_, t)| exists_typ(t, ft))
                    || exists_exp(pe, ft, fe)
                    || exists_exp(ce, ft, fe)
            }

            Decl::View(_, xts, e) => {
                xts.iter().any(|(_, t)| exists_typ(t, ft)) || exists_exp(e, ft, fe)
            }

            Decl::Task(e1, e2) => exists_exp(e1, ft, fe) || exists_exp(e2, ft, fe),

            Decl::Policy(pol) => exists_policy(pol, ft, fe),

            _ => false,
        }
    }
}

// ---------------------------------------------------------------------------
// Level 3 bridge: Prim ↔ TypedValue
// ---------------------------------------------------------------------------
//
// These functions connect Level 3 (term/literal values, `Prim`) to the
// `TypedValue<i64>` / `ScalarValue<i64>` hierarchy so that passes like
// `mono_opt` can perform type-aware constant folding.

/// Returns the [`ScalarTypeTag`] for a [`Prim`] literal.
///
/// This is the narrowest bridge — just the type discriminant, no value conversion.
/// Use [`prim_to_typed_value`] when you also need the concrete value.
pub fn prim_scalar_type(prim: &Prim) -> ScalarTypeTag {
    match prim {
        Prim::Int(_) => ScalarTypeTag::Int, // signed 64-bit integer literal
        Prim::Float(_) => ScalarTypeTag::Float, // IEEE-754 double literal
        Prim::String(_, _) => ScalarTypeTag::String, // UTF-8 string literal
        Prim::Char(_) => ScalarTypeTag::Char, // Unicode character literal
    }
}

/// Convert a [`Prim`] literal into a [`TypedValue<i64>`] for type-aware constant folding.
///
/// Integer and char values are stored as `i64`.  Float values are stored with their bits
/// reinterpreted as `i64` — use [`TypedValue::as_float`] to recover the `f64`.
/// String bytes are stored in [`ScalarValue::String`].
pub fn prim_to_typed_value(prim: &Prim) -> TypedValue<i64> {
    match prim {
        Prim::Int(n) => TypedValue::from_int(*n), // delegate to the TypedValue constructor
        Prim::Float(f) => TypedValue::from_float(*f), // store float bits via from_float
        Prim::String(_, s) => TypedValue {
            value: Values::Scalar(ScalarValue::String(s.as_bytes().to_vec())), // UTF-8 bytes
            type_tag: TypeHierarchy::Scalar(ScalarTypeTag::String),            // string classifier
        },
        Prim::Char(c) => TypedValue {
            value: Values::Scalar(ScalarValue::Int(*c as i64)), // char as unicode scalar i64
            type_tag: TypeHierarchy::Scalar(ScalarTypeTag::Char), // char classifier (not Int)
        },
    }
}

/// Convert a [`TypedValue<i64>`] back to a [`Prim`] if the value is representable.
///
/// Only scalar variants with a clear `Prim` counterpart are converted; compound values
/// and arrays return `None`.  Float bits are reinterpreted from the stored `i64`.
pub fn typed_value_to_prim(tv: &TypedValue<i64>) -> Option<Prim> {
    match (&tv.value, &tv.type_tag) {
        // Integer stored as i64 → Prim::Int.
        (Values::Scalar(ScalarValue::Int(n)), TypeHierarchy::Scalar(ScalarTypeTag::Int)) => {
            Some(Prim::Int(*n)) // straightforward reconstruction
        }
        // Float bits stored as i64 → reinterpret as f64 → Prim::Float.
        (Values::Scalar(ScalarValue::Float(bits)), TypeHierarchy::Scalar(ScalarTypeTag::Float)) => {
            Some(Prim::Float(f64::from_bits(*bits as u64))) // reinterpret bits
        }
        // String bytes → UTF-8 decode → Prim::String.
        (
            Values::Scalar(ScalarValue::String(bytes)),
            TypeHierarchy::Scalar(ScalarTypeTag::String),
        ) => {
            let s = String::from_utf8(bytes.clone()).ok()?; // reject non-UTF-8
            Some(Prim::String(StringMode::Normal, s)) // Normal mode on reconstruction
        }
        // Char stored as i64 unicode scalar → Prim::Char.
        (Values::Scalar(ScalarValue::Int(n)), TypeHierarchy::Scalar(ScalarTypeTag::Char)) => {
            let scalar = u32::try_from(*n).ok()?; // char must fit in u32
            char::from_u32(scalar).map(Prim::Char) // validate unicode scalar
        }
        // Any other combination cannot be converted back to Prim.
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error_types::Located;
    use std::cmp::Ordering;

    #[test]
    fn sort_fields_orders_by_name() {
        let mut fields: Vec<(String, i32)> =
            vec![("z".into(), 3), ("a".into(), 1), ("m".into(), 2)];
        sort_fields(&mut fields);
        assert_eq!(fields[0].0, "a");
        assert_eq!(fields[1].0, "m");
        assert_eq!(fields[2].0, "z");
    }

    #[test]
    fn classify_datatype_enum() {
        let constrs: Vec<(String, usize, Option<LocTyp>)> =
            vec![("A".into(), 0, None), ("B".into(), 1, None)];
        assert_eq!(classify_datatype(0, &constrs), DatatypeKind::Enum);
    }

    #[test]
    fn classify_datatype_option() {
        let unit = Located::dummy(Typ::Record(vec![]));
        let constrs: Vec<(String, usize, Option<LocTyp>)> =
            vec![("None".into(), 0, None), ("Some".into(), 1, Some(unit))];
        assert_eq!(classify_datatype(0, &constrs), DatatypeKind::Option);
    }

    #[test]
    fn classify_datatype_default() {
        let unit = Located::dummy(Typ::Record(vec![]));
        let constrs: Vec<(String, usize, Option<LocTyp>)> = vec![("C".into(), 0, Some(unit))];
        assert_eq!(classify_datatype(0, &constrs), DatatypeKind::Default);
    }

    #[test]
    fn typ_compare_fun_orders_correctly() {
        let unit = Located::dummy(Typ::Record(vec![]));
        let t1 = Located::dummy(Typ::Fun(Box::new(unit.clone()), Box::new(unit.clone())));
        let t2 = Located::dummy(Typ::Fun(Box::new(unit.clone()), Box::new(unit.clone())));
        assert_eq!(typ::compare(&t1, &t2), Ordering::Equal);
    }

    #[test]
    fn typ_compare_ffi_orders_by_module_then_name() {
        let a = Located::dummy(Typ::Ffi("A".into(), "x".into()));
        let b = Located::dummy(Typ::Ffi("B".into(), "y".into()));
        assert_eq!(typ::compare(&a, &b), Ordering::Less);
        assert_eq!(typ::compare(&b, &a), Ordering::Greater);
    }

    #[test]
    fn typ_compare_record_same_order() {
        let unit = Located::dummy(Typ::Record(vec![]));
        let r = Located::dummy(Typ::Record(vec![
            ("x".into(), unit.clone()),
            ("y".into(), unit),
        ]));
        assert_eq!(typ::compare(&r, &r), Ordering::Equal);
    }

    #[test]
    fn typ_compare_option_less_than_list() {
        let unit = Located::dummy(Typ::Record(vec![]));
        let opt = Located::dummy(Typ::Option(Box::new(unit.clone())));
        let list = Located::dummy(Typ::List(Box::new(unit)));
        assert_eq!(typ::compare(&opt, &list), Ordering::Less);
    }

    #[test]
    fn typ_compare_source_equal() {
        let s = Located::dummy(Typ::Source);
        assert_eq!(typ::compare(&s, &s), Ordering::Equal);
    }

    #[test]
    fn typ_compare_signal_equal() {
        let inner = Located::dummy(Typ::Ffi("Basis".into(), "int".into()));
        let sig = Located::dummy(Typ::Signal(Box::new(inner)));
        assert_eq!(typ::compare(&sig, &sig), Ordering::Equal);
    }

    #[test]
    fn typ_compare_fun_less_than_record_by_tag() {
        let unit = Located::dummy(Typ::Record(vec![]));
        let fun = Located::dummy(Typ::Fun(Box::new(unit.clone()), Box::new(unit.clone())));
        let rec = Located::dummy(Typ::Record(vec![]));
        assert_eq!(typ::compare(&fun, &rec), Ordering::Less);
    }

    #[test]
    fn typ_exists_fun_true_in_domain() {
        let unit = Located::dummy(Typ::Record(vec![]));
        let ffi = Located::dummy(Typ::Ffi("Basis".into(), "int".into()));
        let fun = Located::dummy(Typ::Fun(Box::new(ffi), Box::new(unit)));
        let pred = |t: &Typ| matches!(t, Typ::Ffi(m, x) if m == "Basis" && x == "int");
        assert!(typ::exists(&fun, &pred));
    }

    #[test]
    fn typ_exists_record_true_in_field() {
        let unit = Located::dummy(Typ::Record(vec![]));
        let ffi = Located::dummy(Typ::Ffi("Basis".into(), "int".into()));
        let rec = Located::dummy(Typ::Record(vec![("x".into(), unit), ("y".into(), ffi)]));
        let pred = |t: &Typ| matches!(t, Typ::Ffi(m, x) if m == "Basis" && x == "int");
        assert!(typ::exists(&rec, &pred));
    }

    #[test]
    fn typ_exists_option_true_in_inner() {
        let ffi = Located::dummy(Typ::Ffi("Basis".into(), "int".into()));
        let opt = Located::dummy(Typ::Option(Box::new(ffi)));
        let pred = |t: &Typ| matches!(t, Typ::Ffi(m, x) if m == "Basis" && x == "int");
        assert!(typ::exists(&opt, &pred));
    }

    #[test]
    fn typ_exists_false_for_ffi_no_match() {
        let t = Located::dummy(Typ::Ffi("Basis".into(), "int".into()));
        let pred = |t: &Typ| matches!(t, Typ::Ffi(_, x) if x == "string");
        assert!(!typ::exists(&t, &pred));
    }

    #[test]
    fn classify_datatype_default_two_nullary_one_unary() {
        let unit = Located::dummy(Typ::Record(vec![]));
        let constrs: Vec<(String, usize, Option<LocTyp>)> = vec![
            ("A".into(), 0, None),
            ("B".into(), 1, None),
            ("C".into(), 2, Some(unit)),
        ];
        assert_eq!(classify_datatype(0, &constrs), DatatypeKind::Default);
    }

    #[test]
    fn classify_datatype_recursive_unary_defaults() {
        let span = crate::error_types::Span::dummy();
        let datatype_id = 42usize;
        let recursive = Located::new(
            Typ::Datatype(
                datatype_id,
                std::sync::Arc::new(std::sync::Mutex::new(crate::monomorphized::DatatypeDef {
                    kind: DatatypeKind::Default,
                    constrs: Vec::new(),
                })),
            ),
            span.clone(),
        );
        let payload = Located::new(
            Typ::Record(vec![
                (
                    "1".into(),
                    Located::dummy(Typ::Ffi("Basis".into(), "int".into())),
                ),
                ("2".into(), recursive),
            ]),
            span,
        );
        let constrs: Vec<(String, usize, Option<LocTyp>)> =
            vec![("Nil".into(), 0, None), ("Cons".into(), 1, Some(payload))];
        assert_eq!(
            classify_datatype(datatype_id, &constrs),
            DatatypeKind::Default
        );
    }

    #[test]
    fn sort_fields_changes_order() {
        let mut fields: Vec<(String, i32)> = vec![("b".into(), 2), ("a".into(), 1)];
        let before = fields[0].0.clone();
        sort_fields(&mut fields);
        assert_eq!(fields[0].0, "a");
        assert_ne!(fields[0].0, before, "sort_fields must reorder");
    }

    // ── Prim ↔ TypedValue bridge tests ──────────────────────────────────────

    #[test]
    fn prim_int_round_trips_through_typed_value() {
        let original = Prim::Int(42); // a concrete integer literal
        let typed = prim_to_typed_value(&original); // convert to TypedValue
        assert_eq!(typed.as_int(), Some(42)); // value is preserved
        assert_eq!(typed_value_to_prim(&typed), Some(Prim::Int(42))); // round-trip
    }

    #[test]
    fn prim_float_round_trips_through_typed_value() {
        // Use a value that is not an approximation of a well-known constant.
        let test_value: f64 = 1.234_567_891; // arbitrary test value (not a named constant)
        let original = Prim::Float(test_value); // a float literal
        let typed = prim_to_typed_value(&original);
        let recovered = typed.as_float().expect("should recover f64");
        // Bit-exact round-trip: the f64 value must be recovered without any loss.
        assert_eq!(
            recovered.to_bits(),
            test_value.to_bits(),
            "float bits must survive round-trip"
        );
        let prim_back = typed_value_to_prim(&typed).expect("float should round-trip");
        if let Prim::Float(f) = prim_back {
            assert_eq!(f.to_bits(), test_value.to_bits()); // same bits recovered
        } else {
            panic!("expected Prim::Float");
        }
    }

    #[test]
    fn prim_string_round_trips_through_typed_value() {
        let original = Prim::String(StringMode::Normal, "hello".into()); // string literal
        let typed = prim_to_typed_value(&original); // convert to TypedValue
        let recovered = typed_value_to_prim(&typed); // convert back
        assert_eq!(
            recovered,
            Some(Prim::String(StringMode::Normal, "hello".into()))
        );
    }

    #[test]
    fn typed_value_fold_int_binop_add() {
        let left = TypedValue::from_int(10); // first operand
        let right = TypedValue::from_int(32); // second operand
        let result =
            TypedValue::fold_int_binop(&left, &right, "+").expect("addition should succeed");
        assert_eq!(result.as_int(), Some(42)); // 10 + 32 = 42
    }

    #[test]
    fn typed_value_fold_int_binop_div_by_zero_returns_none() {
        let left = TypedValue::from_int(10);
        let right = TypedValue::from_int(0); // division by zero must be guarded
        let result = TypedValue::fold_int_binop(&left, &right, "/");
        assert!(result.is_none(), "division by zero must return None");
    }

    #[test]
    fn prim_scalar_type_returns_correct_tag() {
        assert_eq!(prim_scalar_type(&Prim::Int(0)), ScalarTypeTag::Int); // Int tag
        assert_eq!(prim_scalar_type(&Prim::Float(0.0)), ScalarTypeTag::Float); // Float tag
        assert_eq!(prim_scalar_type(&Prim::Char('x')), ScalarTypeTag::Char); // Char tag
    }
}
