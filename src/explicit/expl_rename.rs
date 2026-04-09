//! ExplRename pass — freshen all named ids in a functor body.
//!
//! When applying a functor multiple times, the body's ids must be freshened to
//! avoid id capture across applications.  Mirrors `expl_rename.sml`.

use std::collections::HashMap;

use crate::error_types::{Located, Span};
use crate::explicit as expl;

// ---------------------------------------------------------------------------
// Renaming state
// ---------------------------------------------------------------------------

/// Maps old named id → fresh id.  `counter` lives outside (shared with the
/// compiler id allocator).
#[derive(Clone)]
struct St {
    renaming: HashMap<usize, usize>,
}

impl St {
    fn new() -> Self {
        St {
            renaming: HashMap::new(),
        }
    }

    /// Allocate a fresh id for `n` (using external counter), record in map.
    fn bind(&mut self, counter: &mut usize, n: usize) -> usize {
        let fresh = *counter;
        *counter += 1;
        self.renaming.insert(n, fresh);
        fresh
    }

    fn lookup(&self, n: usize) -> Option<usize> {
        self.renaming.get(&n).copied()
    }
}

// ---------------------------------------------------------------------------
// Rename helpers
// ---------------------------------------------------------------------------

fn rename_con(st: &St, lc: expl::LocatedConstructor) -> expl::LocatedConstructor {
    let loc = lc.span.clone();
    let mk = |node| Located::new(node, loc.clone());
    match lc.node {
        expl::Constructor::TFun(c1, c2) => mk(expl::Constructor::TFun(
            Box::new(rename_con(st, *c1)),
            Box::new(rename_con(st, *c2)),
        )),
        expl::Constructor::TCFun(x, k, c) => {
            mk(expl::Constructor::TCFun(x, k, Box::new(rename_con(st, *c))))
        }
        expl::Constructor::TRecord(c) => {
            mk(expl::Constructor::TRecord(Box::new(rename_con(st, *c))))
        }
        expl::Constructor::Rel(n) => mk(expl::Constructor::Rel(n)),
        expl::Constructor::Named(n) => match st.lookup(n) {
            None => mk(expl::Constructor::Named(n)),
            Some(n2) => mk(expl::Constructor::Named(n2)),
        },
        expl::Constructor::ModProj(n, ms, x) => match st.lookup(n) {
            None => mk(expl::Constructor::ModProj(n, ms, x)),
            Some(n2) => mk(expl::Constructor::ModProj(n2, ms, x)),
        },
        expl::Constructor::App(c1, c2) => mk(expl::Constructor::App(
            Box::new(rename_con(st, *c1)),
            Box::new(rename_con(st, *c2)),
        )),
        expl::Constructor::Abs(x, k, c) => {
            mk(expl::Constructor::Abs(x, k, Box::new(rename_con(st, *c))))
        }
        expl::Constructor::KAbs(x, c) => {
            mk(expl::Constructor::KAbs(x, Box::new(rename_con(st, *c))))
        }
        expl::Constructor::KApp(c, k) => {
            mk(expl::Constructor::KApp(Box::new(rename_con(st, *c)), k))
        }
        expl::Constructor::TKFun(x, c) => {
            mk(expl::Constructor::TKFun(x, Box::new(rename_con(st, *c))))
        }
        expl::Constructor::Name(s) => mk(expl::Constructor::Name(s)),
        expl::Constructor::Record(k, xcs) => {
            let xcs2 = xcs
                .into_iter()
                .map(|(x, c)| (rename_con(st, x), rename_con(st, c)))
                .collect();
            mk(expl::Constructor::Record(k, xcs2))
        }
        expl::Constructor::Concat(c1, c2) => mk(expl::Constructor::Concat(
            Box::new(rename_con(st, *c1)),
            Box::new(rename_con(st, *c2)),
        )),
        expl::Constructor::Map(k1, k2) => mk(expl::Constructor::Map(k1, k2)),
        expl::Constructor::Unit => mk(expl::Constructor::Unit),
        expl::Constructor::Tuple(cs) => mk(expl::Constructor::Tuple(
            cs.into_iter().map(|c| rename_con(st, c)).collect(),
        )),
        expl::Constructor::Proj(c, i) => {
            mk(expl::Constructor::Proj(Box::new(rename_con(st, *c)), i))
        }
    }
}

fn rename_pat_con(st: &St, pc: expl::PatternConstructor) -> expl::PatternConstructor {
    match pc {
        expl::PatternConstructor::Var(n) => match st.lookup(n) {
            None => expl::PatternConstructor::Var(n),
            Some(n2) => expl::PatternConstructor::Var(n2),
        },
        expl::PatternConstructor::Proj(n, ms, x) => match st.lookup(n) {
            None => expl::PatternConstructor::Proj(n, ms, x),
            Some(n2) => expl::PatternConstructor::Proj(n2, ms, x),
        },
    }
}

fn rename_pat(st: &St, lp: expl::LocatedPattern) -> expl::LocatedPattern {
    let loc = lp.span.clone();
    let mk = |node| Located::new(node, loc.clone());
    match lp.node {
        expl::Pattern::Var(x, c) => mk(expl::Pattern::Var(x, rename_con(st, c))),
        expl::Pattern::Prim(_) => lp,
        expl::Pattern::Constructor(dk, pc, cs, po) => mk(expl::Pattern::Constructor(
            dk,
            rename_pat_con(st, pc),
            cs.into_iter().map(|c| rename_con(st, c)).collect(),
            po.map(|p| Box::new(rename_pat(st, *p))),
        )),
        expl::Pattern::Record(xpcs) => mk(expl::Pattern::Record(
            xpcs.into_iter()
                .map(|(x, p, c)| (x, rename_pat(st, p), rename_con(st, c)))
                .collect(),
        )),
    }
}

fn rename_exp(st: &St, le: expl::LocatedExpression) -> expl::LocatedExpression {
    let loc = le.span.clone();
    let mk = |node| Located::new(node, loc.clone());
    match le.node {
        expl::Expression::Prim(p) => mk(expl::Expression::Prim(p)),
        expl::Expression::Rel(n) => mk(expl::Expression::Rel(n)),
        expl::Expression::Named(n) => match st.lookup(n) {
            None => mk(expl::Expression::Named(n)),
            Some(n2) => mk(expl::Expression::Named(n2)),
        },
        expl::Expression::ModProj(n, ms, x) => match st.lookup(n) {
            None => mk(expl::Expression::ModProj(n, ms, x)),
            Some(n2) => mk(expl::Expression::ModProj(n2, ms, x)),
        },
        expl::Expression::App(e1, e2) => mk(expl::Expression::App(
            Box::new(rename_exp(st, *e1)),
            Box::new(rename_exp(st, *e2)),
        )),
        expl::Expression::Abs(x, dom, ran, e) => mk(expl::Expression::Abs(
            x,
            rename_con(st, dom),
            rename_con(st, ran),
            Box::new(rename_exp(st, *e)),
        )),
        expl::Expression::CApp(e, c) => mk(expl::Expression::CApp(
            Box::new(rename_exp(st, *e)),
            rename_con(st, c),
        )),
        expl::Expression::CAbs(x, k, e) => {
            mk(expl::Expression::CAbs(x, k, Box::new(rename_exp(st, *e))))
        }
        expl::Expression::KAbs(x, e) => mk(expl::Expression::KAbs(x, Box::new(rename_exp(st, *e)))),
        expl::Expression::KApp(e, k) => mk(expl::Expression::KApp(Box::new(rename_exp(st, *e)), k)),
        expl::Expression::Record(xecs) => mk(expl::Expression::Record(
            xecs.into_iter()
                .map(|(x, e, c)| (rename_con(st, x), rename_exp(st, e), rename_con(st, c)))
                .collect(),
        )),
        expl::Expression::Field(e, c, meta) => mk(expl::Expression::Field(
            Box::new(rename_exp(st, *e)),
            rename_con(st, c),
            expl::FieldMeta {
                field: rename_con(st, meta.field),
                rest: rename_con(st, meta.rest),
            },
        )),
        expl::Expression::Concat(e1, c1, e2, c2) => mk(expl::Expression::Concat(
            Box::new(rename_exp(st, *e1)),
            rename_con(st, c1),
            Box::new(rename_exp(st, *e2)),
            rename_con(st, c2),
        )),
        expl::Expression::Cut(e, c, meta) => mk(expl::Expression::Cut(
            Box::new(rename_exp(st, *e)),
            rename_con(st, c),
            expl::FieldMeta {
                field: rename_con(st, meta.field),
                rest: rename_con(st, meta.rest),
            },
        )),
        expl::Expression::CutMulti(e, c, meta) => mk(expl::Expression::CutMulti(
            Box::new(rename_exp(st, *e)),
            rename_con(st, c),
            expl::RestMeta {
                rest: rename_con(st, meta.rest),
            },
        )),
        expl::Expression::Case(e, pes, meta) => mk(expl::Expression::Case(
            Box::new(rename_exp(st, *e)),
            pes.into_iter()
                .map(|(p, e)| (rename_pat(st, p), rename_exp(st, e)))
                .collect(),
            expl::CaseMeta {
                disc: rename_con(st, meta.disc),
                result: rename_con(st, meta.result),
            },
        )),
        expl::Expression::Write(e) => mk(expl::Expression::Write(Box::new(rename_exp(st, *e)))),
        expl::Expression::Let(x, c, e1, e2) => mk(expl::Expression::Let(
            x,
            rename_con(st, c),
            Box::new(rename_exp(st, *e1)),
            Box::new(rename_exp(st, *e2)),
        )),
    }
}

fn rename_sgn_item(st: &St, lsi: expl::LocatedSignatureItem) -> expl::LocatedSignatureItem {
    let loc = lsi.span.clone();
    let mk = |node| Located::new(node, loc.clone());
    match lsi.node {
        expl::SignatureItem::ConAbs(_, _, _) => lsi,
        expl::SignatureItem::Constructor(x, n, k, c) => {
            mk(expl::SignatureItem::Constructor(x, n, k, rename_con(st, c)))
        }
        expl::SignatureItem::Datatype(dts) => mk(expl::SignatureItem::Datatype(
            dts.into_iter()
                .map(|dt| expl::DatatypeDecl {
                    name: dt.name,
                    id: dt.id,
                    params: dt.params,
                    constrs: dt
                        .constrs
                        .into_iter()
                        .map(|(x, n, co)| (x, n, co.map(|c| rename_con(st, c))))
                        .collect(),
                })
                .collect(),
        )),
        expl::SignatureItem::DatatypeImp {
            name,
            id,
            orig_mod,
            orig_path,
            orig_name,
            orig_constrs_path,
            constrs,
        } => mk(expl::SignatureItem::DatatypeImp {
            name,
            id,
            orig_mod,
            orig_path,
            orig_name,
            orig_constrs_path,
            constrs: constrs
                .into_iter()
                .map(|(x, n, co)| (x, n, co.map(|c| rename_con(st, c))))
                .collect(),
        }),
        expl::SignatureItem::Val(x, n, c) => mk(expl::SignatureItem::Val(x, n, rename_con(st, c))),
        expl::SignatureItem::Signature(x, n, sg) => {
            mk(expl::SignatureItem::Signature(x, n, rename_sgn(st, sg)))
        }
        expl::SignatureItem::Structure(x, n, sg) => {
            mk(expl::SignatureItem::Structure(x, n, rename_sgn(st, sg)))
        }
    }
}

fn rename_sgn(st: &St, lsg: expl::LocatedSignature) -> expl::LocatedSignature {
    let loc = lsg.span.clone();
    let mk = |node| Located::new(node, loc.clone());
    match lsg.node {
        expl::Signature::Const(sis) => mk(expl::Signature::Const(
            sis.into_iter().map(|si| rename_sgn_item(st, si)).collect(),
        )),
        expl::Signature::Var(n) => match st.lookup(n) {
            None => mk(expl::Signature::Var(n)),
            Some(n2) => mk(expl::Signature::Var(n2)),
        },
        expl::Signature::Fun(x, n, dom, ran) => mk(expl::Signature::Fun(
            x,
            n,
            Box::new(rename_sgn(st, *dom)),
            Box::new(rename_sgn(st, *ran)),
        )),
        expl::Signature::Where(sg, xs, s, c) => mk(expl::Signature::Where(
            Box::new(rename_sgn(st, *sg)),
            xs,
            s,
            rename_con(st, c),
        )),
        expl::Signature::Proj(n, ms, x) => match st.lookup(n) {
            None => mk(expl::Signature::Proj(n, ms, x)),
            Some(n2) => mk(expl::Signature::Proj(n2, ms, x)),
        },
    }
}

fn rename_decl(st: &St, ld: expl::LocatedDeclaration) -> expl::LocatedDeclaration {
    let loc = ld.span.clone();
    let mk = |node| Located::new(node, loc.clone());
    match ld.node {
        expl::Declaration::Constructor(x, n, k, c) => {
            mk(expl::Declaration::Constructor(x, n, k, rename_con(st, c)))
        }
        expl::Declaration::Datatype(dts) => mk(expl::Declaration::Datatype(
            dts.into_iter()
                .map(|dt| expl::DatatypeDecl {
                    name: dt.name,
                    id: dt.id,
                    params: dt.params,
                    constrs: dt
                        .constrs
                        .into_iter()
                        .map(|(x, n, co)| (x, n, co.map(|c| rename_con(st, c))))
                        .collect(),
                })
                .collect(),
        )),
        expl::Declaration::DatatypeImp {
            name,
            id,
            orig_mod,
            orig_path,
            orig_name,
            orig_constrs_path,
            constrs,
        } => mk(expl::Declaration::DatatypeImp {
            name,
            id,
            orig_mod,
            orig_path,
            orig_name,
            orig_constrs_path,
            constrs: constrs
                .into_iter()
                .map(|(x, n, co)| (x, n, co.map(|c| rename_con(st, c))))
                .collect(),
        }),
        expl::Declaration::Val(x, n, c, e) => mk(expl::Declaration::Val(
            x,
            n,
            rename_con(st, c),
            rename_exp(st, e),
        )),
        expl::Declaration::ValRec(vis) => mk(expl::Declaration::ValRec(
            vis.into_iter()
                .map(|(x, n, c, e)| (x, n, rename_con(st, c), rename_exp(st, e)))
                .collect(),
        )),
        expl::Declaration::Signature(x, n, sg) => {
            mk(expl::Declaration::Signature(x, n, rename_sgn(st, sg)))
        }
        expl::Declaration::Structure(x, n, sg, str) => mk(expl::Declaration::Structure(
            x,
            n,
            rename_sgn(st, sg),
            rename_str(st, str),
        )),
        expl::Declaration::FfiStr(x, n, sg) => {
            mk(expl::Declaration::FfiStr(x, n, rename_sgn(st, sg)))
        }
        expl::Declaration::Export(n, sg, str) => match st.lookup(n) {
            None => mk(expl::Declaration::Export(
                n,
                rename_sgn(st, sg),
                rename_str(st, str),
            )),
            Some(n2) => mk(expl::Declaration::Export(
                n2,
                rename_sgn(st, sg),
                rename_str(st, str),
            )),
        },
        expl::Declaration::Table {
            mod_id,
            name,
            name_id,
            con,
            exp,
            pk_con,
            pk_exp,
            unique_con,
        } => mk(expl::Declaration::Table {
            mod_id,
            name,
            name_id,
            con: rename_con(st, con),
            exp: rename_exp(st, exp),
            pk_con: rename_con(st, pk_con),
            pk_exp: rename_exp(st, pk_exp),
            unique_con: rename_con(st, unique_con),
        }),
        expl::Declaration::Sequence(a, b, c) => mk(expl::Declaration::Sequence(a, b, c)),
        expl::Declaration::View(n, x, n2, e, c) => mk(expl::Declaration::View(
            n,
            x,
            n2,
            rename_exp(st, e),
            rename_con(st, c),
        )),
        expl::Declaration::Index(e1, e2) => mk(expl::Declaration::Index(
            rename_exp(st, e1),
            rename_exp(st, e2),
        )),
        expl::Declaration::Database(s) => mk(expl::Declaration::Database(s)),
        expl::Declaration::Cookie(n, x, n2, c) => {
            mk(expl::Declaration::Cookie(n, x, n2, rename_con(st, c)))
        }
        expl::Declaration::Style(a, b, c) => mk(expl::Declaration::Style(a, b, c)),
        expl::Declaration::Task(e1, e2) => mk(expl::Declaration::Task(
            rename_exp(st, e1),
            rename_exp(st, e2),
        )),
        expl::Declaration::Policy(e) => mk(expl::Declaration::Policy(rename_exp(st, e))),
        expl::Declaration::OnError(n, xs, x) => match st.lookup(n) {
            None => mk(expl::Declaration::OnError(n, xs, x)),
            Some(n2) => mk(expl::Declaration::OnError(n2, xs, x)),
        },
        expl::Declaration::Ffi(x, n, modes, c) => {
            mk(expl::Declaration::Ffi(x, n, modes, rename_con(st, c)))
        }
    }
}

fn rename_str(st: &St, ls: expl::LocatedStructure) -> expl::LocatedStructure {
    let loc = ls.span.clone();
    let mk = |node| Located::new(node, loc.clone());
    match ls.node {
        expl::Structure::Const(ds) => mk(expl::Structure::Const(
            ds.into_iter().map(|d| rename_decl(st, d)).collect(),
        )),
        expl::Structure::Var(n) => match st.lookup(n) {
            None => mk(expl::Structure::Var(n)),
            Some(n2) => mk(expl::Structure::Var(n2)),
        },
        expl::Structure::Proj(str, x) => {
            mk(expl::Structure::Proj(Box::new(rename_str(st, *str)), x))
        }
        expl::Structure::Fun(x, n, dom, ran, body) => mk(expl::Structure::Fun(
            x,
            n,
            rename_sgn(st, dom),
            rename_sgn(st, ran),
            Box::new(rename_str(st, *body)),
        )),
        expl::Structure::App(s1, s2) => mk(expl::Structure::App(
            Box::new(rename_str(st, *s1)),
            Box::new(rename_str(st, *s2)),
        )),
    }
}

// ---------------------------------------------------------------------------
// fromArity helper
// ---------------------------------------------------------------------------

fn from_arity(n: usize, loc: &Span) -> expl::LocatedKind {
    match n == 0 {
        true => Located::new(expl::Kind::Type, loc.clone()),
        false => Located::new(
            expl::Kind::Arrow(
                Box::new(Located::new(expl::Kind::Type, loc.clone())),
                Box::new(from_arity(n - 1, loc)),
            ),
            loc.clone(),
        ),
    }
}

// ---------------------------------------------------------------------------
// dup_decl — allocate fresh ids, emit original + aliases
// ---------------------------------------------------------------------------

fn dup_decl(
    counter: &mut usize,
    st: &mut St,
    ld: expl::LocatedDeclaration,
) -> Vec<expl::LocatedDeclaration> {
    let loc = ld.span.clone();
    let mk = |node| Located::new(node, loc.clone());
    let unit_con = || Located::new(expl::Constructor::Unit, loc.clone());

    match ld.node {
        expl::Declaration::Constructor(x, n, k, c) => {
            let n2 = st.bind(counter, n);
            let c2 = rename_con(st, c);
            vec![
                mk(expl::Declaration::Constructor(
                    x.clone(),
                    n,
                    k.clone(),
                    c2.clone(),
                )),
                mk(expl::Declaration::Constructor(
                    x,
                    n2,
                    k,
                    Located::new(expl::Constructor::Named(n), loc.clone()),
                )),
            ]
        }
        expl::Declaration::Datatype(dts) => {
            // First, build the renamed version of the original decl.
            let renamed_dts: Vec<expl::DatatypeDecl> = dts
                .iter()
                .map(|dt| expl::DatatypeDecl {
                    name: dt.name.clone(),
                    id: dt.id,
                    params: dt.params.clone(),
                    constrs: dt
                        .constrs
                        .iter()
                        .map(|(x, n, co)| {
                            (
                                x.clone(),
                                *n,
                                co.as_ref().map(|c| rename_con(st, c.clone())),
                            )
                        })
                        .collect(),
                })
                .collect();
            let orig_decl = mk(expl::Declaration::Datatype(renamed_dts));

            // Allocate fresh ids for each datatype type and each constructor.
            // Collect (x, n, arity, n', constructors: (x, n_con, n_con'))
            let mut dt_info: Vec<(String, usize, usize, usize, Vec<(String, usize, usize)>)> =
                Vec::new();

            for dt in &dts {
                let n2 = st.bind(counter, dt.id);
                let cn_info: Vec<(String, usize, usize)> = dt
                    .constrs
                    .iter()
                    .map(|(cx, cn, _)| {
                        let cn2 = st.bind(counter, *cn);
                        (cx.clone(), *cn, cn2)
                    })
                    .collect();
                dt_info.push((dt.name.clone(), dt.id, dt.params.len(), n2, cn_info));
            }

            // Type aliases: DCon(x, n', fromArity(arity), CNamed n)
            let type_aliases: Vec<expl::LocatedDeclaration> = dt_info
                .iter()
                .map(|(x, n, arity, n2, _)| {
                    mk(expl::Declaration::Constructor(
                        x.clone(),
                        *n2,
                        from_arity(*arity, &loc),
                        Located::new(expl::Constructor::Named(*n), loc.clone()),
                    ))
                })
                .collect();

            // Constructor value aliases: DVal(x, n_con', unit_con, ENamed n_con)
            let con_aliases: Vec<expl::LocatedDeclaration> = dt_info
                .iter()
                .flat_map(|(_, _, _, _, cns)| {
                    cns.iter().map(|(cx, cn, cn2)| {
                        mk(expl::Declaration::Val(
                            cx.clone(),
                            *cn2,
                            unit_con(),
                            Located::new(expl::Expression::Named(*cn), loc.clone()),
                        ))
                    })
                })
                .collect();

            let mut result = vec![orig_decl];
            result.extend(type_aliases);
            result.extend(con_aliases);
            result
        }
        expl::Declaration::DatatypeImp {
            name,
            id,
            orig_mod,
            orig_path,
            orig_name,
            orig_constrs_path,
            constrs,
        } => {
            // Rename constructors in the original
            let renamed_constrs: Vec<(String, usize, Option<expl::LocatedConstructor>)> = constrs
                .iter()
                .map(|(x, n, co)| {
                    (
                        x.clone(),
                        *n,
                        co.as_ref().map(|c| rename_con(st, c.clone())),
                    )
                })
                .collect();
            let orig_decl = mk(expl::Declaration::DatatypeImp {
                name: name.clone(),
                id,
                orig_mod,
                orig_path: orig_path.clone(),
                orig_name: orig_name.clone(),
                orig_constrs_path: orig_constrs_path.clone(),
                constrs: renamed_constrs.clone(),
            });

            // Allocate fresh ids for constructors
            let mut cn_info: Vec<(String, usize, usize)> = Vec::new();
            for (cx, cn, _) in &constrs {
                let cn2 = st.bind(counter, *cn);
                cn_info.push((cx.clone(), *cn, cn2));
            }

            // Allocate fresh id for the type itself
            let n2 = st.bind(counter, id);

            // Type alias: DCon(name, n', fromArity(len(xs)), CNamed id)
            // Note: DatatypeImp doesn't store xs count directly, we use the
            // number of params inferred (orig_path len is not the same; use 0
            // as placeholder — same as SML which uses `length xs`)
            // We don't have xs here... In SML the DatatypeImp carries xs (the
            // type params of the *implementing* type). We store orig_path for
            // the path, but not the param count. Use 0 as a safe default —
            // the alias is only used as a forwarding stub.
            let type_alias = mk(expl::Declaration::Constructor(
                name.clone(),
                n2,
                from_arity(0, &loc),
                Located::new(expl::Constructor::Named(id), loc.clone()),
            ));

            let con_aliases: Vec<expl::LocatedDeclaration> = cn_info
                .iter()
                .map(|(cx, cn, cn2)| {
                    mk(expl::Declaration::Val(
                        cx.clone(),
                        *cn2,
                        unit_con(),
                        Located::new(expl::Expression::Named(*cn), loc.clone()),
                    ))
                })
                .collect();

            let mut result = vec![orig_decl, type_alias];
            result.extend(con_aliases);
            result
        }
        expl::Declaration::Val(x, n, c, e) => {
            let n2 = st.bind(counter, n);
            let c2 = rename_con(st, c);
            let e2 = rename_exp(st, e);
            vec![
                mk(expl::Declaration::Val(x.clone(), n, c2.clone(), e2)),
                mk(expl::Declaration::Val(
                    x,
                    n2,
                    c2,
                    Located::new(expl::Expression::Named(n), loc.clone()),
                )),
            ]
        }
        expl::Declaration::ValRec(vis) => {
            // Build the renamed original
            let renamed_vis: Vec<(
                String,
                usize,
                expl::LocatedConstructor,
                expl::LocatedExpression,
            )> = vis
                .iter()
                .map(|(x, n, c, e)| {
                    (
                        x.clone(),
                        *n,
                        rename_con(st, c.clone()),
                        rename_exp(st, e.clone()),
                    )
                })
                .collect();
            let orig_decl = mk(expl::Declaration::ValRec(renamed_vis));

            // Allocate fresh ids for each binding
            let aliases: Vec<expl::LocatedDeclaration> = vis
                .iter()
                .map(|(x, n, c, _)| {
                    let n2 = st.bind(counter, *n);
                    let c2 = rename_con(st, c.clone());
                    mk(expl::Declaration::Val(
                        x.clone(),
                        n2,
                        c2,
                        Located::new(expl::Expression::Named(*n), loc.clone()),
                    ))
                })
                .collect();

            let mut result = vec![orig_decl];
            result.extend(aliases);
            result
        }
        expl::Declaration::Signature(x, n, sg) => {
            let n2 = st.bind(counter, n);
            let sg2 = rename_sgn(st, sg);
            vec![
                mk(expl::Declaration::Signature(x.clone(), n, sg2.clone())),
                mk(expl::Declaration::Signature(
                    x,
                    n2,
                    Located::new(expl::Signature::Var(n), loc.clone()),
                )),
            ]
        }
        expl::Declaration::Structure(x, n, sg, str) => {
            let n2 = st.bind(counter, n);
            let sg2 = rename_sgn(st, sg);
            let str2 = rename_str(st, str);
            vec![
                mk(expl::Declaration::Structure(
                    x.clone(),
                    n,
                    sg2.clone(),
                    str2,
                )),
                mk(expl::Declaration::Structure(
                    x,
                    n2,
                    sg2,
                    Located::new(expl::Structure::Var(n), loc.clone()),
                )),
            ]
        }
        expl::Declaration::FfiStr(x, n, sg) => {
            // No alias for FfiStr
            let sg2 = rename_sgn(st, sg);
            vec![mk(expl::Declaration::FfiStr(x, n, sg2))]
        }
        expl::Declaration::Export(n, sg, str) => {
            let n2 = match st.lookup(n) {
                None => n,
                Some(n2) => n2,
            };
            vec![mk(expl::Declaration::Export(
                n2,
                rename_sgn(st, sg),
                rename_str(st, str),
            ))]
        }
        expl::Declaration::Table {
            mod_id,
            name,
            name_id,
            con,
            exp,
            pk_con,
            pk_exp,
            unique_con,
        } => {
            let name_id2 = st.bind(counter, name_id);
            let orig = mk(expl::Declaration::Table {
                mod_id,
                name: name.clone(),
                name_id,
                con: rename_con(st, con),
                exp: rename_exp(st, exp),
                pk_con: rename_con(st, pk_con),
                pk_exp: rename_exp(st, pk_exp),
                unique_con: rename_con(st, unique_con),
            });
            let alias = mk(expl::Declaration::Val(
                name,
                name_id2,
                unit_con(),
                Located::new(expl::Expression::Named(name_id), loc.clone()),
            ));
            vec![orig, alias]
        }
        expl::Declaration::Sequence(n, x, name_id) => {
            let name_id2 = st.bind(counter, name_id);
            let orig = mk(expl::Declaration::Sequence(n, x.clone(), name_id));
            let alias = mk(expl::Declaration::Val(
                x,
                name_id2,
                unit_con(),
                Located::new(expl::Expression::Named(name_id), loc.clone()),
            ));
            vec![orig, alias]
        }
        expl::Declaration::View(n, x, name_id, e, c) => {
            let name_id2 = st.bind(counter, name_id);
            let orig = mk(expl::Declaration::View(
                n,
                x.clone(),
                name_id,
                rename_exp(st, e),
                rename_con(st, c),
            ));
            let alias = mk(expl::Declaration::Val(
                x,
                name_id2,
                unit_con(),
                Located::new(expl::Expression::Named(name_id), loc.clone()),
            ));
            vec![orig, alias]
        }
        expl::Declaration::Index(e1, e2) => {
            vec![mk(expl::Declaration::Index(
                rename_exp(st, e1),
                rename_exp(st, e2),
            ))]
        }
        expl::Declaration::Database(_) => vec![ld],
        expl::Declaration::Cookie(n, x, name_id, c) => {
            let name_id2 = st.bind(counter, name_id);
            let orig = mk(expl::Declaration::Cookie(
                n,
                x.clone(),
                name_id,
                rename_con(st, c),
            ));
            let alias = mk(expl::Declaration::Val(
                x,
                name_id2,
                unit_con(),
                Located::new(expl::Expression::Named(name_id), loc.clone()),
            ));
            vec![orig, alias]
        }
        expl::Declaration::Style(n, x, name_id) => {
            let name_id2 = st.bind(counter, name_id);
            let orig = mk(expl::Declaration::Style(n, x.clone(), name_id));
            let alias = mk(expl::Declaration::Val(
                x,
                name_id2,
                unit_con(),
                Located::new(expl::Expression::Named(name_id), loc.clone()),
            ));
            vec![orig, alias]
        }
        expl::Declaration::Task(e1, e2) => {
            vec![mk(expl::Declaration::Task(
                rename_exp(st, e1),
                rename_exp(st, e2),
            ))]
        }
        expl::Declaration::Policy(e) => {
            vec![mk(expl::Declaration::Policy(rename_exp(st, e)))]
        }
        expl::Declaration::OnError(n, xs, x) => {
            let n2 = match st.lookup(n) {
                None => n,
                Some(n2) => n2,
            };
            vec![mk(expl::Declaration::OnError(n2, xs, x))]
        }
        expl::Declaration::Ffi(x, n, modes, c) => {
            let n2 = st.bind(counter, n);
            let c2 = rename_con(st, c);
            vec![
                mk(expl::Declaration::Ffi(x.clone(), n, modes, c2.clone())),
                mk(expl::Declaration::Val(
                    x,
                    n2,
                    c2,
                    Located::new(expl::Expression::Named(n), loc.clone()),
                )),
            ]
        }
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Freshen all named ids in a functor body.
///
/// `counter` — the shared id allocator (incremented for each fresh id).
/// `formal_name` — the name of the functor parameter (e.g. "M").
/// `formal_id` — the named id of the functor parameter.
/// `body` — the functor body (a `StrConst`).
///
/// Returns the renamed body with the formal prepended as a `DStr` alias.
/// For non-`StrConst` bodies, returns unchanged.
pub fn rename(
    counter: &mut usize,
    formal_name: &str,
    formal_id: usize,
    body: expl::LocatedStructure,
) -> expl::LocatedStructure {
    let loc = body.span.clone();
    match body.node {
        expl::Structure::Const(ds) => {
            let mut st = St::new();
            // Allocate a fresh id for the formal parameter
            let fresh_formal_id = st.bind(counter, formal_id);

            // Process all declarations through dup_decl
            let mut new_ds: Vec<expl::LocatedDeclaration> = Vec::new();
            for d in ds {
                let extras = dup_decl(counter, &mut st, d);
                new_ds.extend(extras);
            }

            // Compute a unique name for the formal that doesn't clash with
            // any DStr in the output.
            let mut formal_name_munged = formal_name.to_string();
            const MAX_FORMAL_NAME_MUNGE_ROUNDS: usize = 65_536;
            for _ in 0..MAX_FORMAL_NAME_MUNGE_ROUNDS {
                let clashes = new_ds.iter().any(|d| {
                    matches!(&d.node,
                    expl::Declaration::Structure(x, _, _, _) if x == &formal_name_munged)
                });
                if !clashes {
                    break;
                }
                formal_name_munged = format!("?{}", formal_name_munged);
            }
            let still_clashes = new_ds.iter().any(|d| {
                matches!(&d.node,
                expl::Declaration::Structure(x, _, _, _) if x == &formal_name_munged)
            });
            if still_clashes {
                panic!("rename: formal name munge exceeded {MAX_FORMAL_NAME_MUNGE_ROUNDS}");
            }

            // Prepend: DStr(formal_name_munged, fresh_formal_id, SgnConst([]), StrVar(formal_id))
            let empty_sgn = Located::new(expl::Signature::Const(vec![]), loc.clone());
            let str_var = Located::new(expl::Structure::Var(formal_id), loc.clone());
            let header = Located::new(
                expl::Declaration::Structure(
                    formal_name_munged,
                    fresh_formal_id,
                    empty_sgn,
                    str_var,
                ),
                loc.clone(),
            );

            let mut result_ds = vec![header];
            result_ds.extend(new_ds);

            Located::new(expl::Structure::Const(result_ds), loc)
        }
        _ => body,
    }
}
