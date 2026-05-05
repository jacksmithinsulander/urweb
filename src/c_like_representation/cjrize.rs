//! CJRize pass: Mono → CJR conversion.
//!
//! Translates monomorphic Mono declarations to the C-like intermediate
//! representation (CJR). Key operations:
//! - Records → struct IDs (via `Sm` memoizer)
//! - DVal with function type → DFun (args unravelled)
//! - DValRec → DFunRec
//! - DExport → export entries (sidedness from Mono ps)
//! - Signal-typed declarations are dropped (client-only)
//!
//! Mirrors `Cjrize.cjrize` in `cjrize.sml`.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

#[cfg(test)]
use std::cell::Cell;

use crate::c_like_representation::{
    self as cjr, CaseMeta, DatatypeDecl, Decl, DmlMeta, Exp, LocDecl, LocExp, LocPat, LocTyp, Pat,
    PatCon, QueryMeta, Task, Typ,
};
use crate::datatype_kind::DatatypeKind;
use crate::diagnostics::{DiagnosticId, DiagnosticPayload};
use crate::error_types::{CompileError, ErrorReporter, Located, Span};
use crate::export::ExportKind;
use crate::monomorphized::{self as mono, DbMode, Sidedness};
use crate::primitives::{Prim, StringMode};

#[cfg(test)]
thread_local! {
    /// Caps work during `cargo test` / mutation so runaway mutants panic instead of timing out.
    static CJRIZE_TICKS: Cell<usize> = const { Cell::new(8_000_000) };
}

#[cfg(test)]
fn cjrize_test_reset_ticks() {
    CJRIZE_TICKS.with(|c| c.set(8_000_000));
}

#[cfg(test)]
fn cjrize_test_tick() {
    CJRIZE_TICKS.with(|c| {
        let n = c.get();
        if n == 0 {
            panic!(
                "cjrize: test tick budget exhausted (likely infinite recursion from a mutation)"
            );
        }
        c.set(n - 1);
    });
}

#[cfg(not(test))]
#[inline]
fn cjrize_test_tick() {}

// ---------------------------------------------------------------------------
// Structural equality on Mono types (for Sm lookup)
// ---------------------------------------------------------------------------

fn typ_eq(a: &mono::Typ, b: &mono::Typ) -> bool {
    match (a, b) {
        (mono::Typ::Fun(a1, a2), mono::Typ::Fun(b1, b2)) => {
            typ_eq(&a1.node, &b1.node) && typ_eq(&a2.node, &b2.node)
        }
        (mono::Typ::Record(af), mono::Typ::Record(bf)) => {
            af.len() == bf.len()
                && af
                    .iter()
                    .zip(bf)
                    .all(|((an, at), (bn, bt))| an == bn && typ_eq(&at.node, &bt.node))
        }
        (mono::Typ::Datatype(an, _), mono::Typ::Datatype(bn, _)) => an == bn,
        (mono::Typ::Ffi(am, ax), mono::Typ::Ffi(bm, bx)) => am == bm && ax == bx,
        (mono::Typ::Option(a), mono::Typ::Option(b)) => typ_eq(&a.node, &b.node),
        (mono::Typ::List(a), mono::Typ::List(b)) => typ_eq(&a.node, &b.node),
        (mono::Typ::Source, mono::Typ::Source) => true,
        (mono::Typ::Signal(a), mono::Typ::Signal(b)) => typ_eq(&a.node, &b.node),
        // Two Transaction types are equal when their result types are equal.
        (mono::Typ::Transaction(a), mono::Typ::Transaction(b)) => typ_eq(&a.node, &b.node),
        _ => false,
    }
}

fn record_fields_eq(a: &[(String, mono::LocTyp)], b: &[(String, mono::LocTyp)]) -> bool {
    a.len() == b.len()
        && a.iter()
            .zip(b)
            .all(|((an, at), (bn, bt))| an == bn && typ_eq(&at.node, &bt.node))
}

// ---------------------------------------------------------------------------
// Sm — struct map: memoizes Mono record types → struct IDs
// ---------------------------------------------------------------------------

struct Sm {
    count: usize,
    /// Mapping from (sorted Mono field types) → struct id.
    normal: Vec<(Vec<(String, mono::LocTyp)>, usize)>,
    /// Mapping from list element type → struct id.
    lists: Vec<(mono::LocTyp, usize)>,
    /// Struct declarations accumulated since last drain.
    decls: Vec<(usize, Vec<(String, LocTyp)>)>,
}

impl Sm {
    fn new() -> Self {
        // Pre-register the unit struct at id 0.
        Sm {
            count: 1,
            normal: vec![(vec![], 0)],
            lists: vec![],
            decls: vec![],
        }
    }

    /// Look up or create a struct id for the given sorted Mono field list.
    /// `xts_mono` is the key; `xts_cjr` is the translated field list to store.
    fn find(
        &mut self,
        xts_mono: &[(String, mono::LocTyp)],
        xts_cjr: Vec<(String, LocTyp)>,
    ) -> usize {
        cjrize_test_tick();
        for (key, id) in &self.normal {
            cjrize_test_tick();
            if record_fields_eq(key, xts_mono) {
                return *id;
            }
        }
        let id = self.count;
        self.count += 1;
        self.normal.push((xts_mono.to_vec(), id));
        self.decls.push((id, xts_cjr));
        id
    }

    /// Look up or create a struct id for a list node with the given element type.
    fn find_list(&mut self, elem_mono: &mono::LocTyp, elem_cjr: &LocTyp) -> usize {
        cjrize_test_tick();
        for (key, id) in &self.lists {
            cjrize_test_tick();
            if typ_eq(&key.node, &elem_mono.node) {
                return *id;
            }
        }
        let id = self.count;
        self.count += 1;
        let span = elem_mono.span.clone();
        let list_t = Located::new(Typ::List(Box::new(elem_cjr.clone()), id), span.clone());
        let xts_cjr = vec![
            ("1".to_string(), elem_cjr.clone()),
            ("2".to_string(), list_t),
        ];
        // Also register in normal map (Mono type for the list node record)
        let list_mono = Located::new(mono::Typ::List(Box::new(elem_mono.clone())), span);
        let xts_mono = vec![
            ("1".to_string(), elem_mono.clone()),
            ("2".to_string(), list_mono),
        ];
        self.normal.push((xts_mono, id));
        self.lists.push((elem_mono.clone(), id));
        self.decls.push((id, xts_cjr));
        id
    }

    /// Extract and clear accumulated struct declarations.
    fn drain_decls(&mut self) -> Vec<(usize, Vec<(String, LocTyp)>)> {
        std::mem::take(&mut self.decls)
    }
}

// ---------------------------------------------------------------------------
// Type translation
// ---------------------------------------------------------------------------

fn cify_typ(t: &mono::LocTyp, sm: &mut Sm) -> LocTyp {
    cify_typ_dtmap(t, sm, &mut HashMap::new())
}

fn cify_typ_dtmap(
    t: &mono::LocTyp,
    sm: &mut Sm,
    dtmap: &mut HashMap<usize, cjr::DatatypeRef>,
) -> LocTyp {
    cjrize_test_tick();
    let loc = t.span.clone();
    match &t.node {
        mono::Typ::Fun(dom, ran) => {
            let cdom = cify_typ_dtmap(dom, sm, dtmap);
            let cran = cify_typ_dtmap(ran, sm, dtmap);
            Located::new(Typ::Fun(Box::new(cdom), Box::new(cran)), loc)
        }
        mono::Typ::Record(fields) => {
            // Sort fields (should already be sorted, but ensure it)
            let mut sorted = fields.clone();
            sorted.sort_by(|(a, _), (b, _)| a.cmp(b));
            let cjr_fields: Vec<(String, LocTyp)> = sorted
                .iter()
                .map(|(x, ft)| (x.clone(), cify_typ_dtmap(ft, sm, dtmap)))
                .collect();
            let id = sm.find(&sorted, cjr_fields);
            Located::new(Typ::Record(id), loc)
        }
        mono::Typ::Datatype(n, r) => {
            if let Some(r_cjr) = dtmap.get(n) {
                return Located::new(Typ::Datatype(DatatypeKind::Default, *n, r_cjr.clone()), loc);
            }
            let r_cjr: cjr::DatatypeRef = Arc::new(Mutex::new(vec![]));
            dtmap.insert(*n, r_cjr.clone());
            let constrs = {
                let guard = crate::compiler_diagnostics::lock_for_compile(
                    r.as_ref(),
                    "cjrize translation cell",
                );
                guard.constrs.clone()
            };
            let translated: Vec<(String, usize, Option<LocTyp>)> = constrs
                .iter()
                .map(|(x, cn, to)| {
                    let ct = to.as_ref().map(|t| cify_typ_dtmap(t, sm, dtmap));
                    (x.clone(), *cn, ct)
                })
                .collect();
            let kind = classify_constrs(&translated);
            *crate::compiler_diagnostics::lock_for_compile(&*r_cjr, "cjrize CJR datatype ref") =
                translated;
            Located::new(Typ::Datatype(kind, *n, r_cjr), loc)
        }
        mono::Typ::Ffi(m, x) => Located::new(Typ::Ffi(m.clone(), x.clone()), loc),
        mono::Typ::Option(inner) => {
            let ci = cify_typ_dtmap(inner, sm, dtmap);
            Located::new(Typ::Option(Box::new(ci)), loc)
        }
        mono::Typ::List(inner) => {
            let ci = cify_typ_dtmap(inner, sm, dtmap);
            let id = sm.find_list(inner, &ci);
            Located::new(Typ::List(Box::new(ci), id), loc)
        }
        mono::Typ::Source => Located::new(Typ::Ffi("Basis".to_string(), "source".to_string()), loc),
        mono::Typ::Signal(_) => {
            // Should have been filtered out before reaching here
            Located::new(Typ::Ffi("Basis".to_string(), "bogus".to_string()), loc)
        }
        mono::Typ::Transaction(inner) => {
            // Lower Typ::Transaction(t) to Fun(unit_record, t) at the C level.
            // A transaction is a suspended computation: () -> t, matching the
            // original representation before Transaction became a distinct variant.
            let unit_record = Located::new(Typ::Record(sm.find(&[], vec![])), loc.clone());
            let cinner = cify_typ_dtmap(inner, sm, dtmap);
            Located::new(Typ::Fun(Box::new(unit_record), Box::new(cinner)), loc)
        }
    }
}

fn classify_constrs(constrs: &[(String, usize, Option<LocTyp>)]) -> DatatypeKind {
    let nullary = constrs.iter().filter(|(_, _, o)| o.is_none()).count();
    let unary = constrs.iter().filter(|(_, _, o)| o.is_some()).count();
    if unary == 0 {
        DatatypeKind::Enum
    } else if nullary == 1 && unary == 1 {
        DatatypeKind::Option
    } else {
        DatatypeKind::Default
    }
}

// ---------------------------------------------------------------------------
// Pattern translation
// ---------------------------------------------------------------------------

fn cify_pat_con(pc: &mono::PatCon, sm: &mut Sm) -> PatCon {
    match pc {
        mono::PatCon::Var(n) => PatCon::Var(*n),
        mono::PatCon::Ffi {
            module,
            datatyp,
            con,
            arg,
        } => PatCon::Ffi {
            module: module.clone(),
            datatyp: datatyp.clone(),
            con: con.clone(),
            arg: arg.as_ref().map(|t| cify_typ(t, sm)),
        },
    }
}

fn cify_pat(p: &mono::LocPat, sm: &mut Sm) -> LocPat {
    cjrize_test_tick();
    let loc = p.span.clone();
    match &p.node {
        mono::Pat::Var(x, t) => Located::new(Pat::Var(x.clone(), cify_typ(t, sm)), loc),
        mono::Pat::Prim(p) => Located::new(Pat::Prim(p.clone()), loc),
        mono::Pat::Con(dk, pc, po) => {
            let cpc = cify_pat_con(pc, sm);
            let cp = po.as_ref().map(|p| Box::new(cify_pat(p, sm)));
            Located::new(Pat::Con(*dk, cpc, cp), loc)
        }
        mono::Pat::Record(xpts) => {
            let cxpts: Vec<_> = xpts
                .iter()
                .map(|(x, p, t)| (x.clone(), cify_pat(p, sm), cify_typ(t, sm)))
                .collect();
            Located::new(Pat::Record(cxpts), loc)
        }
        mono::Pat::None(t) => Located::new(Pat::None(cify_typ(t, sm)), loc),
        mono::Pat::Some(t, p) => {
            Located::new(Pat::Some(cify_typ(t, sm), Box::new(cify_pat(p, sm))), loc)
        }
    }
}

// ---------------------------------------------------------------------------
// Signal detection
// ---------------------------------------------------------------------------

fn type_has_signal(t: &mono::Typ) -> bool {
    match t {
        mono::Typ::Signal(_) => true,
        mono::Typ::Fun(a, b) => type_has_signal(&a.node) || type_has_signal(&b.node),
        mono::Typ::Record(fields) => fields.iter().any(|(_, t)| type_has_signal(&t.node)),
        mono::Typ::Option(inner) | mono::Typ::List(inner) => type_has_signal(&inner.node),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Function unravelling helper
// ---------------------------------------------------------------------------

/// Lift all Rel(n >= depth) by 1 in a Mono expression.
fn lift_mono_exp(depth: usize, e: mono::LocExp) -> mono::LocExp {
    cjrize_test_tick();
    crate::monomorphized::utilities::exp::map(e, &|t| t, &|node| match node {
        mono::Exp::Rel(n) if n >= depth => mono::Exp::Rel(n + 1),
        other => other,
    })
}

/// Unravel a (CJR type, Mono expression) pair into function arguments + body.
///
/// For each `TFun(dom, ran)` layer, if the expression is `EAbs(x, _, _, body)`,
/// we peel the lambda. Otherwise we eta-expand.
///
/// Returns `(args, return_cjr_type, mono_body_to_cify)`.
fn unravel_fun(
    cjr_t: LocTyp,
    e: mono::LocExp,
    loc: &Span,
    args: &mut Vec<(String, LocTyp)>,
) -> (LocTyp, mono::LocExp) {
    cjrize_test_tick();
    const MAX_UNRAVEL: usize = 65_536;
    if args.len() >= MAX_UNRAVEL {
        return (cjr_t, e);
    }
    match cjr_t.node.clone() {
        Typ::Fun(dom, ran) => match e.node {
            mono::Exp::Abs(ax, _, _, body) => {
                args.push((ax, *dom));
                unravel_fun(*ran, *body, loc, args)
            }
            _ => {
                // Eta-expand: lift e and apply to Rel(0).
                let lifted = lift_mono_exp(0, e);
                let app = Located::new(
                    mono::Exp::App(
                        Box::new(lifted),
                        Box::new(Located::new(mono::Exp::Rel(0), loc.clone())),
                    ),
                    loc.clone(),
                );
                args.push(("x".to_string(), *dom));
                unravel_fun(*ran, app, loc, args)
            }
        },
        _ => (cjr_t, e),
    }
}

// ---------------------------------------------------------------------------
// Expression translation
// ---------------------------------------------------------------------------

fn dummy_exp(loc: &Span) -> LocExp {
    Located::new(
        Exp::Prim(Prim::String(StringMode::Normal, String::new())),
        loc.clone(),
    )
}

fn cify_exp(e: &mono::LocExp, sm: &mut Sm, errors: &mut ErrorReporter) -> LocExp {
    cjrize_test_tick();
    let loc = e.span.clone();
    match &e.node {
        mono::Exp::Prim(p) => Located::new(Exp::Prim(p.clone()), loc),
        mono::Exp::Rel(n) => Located::new(Exp::Rel(*n), loc),
        mono::Exp::Named(n) => Located::new(Exp::Named(*n), loc),

        mono::Exp::Con(dk, pc, eo) => {
            let cpc = cify_pat_con(pc, sm);
            let ceo = eo.as_ref().map(|e| Box::new(cify_exp(e, sm, errors)));
            Located::new(Exp::Con(*dk, cpc, ceo), loc)
        }
        mono::Exp::None(t) => Located::new(Exp::None(cify_typ(t, sm)), loc),
        mono::Exp::Some(t, e) => Located::new(
            Exp::Some(cify_typ(t, sm), Box::new(cify_exp(e, sm, errors))),
            loc,
        ),

        mono::Exp::Ffi(m, x) => Located::new(Exp::Ffi(m.clone(), x.clone()), loc),
        mono::Exp::FfiApp(m, x, args) => {
            let cargs: Vec<_> = args
                .iter()
                .map(|(e, t)| (cify_exp(e, sm, errors), cify_typ(t, sm)))
                .collect();
            Located::new(Exp::FfiApp(m.clone(), x.clone(), cargs), loc)
        }

        mono::Exp::App(e1, e2) => {
            // Collect all arguments by unravelling left-spine of App.
            fn collect_args<'a>(
                e: &'a mono::LocExp,
                args: &mut Vec<mono::LocExp>,
                budget: &mut usize,
            ) -> &'a mono::LocExp {
                cjrize_test_tick();
                if *budget == 0 {
                    return e;
                }
                *budget -= 1;
                match &e.node {
                    mono::Exp::App(f, arg) => {
                        let f = collect_args(f, args, budget);
                        args.push(*arg.clone());
                        f
                    }
                    _ => e,
                }
            }
            let mut spine_budget = 65_536usize;
            let mut args = vec![*e2.clone()];
            let f_ref = collect_args(e1, &mut args, &mut spine_budget);
            // args is collected in order [e2_of_outermost, e2_of_next, ...]
            // but collect_args recurses on e1 and pushes e2 last, so args is [innermost_arg, ..., e2]
            // Actually: collect_args(App(App(f, a), b), args=[b]) recurses on App(f,a), pushes a → args=[b, a], returns f
            // So args is in *reverse* application order. Reverse to get [a, b].
            args.reverse();
            let cf = cify_exp(f_ref, sm, errors);
            let cargs: Vec<LocExp> = args.iter().map(|a| cify_exp(a, sm, errors)).collect();
            Located::new(Exp::App(Box::new(cf), cargs), loc)
        }

        mono::Exp::Abs(_, _, _, _) => {
            let _ = (|| -> std::io::Result<()> {
                let mut file = std::fs::OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open("/tmp/urweb-cjr-abs.log")?;
                std::io::Write::write_all(
                    &mut file,
                    format!("cjrize stray abs at {:?}:\n{:#?}\n\n", loc, e).as_bytes(),
                )
            })();
            errors.report_at(
                loc.clone(),
                DiagnosticPayload::new(DiagnosticId::CjrizeAnonymousFunctionRemains, Vec::new()),
            );
            dummy_exp(&loc)
        }

        mono::Exp::Unop(s, e) => {
            Located::new(Exp::Unop(s.clone(), Box::new(cify_exp(e, sm, errors))), loc)
        }
        mono::Exp::Binop(_, s, e1, e2) => Located::new(
            Exp::Binop(
                s.clone(),
                Box::new(cify_exp(e1, sm, errors)),
                Box::new(cify_exp(e2, sm, errors)),
            ),
            loc,
        ),

        mono::Exp::Record(xets) => {
            // Build Mono field type list for Sm lookup (old_xts in SML)
            let old_xts: Vec<(String, mono::LocTyp)> = xets
                .iter()
                .map(|(x, _, t)| (x.clone(), t.clone()))
                .collect();
            let cjr_xets: Vec<(String, LocExp, LocTyp)> = xets
                .iter()
                .map(|(x, e, t)| (x.clone(), cify_exp(e, sm, errors), cify_typ(t, sm)))
                .collect();
            let cjr_xts: Vec<(String, LocTyp)> = cjr_xets
                .iter()
                .map(|(x, _, t)| (x.clone(), t.clone()))
                .collect();
            let si = sm.find(&old_xts, cjr_xts);
            // Sort field expressions alphabetically
            let mut xes: Vec<(String, LocExp)> =
                cjr_xets.into_iter().map(|(x, e, _)| (x, e)).collect();
            xes.sort_by(|(a, _), (b, _)| a.cmp(b));
            Located::new(Exp::Record(si, xes), loc)
        }

        mono::Exp::Field(e, x) => Located::new(
            Exp::Field(Box::new(cify_exp(e, sm, errors)), x.clone()),
            loc,
        ),

        mono::Exp::Case(disc, arms, meta) => {
            let cd = cify_exp(disc, sm, errors);
            let carms: Vec<(LocPat, LocExp)> = arms
                .iter()
                .map(|(p, e)| (cify_pat(p, sm), cify_exp(e, sm, errors)))
                .collect();
            let cdisc = cify_typ(&meta.disc, sm);
            let cresult = cify_typ(&meta.result, sm);
            Located::new(
                Exp::Case(
                    Box::new(cd),
                    carms,
                    CaseMeta {
                        disc: cdisc,
                        result: cresult,
                    },
                ),
                loc,
            )
        }

        mono::Exp::Error(e, t) => Located::new(
            Exp::Error(Box::new(cify_exp(e, sm, errors)), cify_typ(t, sm)),
            loc,
        ),
        mono::Exp::ReturnBlob { blob, mime_type, t } => Located::new(
            Exp::ReturnBlob {
                blob: blob.as_ref().map(|b| Box::new(cify_exp(b, sm, errors))),
                mime_type: Box::new(cify_exp(mime_type, sm, errors)),
                t: cify_typ(t, sm),
            },
            loc,
        ),
        mono::Exp::Redirect(e, t) => Located::new(
            Exp::Redirect(Box::new(cify_exp(e, sm, errors)), cify_typ(t, sm)),
            loc,
        ),

        mono::Exp::Strcat(e1, e2) => {
            // EStrcat(e1, e2) → EFfiApp("Basis", "strcat", [(e1, string), (e2, string)])
            let ce1 = cify_exp(e1, sm, errors);
            let ce2 = cify_exp(e2, sm, errors);
            let s_t = Located::new(
                Typ::Ffi("Basis".to_string(), "string".to_string()),
                loc.clone(),
            );
            Located::new(
                Exp::FfiApp(
                    "Basis".to_string(),
                    "strcat".to_string(),
                    vec![(ce1, s_t.clone()), (ce2, s_t)],
                ),
                loc,
            )
        }

        mono::Exp::Write(e) => Located::new(Exp::Write(Box::new(cify_exp(e, sm, errors))), loc),
        mono::Exp::Seq(e1, e2) => Located::new(
            Exp::Seq(
                Box::new(cify_exp(e1, sm, errors)),
                Box::new(cify_exp(e2, sm, errors)),
            ),
            loc,
        ),
        mono::Exp::Let(x, t, e1, e2) => Located::new(
            Exp::Let(
                x.clone(),
                cify_typ(t, sm),
                Box::new(cify_exp(e1, sm, errors)),
                Box::new(cify_exp(e2, sm, errors)),
            ),
            loc,
        ),

        mono::Exp::Closure(_, _) => {
            errors.report_at(
                loc.clone(),
                DiagnosticPayload::new(DiagnosticId::CjrizeNestedClosureRemains, Vec::new()),
            );
            dummy_exp(&loc)
        }

        mono::Exp::Query(qm) => {
            let exps: Vec<(String, LocTyp)> = qm
                .exps
                .iter()
                .map(|(x, t)| (x.clone(), cify_typ(t, sm)))
                .collect();
            let tables: Vec<(String, Vec<(String, LocTyp)>)> = qm
                .tables
                .iter()
                .map(|(x, xts)| {
                    let cxts = xts
                        .iter()
                        .map(|(x, t)| (x.clone(), cify_typ(t, sm)))
                        .collect();
                    (x.clone(), cxts)
                })
                .collect();

            // Build the combined row for struct lookup
            let loc2 = qm.query.span.clone();
            let mut row_mono: Vec<(String, mono::LocTyp)> = qm.exps.clone();
            for (x, xts) in &qm.tables {
                row_mono.push((
                    x.clone(),
                    Located::new(mono::Typ::Record(xts.clone()), loc2.clone()),
                ));
            }
            row_mono.sort_by(|(a, _), (b, _)| a.cmp(b));

            // CJR: table rows get struct ids too
            let mut table_rnums: Vec<(String, usize)> = Vec::new();
            for (x, xts) in qm.tables.iter() {
                let cxts: Vec<(String, LocTyp)> = xts
                    .iter()
                    .map(|(fx, ft)| (fx.clone(), cify_typ(ft, sm)))
                    .collect();
                let mono_xts: Vec<(String, mono::LocTyp)> = xts.clone();
                let rnum = sm.find(&mono_xts, cxts);
                table_rnums.push((x.clone(), rnum));
            }

            // Build combined CJR row for the row struct
            let mut row_cjr: Vec<(String, LocTyp)> = exps.clone();
            for (x, rnum) in &table_rnums {
                row_cjr.push((x.clone(), Located::new(Typ::Record(*rnum), loc2.clone())));
            }
            row_cjr.sort_by(|(a, _), (b, _)| a.cmp(b));

            let rnum = sm.find(&row_mono, row_cjr);

            Located::new(
                Exp::Query(QueryMeta {
                    exps,
                    tables,
                    rnum,
                    state: cify_typ(&qm.state, sm),
                    query: Box::new(cify_exp(&qm.query, sm, errors)),
                    body: Box::new(cify_exp(&qm.body, sm, errors)),
                    initial: Box::new(cify_exp(&qm.initial, sm, errors)),
                    prepared: None,
                }),
                loc,
            )
        }

        mono::Exp::Dml(e, mode) => Located::new(
            Exp::Dml(DmlMeta {
                dml: Box::new(cify_exp(e, sm, errors)),
                prepared: None,
                mode: *mode,
            }),
            loc,
        ),
        mono::Exp::Nextval(e) => Located::new(
            Exp::Nextval {
                seq: Box::new(cify_exp(e, sm, errors)),
                prepared: None,
            },
            loc,
        ),
        mono::Exp::Setval(seq, count) => Located::new(
            Exp::Setval {
                seq: Box::new(cify_exp(seq, sm, errors)),
                count: Box::new(cify_exp(count, sm, errors)),
            },
            loc,
        ),
        mono::Exp::Uurlify(e, t, b) => Located::new(
            Exp::Uurlify(Box::new(cify_exp(e, sm, errors)), cify_typ(t, sm), *b),
            loc,
        ),

        mono::Exp::JavaScript(_, _) => {
            errors.report_at_with_hint(
                loc.clone(),
                DiagnosticPayload::new(DiagnosticId::CjrizeJavaScriptStillPresent, Vec::new()),
                DiagnosticId::HintCjrizeJavaScriptStillPresent,
                Vec::new(),
            );
            dummy_exp(&loc)
        }
        mono::Exp::SignalReturn(_) => {
            errors.report_at_with_hint(
                loc.clone(),
                DiagnosticPayload::new(DiagnosticId::CjrizeSignalReturnInvalidServer, Vec::new()),
                DiagnosticId::HintCjrizeSignalReturnInvalidServer,
                Vec::new(),
            );
            dummy_exp(&loc)
        }
        mono::Exp::SignalBind(_, _) => {
            errors.report_at_with_hint(
                loc.clone(),
                DiagnosticPayload::new(DiagnosticId::CjrizeSignalBindInvalidServer, Vec::new()),
                DiagnosticId::HintCjrizeSignalBindInvalidServer,
                Vec::new(),
            );
            dummy_exp(&loc)
        }
        mono::Exp::SignalSource(_) => {
            errors.report_at_with_hint(
                loc.clone(),
                DiagnosticPayload::new(DiagnosticId::CjrizeSignalSourceInvalidServer, Vec::new()),
                DiagnosticId::HintCjrizeSignalSourceInvalidServer,
                Vec::new(),
            );
            dummy_exp(&loc)
        }
        mono::Exp::ServerCall(_, _, _, _) => {
            errors.report_at_with_hint(
                loc.clone(),
                DiagnosticPayload::new(DiagnosticId::CjrizeRpcStillOnServer, Vec::new()),
                DiagnosticId::HintCjrizeRpcStillOnServer,
                Vec::new(),
            );
            dummy_exp(&loc)
        }
        mono::Exp::Recv(_, _) => {
            errors.report_at_with_hint(
                loc.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::CjrizeChannelRecvUnsupportedServer,
                    Vec::new(),
                ),
                DiagnosticId::HintCjrizeChannelRecvUnsupportedServer,
                Vec::new(),
            );
            dummy_exp(&loc)
        }
        mono::Exp::Sleep(_) => {
            errors.report_at_with_hint(
                loc.clone(),
                DiagnosticPayload::new(DiagnosticId::CjrizeSleepInvalidServer, Vec::new()),
                DiagnosticId::HintCjrizeSleepInvalidServer,
                Vec::new(),
            );
            dummy_exp(&loc)
        }
        mono::Exp::Spawn(_) => {
            errors.report_at_with_hint(
                loc.clone(),
                DiagnosticPayload::new(DiagnosticId::CjrizeSpawnInvalidServer, Vec::new()),
                DiagnosticId::HintCjrizeSpawnInvalidServer,
                Vec::new(),
            );
            dummy_exp(&loc)
        }
    }
}

// ---------------------------------------------------------------------------
// Table constraint flattening
// ---------------------------------------------------------------------------

#[derive(Clone)]
enum StaticSqlVal {
    String(String),
    Int(i64),
    Bool(bool),
    Record(Vec<(String, StaticSqlVal)>),
}

fn static_sql_val_to_string(v: StaticSqlVal) -> Option<String> {
    match v {
        StaticSqlVal::String(s) => Some(s),
        StaticSqlVal::Int(n) => Some(n.to_string()),
        StaticSqlVal::Bool(true) => Some("1".into()),
        StaticSqlVal::Bool(false) => Some("0".into()),
        StaticSqlVal::Record(_) => None,
    }
}

fn trivial_sql_proof(e: &mono::LocExp) -> bool {
    match &e.node {
        mono::Exp::Prim(Prim::Int(0)) => true,
        mono::Exp::Record(xets) => xets.is_empty(),
        _ => false,
    }
}

fn flatten_sql_app_chain<'a>(
    e: &'a mono::LocExp,
    args: &mut Vec<&'a mono::LocExp>,
) -> &'a mono::LocExp {
    match &e.node {
        mono::Exp::App(f, a) => {
            let head = flatten_sql_app_chain(f, args);
            args.push(a);
            head
        }
        _ => e,
    }
}

fn derive_sql_alias(table_name: &str) -> String {
    let stem = table_name.rsplit('_').next().unwrap_or("t");
    stem.chars()
        .next()
        .map(|c| c.to_ascii_uppercase().to_string())
        .unwrap_or_else(|| "T".into())
}

fn eval_static_sql_value(
    e: &mono::LocExp,
    env: &[StaticSqlVal],
    named: &HashMap<usize, mono::LocExp>,
) -> Option<StaticSqlVal> {
    match &e.node {
        mono::Exp::Rel(n) => env.get(*n).cloned(),
        mono::Exp::Named(n) => named
            .get(n)
            .and_then(|exp| eval_static_sql_value(exp, env, named)),
        mono::Exp::Prim(Prim::String(_, s)) => Some(StaticSqlVal::String(s.clone())),
        mono::Exp::Prim(Prim::Int(n)) => Some(StaticSqlVal::Int(*n)),
        mono::Exp::Record(xets) => {
            let mut out = Vec::with_capacity(xets.len());
            for (name, inner, _) in xets {
                out.push((name.clone(), eval_static_sql_value(inner, env, named)?));
            }
            Some(StaticSqlVal::Record(out))
        }
        mono::Exp::Field(e1, name) => match eval_static_sql_value(e1, env, named)? {
            StaticSqlVal::Record(fields) => fields
                .into_iter()
                .find(|(field_name, _)| field_name == name)
                .map(|(_, v)| v),
            _ => None,
        },
        mono::Exp::Con(
            crate::datatype_kind::DatatypeKind::Enum,
            mono::PatCon::Ffi {
                module,
                datatyp,
                con,
                ..
            },
            None,
        ) if module == "Basis" && datatyp == "bool" => Some(StaticSqlVal::Bool(con == "True")),
        mono::Exp::Strcat(e1, e2) => Some(StaticSqlVal::String(format!(
            "{}{}",
            eval_static_sql_string(e1, env, named)?,
            eval_static_sql_string(e2, env, named)?
        ))),
        mono::Exp::Ffi(module, name) if module == "Basis" => match name.as_str() {
            "sql_no_limit" | "sql_no_offset" | "sql_subset_all" | "sql_asc" => {
                Some(StaticSqlVal::String(String::new()))
            }
            "sql_desc" => Some(StaticSqlVal::String(" DESC".into())),
            _ => None,
        },
        mono::Exp::FfiApp(module, name, args) if module == "Basis" => match name.as_str() {
            "sqlifyInt" if args.len() == 1 => {
                match eval_static_sql_value(&args[0].0, env, named)? {
                    StaticSqlVal::Int(n) => Some(StaticSqlVal::String(n.to_string())),
                    other => Some(StaticSqlVal::String(static_sql_val_to_string(other)?)),
                }
            }
            "sqlifyFloat" if args.len() == 1 => Some(StaticSqlVal::String(eval_static_sql_string(
                &args[0].0, env, named,
            )?)),
            "sqlifyChar" if args.len() == 1 => Some(StaticSqlVal::String(eval_static_sql_string(
                &args[0].0, env, named,
            )?)),
            "sqlifyString" if args.len() == 1 => Some(StaticSqlVal::String(
                eval_static_sql_string(&args[0].0, env, named)?,
            )),
            "checkString" if args.len() == 1 => Some(StaticSqlVal::String(eval_static_sql_string(
                &args[0].0, env, named,
            )?)),
            _ => None,
        },
        mono::Exp::App(_, _) => {
            let mut args = Vec::new();
            let head = flatten_sql_app_chain(e, &mut args);
            let args: Vec<&mono::LocExp> = args;
            if let Some(StaticSqlVal::String(s)) = eval_static_sql_value(head, env, named) {
                if args.iter().all(|arg| trivial_sql_proof(arg)) {
                    return Some(StaticSqlVal::String(s));
                }
            }
            match &head.node {
                mono::Exp::Ffi(module, name) if module == "Basis" => match name.as_str() {
                    "sql_from_table" if args.len() >= 2 => {
                        let table = eval_static_sql_string(args[args.len() - 1], env, named)?;
                        let alias = derive_sql_alias(&table);
                        Some(StaticSqlVal::String(format!("{table} AS T_{alias}")))
                    }
                    "sql_window" if args.len() >= 2 => {
                        eval_static_sql_value(args[args.len() - 1], env, named)
                    }
                    _ => None,
                },
                _ => None,
            }
        }
        mono::Exp::Case(disc, arms, _) => {
            let disc_val = eval_static_sql_value(disc, env, named)?;
            for (pat, arm) in arms {
                let matches = match (&pat.node, &disc_val) {
                    (mono::Pat::Var(_, _), _) => true,
                    (mono::Pat::Prim(Prim::String(_, s)), StaticSqlVal::String(v)) => s == v,
                    (mono::Pat::Prim(Prim::String(_, s)), StaticSqlVal::Bool(true)) => {
                        s == "1" || s.eq_ignore_ascii_case("true")
                    }
                    (mono::Pat::Prim(Prim::String(_, s)), StaticSqlVal::Bool(false)) => {
                        s == "0" || s.eq_ignore_ascii_case("false")
                    }
                    (mono::Pat::Prim(Prim::Int(n)), StaticSqlVal::Int(v)) => *n == *v,
                    (
                        mono::Pat::Con(
                            crate::datatype_kind::DatatypeKind::Enum,
                            mono::PatCon::Ffi {
                                module,
                                datatyp,
                                con,
                                ..
                            },
                            None,
                        ),
                        StaticSqlVal::Bool(v),
                    ) => {
                        module == "Basis"
                            && datatyp == "bool"
                            && ((*v && con == "True") || (!*v && con == "False"))
                    }
                    _ => false,
                };
                if matches {
                    let mut env2 = env.to_vec();
                    if matches!(pat.node, mono::Pat::Var(_, _)) {
                        env2.insert(0, disc_val.clone());
                    }
                    return eval_static_sql_value(arm, &env2, named);
                }
            }
            None
        }
        _ => None,
    }
}

fn eval_static_sql_string(
    e: &mono::LocExp,
    env: &[StaticSqlVal],
    named: &HashMap<usize, mono::LocExp>,
) -> Option<String> {
    eval_static_sql_value(e, env, named).and_then(static_sql_val_to_string)
}

/// Flatten a Mono expression representing table constraints into `(field, value)` pairs.
///
/// Mirrors the `flatten` function in `cjrize.sml`.
fn flatten_constraint(
    e: &mono::LocExp,
    errors: &mut ErrorReporter,
    named: &HashMap<usize, mono::LocExp>,
) -> Vec<(String, String)> {
    cjrize_test_tick();
    match &e.node {
        mono::Exp::Record(xets) if xets.is_empty() => vec![],
        mono::Exp::Record(xets) if xets.len() == 1 => {
            let (x, val_e, _) = &xets[0];
            if let Some(s) = eval_static_sql_string(val_e, &[], named) {
                vec![(x.clone(), s)]
            } else {
                if std::env::var("URWEB_DEBUG_CJR_SQL").ok().as_deref() == Some("1") {
                    eprintln!(
                        "cjrize flatten_constraint non-string field label={} expr={:#?}",
                        x, val_e
                    );
                }
                errors.report_at_with_hint(
                    e.span.clone(),
                    DiagnosticPayload::new(
                        DiagnosticId::CjrizeTableConstraintNotSimpleString,
                        Vec::new(),
                    ),
                    DiagnosticId::HintCjrizeTableConstraintNotSimpleString,
                    Vec::new(),
                );
                vec![]
            }
        }
        mono::Exp::Strcat(e1, e2) => {
            let mut v = flatten_constraint(e1, errors, named);
            v.extend(flatten_constraint(e2, errors, named));
            v
        }
        _ => {
            if std::env::var("URWEB_DEBUG_CJR_SQL").ok().as_deref() == Some("1") {
                eprintln!("cjrize flatten_constraint unsupported expr={:#?}", e);
            }
            errors.report_at_with_hint(
                e.span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::CjrizeTableConstraintNotSimpleString,
                    Vec::new(),
                ),
                DiagnosticId::HintCjrizeTableConstraintNotSimpleString,
                Vec::new(),
            );
            vec![]
        }
    }
}

// ---------------------------------------------------------------------------
// Declaration translation
// ---------------------------------------------------------------------------

/// Stub body for signal/script-typed declarations.
fn stub_body(t: &mono::LocTyp, loc: &Span) -> mono::LocExp {
    cjrize_test_tick();
    match &t.node {
        mono::Typ::Fun(dom, ran) => {
            let body = stub_body(ran, loc);
            Located::new(
                mono::Exp::Abs("_".to_string(), *dom.clone(), *ran.clone(), Box::new(body)),
                loc.clone(),
            )
        }
        _ => Located::new(mono::Exp::Record(vec![]), loc.clone()),
    }
}

fn exp_contains_abs(e: &mono::LocExp) -> bool {
    crate::monomorphized::utilities::exp::exists(e, &|_| false, &|node| {
        matches!(node, mono::Exp::Abs(_, _, _, _))
    })
}

fn reduce_head_apps_for_cjr(e: mono::LocExp) -> mono::LocExp {
    let loc = e.span.clone();
    match e.node {
        mono::Exp::App(f, arg) => {
            let f = reduce_head_apps_for_cjr(*f);
            let arg = reduce_head_apps_for_cjr(*arg);
            match f.node {
                mono::Exp::Abs(_, _, _, body) => reduce_head_apps_for_cjr(
                    crate::monomorphized::environment::sub_exp_in_exp(0, &arg, &body),
                ),
                mono::Exp::Let(x, t, e1, body) => {
                    let lifted_arg = lift_mono_exp(0, arg);
                    let app = Located::new(mono::Exp::App(body, Box::new(lifted_arg)), loc.clone());
                    reduce_head_apps_for_cjr(Located::new(
                        mono::Exp::Let(x, t, e1, Box::new(app)),
                        loc,
                    ))
                }
                other => Located::new(
                    mono::Exp::App(Box::new(Located::new(other, f.span)), Box::new(arg)),
                    loc,
                ),
            }
        }
        mono::Exp::Abs(x, dom, ran, body) => Located::new(
            mono::Exp::Abs(x, dom, ran, Box::new(reduce_head_apps_for_cjr(*body))),
            loc,
        ),
        mono::Exp::Con(dk, pc, eo) => Located::new(
            mono::Exp::Con(
                dk,
                pc,
                eo.map(|inner| Box::new(reduce_head_apps_for_cjr(*inner))),
            ),
            loc,
        ),
        mono::Exp::Some(t, inner) => Located::new(
            mono::Exp::Some(t, Box::new(reduce_head_apps_for_cjr(*inner))),
            loc,
        ),
        mono::Exp::FfiApp(m, x, args) => Located::new(
            mono::Exp::FfiApp(
                m,
                x,
                args.into_iter()
                    .map(|(arg, t)| (reduce_head_apps_for_cjr(arg), t))
                    .collect(),
            ),
            loc,
        ),
        mono::Exp::Unop(op, inner) => Located::new(
            mono::Exp::Unop(op, Box::new(reduce_head_apps_for_cjr(*inner))),
            loc,
        ),
        mono::Exp::Binop(intness, op, left, right) => Located::new(
            mono::Exp::Binop(
                intness,
                op,
                Box::new(reduce_head_apps_for_cjr(*left)),
                Box::new(reduce_head_apps_for_cjr(*right)),
            ),
            loc,
        ),
        mono::Exp::Record(xets) => Located::new(
            mono::Exp::Record(
                xets.into_iter()
                    .map(|(name, exp, t)| (name, reduce_head_apps_for_cjr(exp), t))
                    .collect(),
            ),
            loc,
        ),
        mono::Exp::Field(inner, field) => Located::new(
            mono::Exp::Field(Box::new(reduce_head_apps_for_cjr(*inner)), field),
            loc,
        ),
        mono::Exp::Case(disc, arms, meta) => Located::new(
            mono::Exp::Case(
                Box::new(reduce_head_apps_for_cjr(*disc)),
                arms.into_iter()
                    .map(|(pat, arm)| (pat, reduce_head_apps_for_cjr(arm)))
                    .collect(),
                meta,
            ),
            loc,
        ),
        mono::Exp::Strcat(left, right) => Located::new(
            mono::Exp::Strcat(
                Box::new(reduce_head_apps_for_cjr(*left)),
                Box::new(reduce_head_apps_for_cjr(*right)),
            ),
            loc,
        ),
        mono::Exp::Error(inner, t) => Located::new(
            mono::Exp::Error(Box::new(reduce_head_apps_for_cjr(*inner)), t),
            loc,
        ),
        mono::Exp::ReturnBlob { blob, mime_type, t } => Located::new(
            mono::Exp::ReturnBlob {
                blob: blob.map(|inner| Box::new(reduce_head_apps_for_cjr(*inner))),
                mime_type: Box::new(reduce_head_apps_for_cjr(*mime_type)),
                t,
            },
            loc,
        ),
        mono::Exp::Redirect(inner, t) => Located::new(
            mono::Exp::Redirect(Box::new(reduce_head_apps_for_cjr(*inner)), t),
            loc,
        ),
        mono::Exp::Write(inner) => Located::new(
            mono::Exp::Write(Box::new(reduce_head_apps_for_cjr(*inner))),
            loc,
        ),
        mono::Exp::Seq(left, right) => Located::new(
            mono::Exp::Seq(
                Box::new(reduce_head_apps_for_cjr(*left)),
                Box::new(reduce_head_apps_for_cjr(*right)),
            ),
            loc,
        ),
        mono::Exp::Let(x, t, e1, e2) => Located::new(
            mono::Exp::Let(
                x,
                t,
                Box::new(reduce_head_apps_for_cjr(*e1)),
                Box::new(reduce_head_apps_for_cjr(*e2)),
            ),
            loc,
        ),
        mono::Exp::Closure(n, envs) => Located::new(
            mono::Exp::Closure(n, envs.into_iter().map(reduce_head_apps_for_cjr).collect()),
            loc,
        ),
        mono::Exp::Query(qm) => Located::new(
            mono::Exp::Query(mono::QueryMeta {
                exps: qm.exps,
                tables: qm.tables,
                state: qm.state,
                query: Box::new(reduce_head_apps_for_cjr(*qm.query)),
                body: Box::new(reduce_head_apps_for_cjr(*qm.body)),
                initial: Box::new(reduce_head_apps_for_cjr(*qm.initial)),
            }),
            loc,
        ),
        mono::Exp::Dml(inner, mode) => Located::new(
            mono::Exp::Dml(Box::new(reduce_head_apps_for_cjr(*inner)), mode),
            loc,
        ),
        mono::Exp::Nextval(inner) => Located::new(
            mono::Exp::Nextval(Box::new(reduce_head_apps_for_cjr(*inner))),
            loc,
        ),
        mono::Exp::Setval(seq, count) => Located::new(
            mono::Exp::Setval(
                Box::new(reduce_head_apps_for_cjr(*seq)),
                Box::new(reduce_head_apps_for_cjr(*count)),
            ),
            loc,
        ),
        mono::Exp::Uurlify(inner, t, flag) => Located::new(
            mono::Exp::Uurlify(Box::new(reduce_head_apps_for_cjr(*inner)), t, flag),
            loc,
        ),
        mono::Exp::JavaScript(mode, inner) => Located::new(
            mono::Exp::JavaScript(mode, Box::new(reduce_head_apps_for_cjr(*inner))),
            loc,
        ),
        mono::Exp::SignalReturn(inner) => Located::new(
            mono::Exp::SignalReturn(Box::new(reduce_head_apps_for_cjr(*inner))),
            loc,
        ),
        mono::Exp::SignalBind(left, right) => Located::new(
            mono::Exp::SignalBind(
                Box::new(reduce_head_apps_for_cjr(*left)),
                Box::new(reduce_head_apps_for_cjr(*right)),
            ),
            loc,
        ),
        mono::Exp::SignalSource(inner) => Located::new(
            mono::Exp::SignalSource(Box::new(reduce_head_apps_for_cjr(*inner))),
            loc,
        ),
        mono::Exp::ServerCall(inner, t, eff, mode) => Located::new(
            mono::Exp::ServerCall(Box::new(reduce_head_apps_for_cjr(*inner)), t, eff, mode),
            loc,
        ),
        mono::Exp::Recv(inner, t) => Located::new(
            mono::Exp::Recv(Box::new(reduce_head_apps_for_cjr(*inner)), t),
            loc,
        ),
        mono::Exp::Sleep(inner) => Located::new(
            mono::Exp::Sleep(Box::new(reduce_head_apps_for_cjr(*inner))),
            loc,
        ),
        mono::Exp::Spawn(inner) => Located::new(
            mono::Exp::Spawn(Box::new(reduce_head_apps_for_cjr(*inner))),
            loc,
        ),
        other => Located::new(other, loc),
    }
}

fn cify_decl(
    d: &mono::LocDecl,
    sm: &mut Sm,
    errors: &mut ErrorReporter,
    named: &HashMap<usize, mono::LocExp>,
) -> (
    Option<LocDecl>,
    Option<(ExportKind, String, usize, Vec<LocTyp>, LocTyp, bool)>,
) {
    cjrize_test_tick();
    let loc = d.span.clone();
    match &d.node {
        mono::Decl::Datatype(dts) => {
            let cdts: Vec<DatatypeDecl> = dts
                .iter()
                .map(|dt| {
                    let constrs: Vec<(String, usize, Option<LocTyp>)> = dt
                        .constrs
                        .iter()
                        .map(|(x, n, to)| (x.clone(), *n, to.as_ref().map(|t| cify_typ(t, sm))))
                        .collect();
                    let kind = classify_constrs(&constrs);
                    DatatypeDecl {
                        kind,
                        name: dt.name.clone(),
                        id: dt.id,
                        constrs,
                    }
                })
                .collect();
            (Some(Located::new(Decl::Datatype(cdts), loc)), None)
        }

        mono::Decl::Val(x, n, t, e, _s) => {
            if type_has_signal(&t.node) {
                return (None, None);
            }
            // For script declarations, stub out the body.
            let effective_e = if _s == "<script>" {
                stub_body(t, &loc)
            } else {
                e.clone()
            };

            let ct = cify_typ(t, sm);

            let d = match &ct.node {
                Typ::Fun(..) => {
                    let mut args = Vec::new();
                    let (ran, body) = unravel_fun(ct.clone(), effective_e, &loc, &mut args);
                    let body = reduce_head_apps_for_cjr(body);
                    if exp_contains_abs(&body) {
                        eprintln!("cjrize nested abs in val fun body: {}", x);
                        let _ = (|| -> std::io::Result<()> {
                            let mut file = std::fs::OpenOptions::new()
                                .create(true)
                                .append(true)
                                .open("/tmp/urweb-cjr-bodies.log")?;
                            std::io::Write::write_all(
                                &mut file,
                                format!("VAL FUN {x} @ {:?}\n{body:#?}\n\n", loc).as_bytes(),
                            )
                        })();
                    }
                    let cbody = cify_exp(&body, sm, errors);
                    Decl::Fun(x.clone(), *n, args, ran, cbody)
                }
                _ => {
                    if exp_contains_abs(&effective_e) {
                        eprintln!("cjrize nested abs in val expr: {}", x);
                    }
                    let ce = cify_exp(&effective_e, sm, errors);
                    Decl::Val(x.clone(), *n, ct, ce)
                }
            };
            (Some(Located::new(d, loc)), None)
        }

        mono::Decl::ValRec(vis) => {
            // Drop signal-typed members.
            let vis: Vec<_> = vis
                .iter()
                .filter(|(_, _, t, _, _)| !type_has_signal(&t.node))
                .collect();
            if vis.is_empty() {
                return (None, None);
            }
            let cfuns: Vec<(String, usize, Vec<(String, LocTyp)>, LocTyp, LocExp)> = vis
                .iter()
                .map(|(x, n, t, e, s)| {
                    let effective_e = if *s == "<script>" {
                        stub_body(t, &loc)
                    } else {
                        e.clone()
                    };
                    let ct = cify_typ(t, sm);
                    match &ct.node {
                        Typ::Fun(..) => {
                            let mut args = Vec::new();
                            let (ran, body) = unravel_fun(ct, effective_e, &loc, &mut args);
                            let body = reduce_head_apps_for_cjr(body);
                            if exp_contains_abs(&body) {
                                eprintln!("cjrize nested abs in valrec fun body: {}", x);
                                let _ = (|| -> std::io::Result<()> {
                                    let mut file = std::fs::OpenOptions::new()
                                        .create(true)
                                        .append(true)
                                        .open("/tmp/urweb-cjr-bodies.log")?;
                                    std::io::Write::write_all(
                                        &mut file,
                                        format!("VALREC FUN {x} @ {:?}\n{body:#?}\n\n", loc)
                                            .as_bytes(),
                                    )
                                })();
                            }
                            let cbody = cify_exp(&body, sm, errors);
                            (x.clone(), *n, args, ran, cbody)
                        }
                        _ => {
                            if exp_contains_abs(&effective_e) {
                                eprintln!("cjrize nested abs in valrec expr: {}", x);
                            }
                            errors.report_at(
                                loc.clone(),
                                DiagnosticPayload::new(
                                    DiagnosticId::CjrizeFunctionNotExplicitAtCodegen,
                                    Vec::new(),
                                ),
                            );
                            (
                                x.clone(),
                                *n,
                                vec![],
                                ct,
                                cify_exp(&effective_e, sm, errors),
                            )
                        }
                    }
                })
                .collect();
            (Some(Located::new(Decl::FunRec(cfuns), loc)), None)
        }

        mono::Decl::Export(ek, path, n, ts, t, b) => {
            let cts: Vec<LocTyp> = ts.iter().map(|t| cify_typ(t, sm)).collect();
            let ct = cify_typ(t, sm);
            // Prepend "/" to path
            let full_path = format!("/{}", path);
            (None, Some((*ek, full_path, *n, cts, ct, *b)))
        }

        mono::Decl::Table(name, xts, pe, ce) => {
            let cxts: Vec<(String, LocTyp)> = xts
                .iter()
                .map(|(x, t)| (x.clone(), cify_typ(t, sm)))
                .collect();
            let pk = match &pe.node {
                mono::Exp::Prim(Prim::String(_, s)) => s.clone(),
                _ => {
                    errors.report(CompileError::sql_at_with_hint(
                        pe.span.clone(),
                        DiagnosticPayload::new(
                            DiagnosticId::SqlTablePrimaryKeyNotKnownString,
                            Vec::new(),
                        ),
                        DiagnosticId::HintSqlTablePrimaryKeyNotKnownString,
                        Vec::new(),
                    ));
                    String::new()
                }
            };
            let constraints = flatten_constraint(ce, errors, named);
            (
                Some(Located::new(
                    Decl::Table(name.clone(), cxts, pk, constraints),
                    loc,
                )),
                None,
            )
        }

        mono::Decl::Sequence(name) => (Some(Located::new(Decl::Sequence(name.clone()), loc)), None),

        mono::Decl::View(name, xts, e) => {
            let cxts: Vec<(String, LocTyp)> = xts
                .iter()
                .map(|(x, t)| (x.clone(), cify_typ(t, sm)))
                .collect();
            let sql = if let mono::Exp::FfiApp(m, x, args) = &e.node {
                if m == "Basis" && x == "viewify" && args.len() == 1 {
                    if let Some(s) = eval_static_sql_string(&args[0].0, &[], named) {
                        s
                    } else {
                        if std::env::var("URWEB_DEBUG_CJR_SQL").ok().as_deref() == Some("1") {
                            eprintln!("cjrize viewify non-string arg={:#?}", args[0].0);
                        }
                        errors.report(CompileError::sql_at_with_hint(
                            e.span.clone(),
                            DiagnosticPayload::new(DiagnosticId::SqlViewNotPlainString, Vec::new()),
                            DiagnosticId::HintSqlViewNotPlainStringStrcat,
                            Vec::new(),
                        ));
                        String::new()
                    }
                } else {
                    if std::env::var("URWEB_DEBUG_CJR_SQL").ok().as_deref() == Some("1") {
                        eprintln!("cjrize view unsupported expr={:#?}", e);
                    }
                    errors.report(CompileError::sql_at_with_hint(
                        e.span.clone(),
                        DiagnosticPayload::new(DiagnosticId::SqlViewNotPlainString, Vec::new()),
                        DiagnosticId::HintSqlViewNotPlainStringLiteral,
                        Vec::new(),
                    ));
                    String::new()
                }
            } else if let Some(s) = eval_static_sql_string(e, &[], named) {
                s
            } else {
                if std::env::var("URWEB_DEBUG_CJR_SQL").ok().as_deref() == Some("1") {
                    eprintln!("cjrize view unsupported expr={:#?}", e);
                }
                errors.report(CompileError::sql_at_with_hint(
                    e.span.clone(),
                    DiagnosticPayload::new(DiagnosticId::SqlViewNotPlainString, Vec::new()),
                    DiagnosticId::HintSqlViewNotPlainStringLiteral,
                    Vec::new(),
                ));
                String::new()
            };
            (
                Some(Located::new(Decl::View(name.clone(), cxts, sql), loc)),
                None,
            )
        }

        mono::Decl::Index(table, cols) => (
            Some(Located::new(Decl::Index(table.clone(), cols.clone()), loc)),
            None,
        ),

        mono::Decl::Database {
            name,
            expunge,
            initialize,
            uses_similar,
        } => (
            Some(Located::new(
                Decl::Database {
                    name: name.clone(),
                    expunge: *expunge,
                    initialize: *initialize,
                    uses_similar: *uses_similar,
                },
                loc,
            )),
            None,
        ),

        mono::Decl::JavaScript(s) => (Some(Located::new(Decl::JavaScript(s.clone()), loc)), None),
        mono::Decl::Cookie(name) => (Some(Located::new(Decl::Cookie(name.clone()), loc)), None),
        mono::Decl::Style(name) => (Some(Located::new(Decl::Style(name.clone()), loc)), None),

        mono::Decl::Task(e1, e2) => {
            // e2 must be EAbs(x1, _, _, EAbs(x2, _, _, body))
            match &e2.node {
                mono::Exp::Abs(x1, _, _, inner) => match &inner.node {
                    mono::Exp::Abs(x2, _, _, body) => {
                        let tk = match &e1.node {
                            mono::Exp::Ffi(m, x) if m == "Basis" && x == "initialize" => {
                                Task::Initialize
                            }
                            mono::Exp::Ffi(m, x) if m == "Basis" && x == "clientLeaves" => {
                                Task::ClientLeaves
                            }
                            mono::Exp::FfiApp(m, x, args)
                                if m == "Basis" && x == "periodic" && args.len() == 1 =>
                            {
                                match &args[0].0.node {
                                    mono::Exp::Prim(Prim::Int(n)) => Task::Periodic(*n),
                                    _ => {
                                        errors.report_at(
                                            e1.span.clone(),
                                            DiagnosticPayload::new(
                                                DiagnosticId::CjrizeTaskKindNotFullyDetermined,
                                                Vec::new(),
                                            ),
                                        );
                                        Task::Initialize
                                    }
                                }
                            }
                            _ => {
                                errors.report_at(
                                    e1.span.clone(),
                                    DiagnosticPayload::new(
                                        DiagnosticId::CjrizeTaskKindNotFullyDetermined,
                                        Vec::new(),
                                    ),
                                );
                                Task::Initialize
                            }
                        };
                        let cbody = cify_exp(body, sm, errors);
                        (
                            Some(Located::new(
                                Decl::Task(tk, x1.clone(), x2.clone(), cbody),
                                loc,
                            )),
                            None,
                        )
                    }
                    _ => {
                        errors.report_at(
                            loc.clone(),
                            DiagnosticPayload::new(
                                DiagnosticId::CjrizeInitializerNotFullyDetermined,
                                Vec::new(),
                            ),
                        );
                        (None, None)
                    }
                },
                _ => {
                    errors.report_at(
                        loc.clone(),
                        DiagnosticPayload::new(
                            DiagnosticId::CjrizeInitializerNotFullyDetermined,
                            Vec::new(),
                        ),
                    );
                    (None, None)
                }
            }
        }

        // Policy declarations are dropped at CJR level.
        mono::Decl::Policy(_) => (None, None),

        mono::Decl::OnError(n) => (Some(Located::new(Decl::OnError(*n), loc)), None),
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Convert a Mono file to a CJR file.
///
/// Mirrors `Cjrize.cjrize`.
pub fn cjrize(file: mono::File, errors: &mut ErrorReporter) -> Option<cjr::File> {
    #[cfg(test)]
    cjrize_test_reset_ticks();
    let (mono_decls, mono_ps) = file;
    let mut sm = Sm::new();
    // dsf = "front" declarations: struct defs, type forward decls, datatypes
    let mut dsf: Vec<LocDecl> = Vec::new();
    // ds = regular declarations
    let mut ds: Vec<LocDecl> = Vec::new();
    // export entries (without sidedness — to be filled from mono_ps)
    let mut ps_raw: Vec<(ExportKind, String, usize, Vec<LocTyp>, LocTyp, bool)> = Vec::new();
    let mut named: HashMap<usize, mono::LocExp> = HashMap::new();

    for mono_decl in &mono_decls {
        if let mono::Decl::Val(_, n, _, e, _) = &mono_decl.node {
            named.insert(*n, e.clone());
        }
    }

    for mono_decl in &mono_decls {
        let (dop, pop) = cify_decl(mono_decl, &mut sm, errors, &named);

        // Emit struct declarations accumulated so far.
        for (id, fields) in sm.drain_decls() {
            dsf.push(Located::new(Decl::Struct(id, fields), Span::dummy()));
        }

        // Distribute the translated declaration.
        match dop {
            None => {}
            Some(d) => {
                match &d.node {
                    Decl::Datatype(dts) => {
                        // Emit forward declarations first.
                        for dt in dts {
                            dsf.push(Located::new(
                                Decl::DatatypeForward(dt.kind, dt.name.clone(), dt.id),
                                d.span.clone(),
                            ));
                        }
                        // Then the datatype itself goes in dsf.
                        dsf.push(d);
                    }
                    _ => ds.push(d),
                }
            }
        }

        if let Some(p) = pop {
            ps_raw.push(p);
        }
    }

    // Build sidedness map from Mono ps.
    let side_map: HashMap<usize, (Sidedness, DbMode)> = mono_ps
        .iter()
        .map(|(n, side, db)| (*n, (*side, *db)))
        .collect();

    // Attach sidedness to each export entry.
    let ps: Vec<cjr::ExportEntry> = ps_raw
        .into_iter()
        .map(|(ek, path, n, ts, t, b)| {
            let (side, db) = side_map
                .get(&n)
                .copied()
                .unwrap_or((Sidedness::ServerOnly, DbMode::AnyDb));
            (ek, path, n, ts, t, side, db, b)
        })
        .collect();

    // Final output: front declarations followed by regular declarations.
    dsf.extend(ds);
    Some((dsf, ps))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_file_cjrizes_to_empty() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut errors = ErrorReporter::new();
        let result = cjrize((vec![], vec![]), &mut errors);
        assert!(result.is_some());
        let (decls, ps) = result.ok_or_else(|| anyhow::anyhow!("expected Some from result"))?; // convert None to anyhow error
        assert!(decls.is_empty());
        assert!(ps.is_empty());
        assert!(!errors.has_errors());
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sm_unit_struct_is_id_zero() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut sm = Sm::new();
        // Empty record → struct id 0
        let id = sm.find(&[], vec![]);
        assert_eq!(id, 0);
        // No decls emitted (already known)
        assert!(sm.drain_decls().is_empty());
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sm_new_struct_gets_fresh_id() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut sm = Sm::new();
        let span = Span::dummy();
        let t = Located::new(
            Typ::Ffi("Basis".to_string(), "int".to_string()),
            span.clone(),
        );
        let mt = Located::new(mono::Typ::Ffi("Basis".to_string(), "int".to_string()), span);
        let mono_fields = vec![("x".to_string(), mt)];
        let cjr_fields = vec![("x".to_string(), t)];
        let id = sm.find(&mono_fields, cjr_fields.clone());
        assert_eq!(id, 1); // first fresh id
                           // Idempotent
        let id2 = sm.find(&mono_fields, cjr_fields);
        assert_eq!(id2, 1);
        Ok(()) // return success to the test harness
    }

    #[test]
    fn typ_eq_fun_same() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let span = Span::dummy();
        let a = mono::Typ::Fun(
            Box::new(Located::new(mono::Typ::Source, span.clone())),
            Box::new(Located::new(mono::Typ::Source, span.clone())),
        );
        let b = mono::Typ::Fun(
            Box::new(Located::new(mono::Typ::Source, span.clone())),
            Box::new(Located::new(mono::Typ::Source, span)),
        );
        assert!(typ_eq(&a, &b), "same Fun types must be equal");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn typ_eq_fun_differ_domain() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let span = Span::dummy();
        let a = mono::Typ::Fun(
            Box::new(Located::new(mono::Typ::Source, span.clone())),
            Box::new(Located::new(mono::Typ::Source, span.clone())),
        );
        let b = mono::Typ::Fun(
            Box::new(Located::new(
                mono::Typ::Ffi("Basis".into(), "int".into()),
                span.clone(),
            )),
            Box::new(Located::new(mono::Typ::Source, span)),
        );
        assert!(
            !typ_eq(&a, &b),
            "Fun with different domain must not be equal"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn typ_eq_datatype_same_id() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let def = mono::DatatypeDef {
            kind: DatatypeKind::Default,
            constrs: vec![],
        };
        let r = Arc::new(Mutex::new(def));
        let a = mono::Typ::Datatype(5, r.clone());
        let b = mono::Typ::Datatype(5, r);
        assert!(typ_eq(&a, &b));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn typ_eq_datatype_different_id() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let def = mono::DatatypeDef {
            kind: DatatypeKind::Default,
            constrs: vec![],
        };
        let r = Arc::new(Mutex::new(def));
        let a = mono::Typ::Datatype(5, r.clone());
        let b = mono::Typ::Datatype(6, r);
        assert!(!typ_eq(&a, &b));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn typ_eq_ffi_same() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let a = mono::Typ::Ffi("Basis".into(), "int".into());
        let b = mono::Typ::Ffi("Basis".into(), "int".into());
        assert!(typ_eq(&a, &b));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn typ_eq_ffi_different_module() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let a = mono::Typ::Ffi("Basis".into(), "int".into());
        let b = mono::Typ::Ffi("Other".into(), "int".into());
        assert!(!typ_eq(&a, &b));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn typ_eq_source() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let a = mono::Typ::Source;
        let b = mono::Typ::Source;
        assert!(typ_eq(&a, &b));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn typ_eq_different_variants() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let a = mono::Typ::Source;
        let b = mono::Typ::Ffi("Basis".into(), "int".into());
        assert!(!typ_eq(&a, &b), "different variants must not be equal");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn record_fields_eq_same() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let span = Span::dummy();
        let t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span);
        let a = vec![("x".to_string(), t.clone())];
        let b = vec![("x".to_string(), t)];
        assert!(record_fields_eq(&a, &b));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn record_fields_eq_different_field_name() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let span = Span::dummy();
        let t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span);
        let a = vec![("x".to_string(), t.clone())];
        let b = vec![("y".to_string(), t)];
        assert!(!record_fields_eq(&a, &b));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn typ_eq_record_same() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let span = Span::dummy();
        let t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span);
        let a = mono::Typ::Record(vec![("x".into(), t.clone())]);
        let b = mono::Typ::Record(vec![("x".into(), t)]);
        assert!(typ_eq(&a, &b), "same Record types must be equal");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn typ_eq_record_different_field_type() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let span = Span::dummy();
        let t1 = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let t2 = Located::new(mono::Typ::Ffi("Basis".into(), "string".into()), span);
        let a = mono::Typ::Record(vec![("x".into(), t1)]);
        let b = mono::Typ::Record(vec![("x".into(), t2)]);
        assert!(
            !typ_eq(&a, &b),
            "Record with different field types must not be equal (catches && in record_fields_eq)"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn typ_eq_record_vs_option() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let span = Span::dummy();
        let t = Located::new(mono::Typ::Source, span);
        let rec = mono::Typ::Record(vec![]);
        let opt = mono::Typ::Option(Box::new(t));
        assert!(
            !typ_eq(&rec, &opt),
            "Record vs Option must not be equal (catches delete Record arm)"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn typ_eq_option_same() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let span = Span::dummy();
        let t = Located::new(mono::Typ::Source, span);
        let a = mono::Typ::Option(Box::new(t.clone()));
        let b = mono::Typ::Option(Box::new(t));
        assert!(typ_eq(&a, &b));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn typ_eq_list_same() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let span = Span::dummy();
        let t = Located::new(mono::Typ::Source, span);
        let a = mono::Typ::List(Box::new(t.clone()));
        let b = mono::Typ::List(Box::new(t));
        assert!(typ_eq(&a, &b));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn typ_eq_signal_same() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let span = Span::dummy();
        let t = Located::new(mono::Typ::Source, span);
        let a = mono::Typ::Signal(Box::new(t.clone()));
        let b = mono::Typ::Signal(Box::new(t));
        assert!(typ_eq(&a, &b));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sm_find_list_increments_count() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut sm = Sm::new();
        let span = Span::dummy();
        let elem_mono = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let elem_cjr = Located::new(Typ::Ffi("Basis".into(), "int".into()), span);
        let id = sm.find_list(&elem_mono, &elem_cjr);
        assert_eq!(id, 1, "find_list must use count (catches += mutant)");
        let id2 = sm.find_list(&elem_mono, &elem_cjr);
        assert_eq!(id2, 1, "same type must return same id");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn classify_constrs_enum() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let c: Vec<(String, usize, Option<LocTyp>)> =
            vec![("A".into(), 0, None), ("B".into(), 1, None)];
        assert_eq!(
            classify_constrs(&c),
            DatatypeKind::Enum,
            "all nullary => Enum (catches unary==0 check)"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn classify_constrs_option() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let unit = Located::dummy(Typ::Ffi("Basis".into(), "unit".into()));
        let c: Vec<(String, usize, Option<LocTyp>)> =
            vec![("None".into(), 0, None), ("Some".into(), 1, Some(unit))];
        assert_eq!(
            classify_constrs(&c),
            DatatypeKind::Option,
            "1 nullary && 1 unary => Option"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn classify_constrs_default() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let unit = Located::dummy(Typ::Ffi("Basis".into(), "unit".into()));
        let c: Vec<(String, usize, Option<LocTyp>)> = vec![
            ("A".into(), 0, None),
            ("B".into(), 0, None),
            ("C".into(), 1, Some(unit)),
        ];
        assert_eq!(
            classify_constrs(&c),
            DatatypeKind::Default,
            "2 nullary 1 unary => Default (catches nullary==1 && unary==1)"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn type_has_signal_direct() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let t = mono::Typ::Signal(Box::new(Located::dummy(mono::Typ::Source)));
        assert!(type_has_signal(&t), "Signal must have signal");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn type_has_signal_fun() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let inner = mono::Typ::Signal(Box::new(Located::dummy(mono::Typ::Source)));
        let t = mono::Typ::Fun(
            Box::new(Located::dummy(mono::Typ::Source)),
            Box::new(Located::new(inner, Span::dummy())),
        );
        assert!(
            type_has_signal(&t),
            "Fun with Signal in range must have signal (catches || mutant)"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn type_has_signal_record() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let inner = mono::Typ::Signal(Box::new(Located::dummy(mono::Typ::Source)));
        let t = mono::Typ::Record(vec![("x".into(), Located::new(inner, Span::dummy()))]);
        assert!(
            type_has_signal(&t),
            "Record with Signal field must have signal"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn type_has_signal_option_no_signal() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let t = mono::Typ::Option(Box::new(Located::dummy(mono::Typ::Source)));
        assert!(
            !type_has_signal(&t),
            "Option of Source must not have signal"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn type_has_signal_option_with_signal() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // Catches mutant: delete Typ::Option|List arm in type_has_signal.
        let inner = mono::Typ::Signal(Box::new(Located::dummy(mono::Typ::Source)));
        let t = mono::Typ::Option(Box::new(Located::new(inner, Span::dummy())));
        assert!(
            type_has_signal(&t),
            "Option containing Signal must have signal"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn cjrize_task_initialize_produces_task_decl() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let span = Span::dummy();
        let unit = Located::new(mono::Typ::Ffi("Basis".into(), "unit".into()), span.clone());
        let body = mono::Exp::Record(vec![]);
        let inner = mono::Exp::Abs(
            "_".into(),
            unit.clone(),
            unit.clone(),
            Box::new(Located::new(body, span.clone())),
        );
        let e2 = mono::Exp::Abs(
            "_".into(),
            unit.clone(),
            unit.clone(),
            Box::new(Located::new(inner, span.clone())),
        );
        let e1 = mono::Exp::Ffi("Basis".into(), "initialize".into());
        let decl = mono::Decl::Task(
            Located::new(e1, span.clone()),
            Located::new(e2, span.clone()),
        );
        let file: mono::File = (vec![Located::new(decl, span)], vec![]);
        let mut errors = ErrorReporter::new();
        let result = cjrize(file, &mut errors);
        assert!(result.is_some(), "cjrize must process Task (initialize)");
        assert!(!errors.has_errors());
        let (decls, _) = result.ok_or_else(|| anyhow::anyhow!("expected Some from result"))?; // convert None to anyhow error
        assert_eq!(decls.len(), 1);
        match &decls[0].node {
            Decl::Task(tk, ..) => {
                assert!(
                    matches!(tk, Task::Initialize),
                    "initialize => Task::Initialize (catches m==Basis, x==initialize)"
                );
            }
            _ => panic!("expected Decl::Task, got {:?}", decls[0].node),
        }
        Ok(()) // return success to the test harness
    }

    #[test]
    fn cjrize_task_client_leaves_produces_task_decl() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let span = Span::dummy();
        let unit = Located::new(mono::Typ::Ffi("Basis".into(), "unit".into()), span.clone());
        let body = mono::Exp::Record(vec![]);
        let inner = mono::Exp::Abs(
            "_".into(),
            unit.clone(),
            unit.clone(),
            Box::new(Located::new(body, span.clone())),
        );
        let e2 = mono::Exp::Abs(
            "_".into(),
            unit.clone(),
            unit.clone(),
            Box::new(Located::new(inner, span.clone())),
        );
        let e1 = mono::Exp::Ffi("Basis".into(), "clientLeaves".into());
        let decl = mono::Decl::Task(
            Located::new(e1, span.clone()),
            Located::new(e2, span.clone()),
        );
        let file: mono::File = (vec![Located::new(decl, span)], vec![]);
        let mut errors = ErrorReporter::new();
        let result = cjrize(file, &mut errors);
        assert!(result.is_some(), "cjrize must process Task (clientLeaves)");
        assert!(!errors.has_errors());
        let (decls, _) = result.ok_or_else(|| anyhow::anyhow!("expected Some from result"))?; // convert None to anyhow error
        assert_eq!(decls.len(), 1);
        match &decls[0].node {
            Decl::Task(tk, ..) => {
                assert!(
                    matches!(tk, Task::ClientLeaves),
                    "clientLeaves => Task::ClientLeaves (catches m==Basis, x==clientLeaves)"
                );
            }
            _ => panic!("expected Decl::Task, got {:?}", decls[0].node),
        }
        Ok(()) // return success to the test harness
    }

    #[test]
    fn cjrize_task_periodic_produces_periodic() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let span = Span::dummy();
        let unit = Located::new(mono::Typ::Ffi("Basis".into(), "unit".into()), span.clone());
        let body = mono::Exp::Record(vec![]);
        let inner = mono::Exp::Abs(
            "_".into(),
            unit.clone(),
            unit.clone(),
            Box::new(Located::new(body, span.clone())),
        );
        let e2 = mono::Exp::Abs(
            "_".into(),
            unit.clone(),
            unit.clone(),
            Box::new(Located::new(inner, span.clone())),
        );
        let int_ty = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let e1 = mono::Exp::FfiApp(
            "Basis".into(),
            "periodic".into(),
            vec![(
                Located::new(mono::Exp::Prim(Prim::Int(100)), span.clone()),
                int_ty,
            )],
        );
        let decl = mono::Decl::Task(
            Located::new(e1, span.clone()),
            Located::new(e2, span.clone()),
        );
        let file: mono::File = (vec![Located::new(decl, span)], vec![]);
        let mut errors = ErrorReporter::new();
        let result = cjrize(file, &mut errors);
        assert!(result.is_some(), "cjrize must process Task (periodic)");
        assert!(!errors.has_errors());
        let (decls, _) = result.ok_or_else(|| anyhow::anyhow!("expected Some from result"))?; // convert None to anyhow error
        assert_eq!(decls.len(), 1);
        match &decls[0].node {
            Decl::Task(tk, ..) => {
                assert!(
                    matches!(tk, Task::Periodic(100)),
                    "periodic(100) => Task::Periodic(100) (catches FfiApp arm, Prim::Int)"
                );
            }
            _ => panic!("expected Decl::Task, got {:?}", decls[0].node),
        }
        Ok(()) // return success to the test harness
    }

    #[test]
    fn cjrize_table_with_strcat_constraint() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let span = Span::dummy();
        let string_ty = Located::new(
            mono::Typ::Ffi("Basis".into(), "string".into()),
            span.clone(),
        );
        let r1 = mono::Exp::Record(vec![(
            "a".into(),
            Located::new(
                mono::Exp::Prim(Prim::String(StringMode::Normal, "val1".into())),
                span.clone(),
            ),
            string_ty.clone(),
        )]);
        let r2 = mono::Exp::Record(vec![(
            "b".into(),
            Located::new(
                mono::Exp::Prim(Prim::String(StringMode::Normal, "val2".into())),
                span.clone(),
            ),
            string_ty.clone(),
        )]);
        let ce = mono::Exp::Strcat(
            Box::new(Located::new(r1, span.clone())),
            Box::new(Located::new(r2, span.clone())),
        );
        let pe = mono::Exp::Prim(Prim::String(StringMode::Normal, "id".into()));
        let decl = mono::Decl::Table(
            "t".into(),
            vec![
                ("id".into(), string_ty.clone()),
                ("a".into(), string_ty.clone()),
                ("b".into(), string_ty),
            ],
            Located::new(pe, span.clone()),
            Located::new(ce, span.clone()),
        );
        let file: mono::File = (vec![Located::new(decl, span)], vec![]);
        let mut errors = ErrorReporter::new();
        let result = cjrize(file, &mut errors);
        assert!(
            result.is_some(),
            "cjrize must process Table with Strcat constraint"
        );
        assert!(!errors.has_errors());
        let (decls, _) = result.ok_or_else(|| anyhow::anyhow!("expected Some from result"))?; // convert None to anyhow error
        assert_eq!(decls.len(), 1);
        match &decls[0].node {
            Decl::Table(_, _, _, constraints) => {
                assert_eq!(
                    constraints.as_slice(),
                    &[("a".into(), "val1".into()), ("b".into(), "val2".into())],
                    "Strcat(Record(a=val1), Record(b=val2)) => both constraints (catches Strcat arm)"
                );
            }
            _ => panic!("expected Decl::Table, got {:?}", decls[0].node),
        }
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sm_find_idempotent_two_same_structs() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut sm = Sm::new();
        let span = Span::dummy();
        let t = Located::new(
            Typ::Ffi("Basis".to_string(), "int".to_string()),
            span.clone(),
        );
        let mt = Located::new(mono::Typ::Ffi("Basis".to_string(), "int".to_string()), span);
        let mono_fields = vec![("x".to_string(), mt.clone()), ("y".to_string(), mt)];
        let cjr_fields = vec![("x".to_string(), t.clone()), ("y".to_string(), t)];
        let id1 = sm.find(&mono_fields, cjr_fields.clone());
        let id2 = sm.find(&mono_fields, cjr_fields);
        assert_eq!(
            id1, id2,
            "Sm::find same struct twice => same id (catches += 1)"
        );
        assert_eq!(id1, 1, "first non-unit struct gets id 1");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn cjrize_datatype_produces_decl() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let decl = mono::Decl::Datatype(vec![mono::DatatypeDecl {
            name: "Color".into(),
            id: 10,
            constrs: vec![("Red".into(), 11, None), ("Blue".into(), 12, None)],
        }]);
        let file: mono::File = (vec![Located::dummy(decl)], vec![]);
        let mut errors = ErrorReporter::new();
        let result = cjrize(file, &mut errors);
        assert!(
            result.is_some(),
            "cjrize must process Datatype (catches delete Decl::Datatype arm)"
        );
        let (decls, _) = result.ok_or_else(|| anyhow::anyhow!("expected Some from result"))?; // convert None to anyhow error
        assert!(!decls.is_empty(), "cjrize must produce decl for Datatype");
        Ok(()) // return success to the test harness
    }
}
