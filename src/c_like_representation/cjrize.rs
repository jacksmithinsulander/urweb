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

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
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

thread_local! {
    static CJRIZE_NAMED_TYPES: RefCell<HashMap<usize, mono::LocTyp>> = RefCell::new(HashMap::new());
}

thread_local! {
    static CJRIZE_RAW_NAMED_TYPES: RefCell<HashMap<usize, mono::LocTyp>> =
        RefCell::new(HashMap::new());
}

thread_local! {
    static CJRIZE_REL_TYPES: RefCell<Vec<mono::LocTyp>> = const { RefCell::new(Vec::new()) };
}

thread_local! {
    static CJRIZE_CONSTRUCTOR_KINDS: RefCell<HashMap<usize, DatatypeKind>> =
        RefCell::new(HashMap::new());
}

thread_local! {
    static CJRIZE_CURRENT_DECL: RefCell<Option<String>> = const { RefCell::new(None) };
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

fn debug_chat_cjr_enabled() -> bool {
    std::env::var("URWEB_DEBUG_CHAT_CJR").ok().as_deref() == Some("1")
}

fn debug_chat_cjr(span: &Span, label: &str, detail: impl FnOnce() -> String) {
    if !debug_chat_cjr_enabled() || !span.file.ends_with("/demo/chat.ur") {
        return;
    }
    eprintln!(
        "URWEB_DEBUG_CHAT_CJR {label} {}:{} {}",
        span.file,
        span.first.line,
        detail()
    );
}

fn debug_cjr_field_enabled() -> bool {
    std::env::var("URWEB_DEBUG_CJR_FIELD").ok().as_deref() == Some("1")
}

fn debug_cjr_field_span(span: &Span) -> bool {
    debug_cjr_field_enabled()
        && (span.file.ends_with("/lib/ur/top.ur")
            || span.file.ends_with("/demo/metaform.ur")
            || span.file.ends_with("/demo/crud.ur")
            || span.file.ends_with("/demo/listFun.ur")
            || span.file.ends_with("/demo/refFun.ur")
            || span.file.ends_with("/demo/treeFun.ur"))
}

fn debug_cjr_field(span: &Span, label: &str, detail: impl FnOnce() -> String) {
    if !debug_cjr_field_span(span) {
        return;
    }
    let current_decl = CJRIZE_CURRENT_DECL.with(|slot| slot.borrow().clone());
    eprintln!(
        "URWEB_DEBUG_CJR_FIELD {label} decl={current_decl:?} {}:{} {}",
        span.file,
        span.first.line,
        detail()
    );
}

fn debug_cjr_lowered_enabled() -> bool {
    std::env::var("URWEB_DEBUG_CJR_LOWERED").ok().as_deref() == Some("1")
}

fn debug_cjr_lowered(span: &Span, label: &str, detail: impl FnOnce() -> String) {
    if !debug_cjr_lowered_enabled() {
        return;
    }
    eprintln!(
        "URWEB_DEBUG_CJR_LOWERED {label} {}:{} {}",
        span.file,
        span.first.line,
        detail()
    );
}

fn debug_cjr_top_lambda_enabled() -> bool {
    std::env::var("URWEB_DEBUG_CJR_TOP_LAMBDA").ok().as_deref() == Some("1")
}

fn debug_cjr_top_lambda(span: &Span, label: &str, detail: impl FnOnce() -> String) {
    if !debug_cjr_top_lambda_enabled()
        || !span.file.ends_with("/lib/ur/top.ur")
        || !matches!(
            span.first.line,
            137 | 138 | 139 | 140 | 156 | 157 | 158 | 159 | 160 | 161
        )
    {
        return;
    }
    eprintln!(
        "URWEB_DEBUG_CJR_TOP {label} {}:{} {}",
        span.file,
        span.first.line,
        detail()
    );
}

fn debug_cjr_pre_unravel_enabled() -> bool {
    std::env::var("URWEB_DEBUG_CJR_PRE_UNRAVEL").ok().as_deref() == Some("1")
}

fn debug_cjr_pre_unravel(span: &Span, label: &str, detail: impl FnOnce() -> String) {
    if !debug_cjr_pre_unravel_enabled()
        || !span.file.ends_with("/lib/ur/top.ur")
        || span.first.line != 156
    {
        return;
    }
    eprintln!(
        "URWEB_DEBUG_CJR_PRE_UNRAVEL {label} {}:{} {}",
        span.file,
        span.first.line,
        detail()
    );
}

fn with_current_decl<T>(label: String, f: impl FnOnce() -> T) -> T {
    CJRIZE_CURRENT_DECL.with(|slot| {
        let previous = slot.replace(Some(label));
        let out = f();
        slot.replace(previous);
        out
    })
}

fn with_rel_binder<T>(typ: mono::LocTyp, f: impl FnOnce() -> T) -> T {
    CJRIZE_REL_TYPES.with(|slot| {
        slot.borrow_mut().insert(0, typ);
        let out = f();
        slot.borrow_mut().remove(0);
        out
    })
}

fn with_rel_types<T>(types: Vec<mono::LocTyp>, f: impl FnOnce() -> T) -> T {
    CJRIZE_REL_TYPES.with(|slot| {
        let previous = slot.replace(types);
        let out = f();
        slot.replace(previous);
        out
    })
}

fn mono_pat_bound_types_into(pat: &mono::LocPat, out: &mut Vec<mono::LocTyp>) {
    match &pat.node {
        mono::Pat::Var(_, typ) => out.push(typ.clone()),
        mono::Pat::Prim(_) => {}
        mono::Pat::Con(_, _, Some(inner)) => mono_pat_bound_types_into(inner, out),
        mono::Pat::Con(_, _, None) => {}
        mono::Pat::Record(fields) => {
            for (_, inner, _) in fields {
                mono_pat_bound_types_into(inner, out);
            }
        }
        mono::Pat::None(_) => {}
        mono::Pat::Some(_, inner) => mono_pat_bound_types_into(inner, out),
    }
}

fn with_rel_pattern_binders<T>(pat: &mono::LocPat, f: impl FnOnce() -> T) -> T {
    let mut bound_types = Vec::new();
    mono_pat_bound_types_into(pat, &mut bound_types);
    CJRIZE_REL_TYPES.with(|slot| {
        for typ in &bound_types {
            slot.borrow_mut().insert(0, typ.clone());
        }
        let out = f();
        for _ in 0..bound_types.len() {
            slot.borrow_mut().remove(0);
        }
        out
    })
}

fn debug_validate_named_enabled() -> bool {
    std::env::var("URWEB_DEBUG_CJR_VALIDATE").ok().as_deref() == Some("1")
}

fn debug_validate_named_span(span: &Span) -> bool {
    span.file.ends_with("/demo/listFun.ur") || span.file.ends_with("/demo/listShop.ur")
}

fn collect_cjr_bound_named_ids(decls: &[LocDecl]) -> HashSet<usize> {
    let mut bound = HashSet::new();
    for decl in decls {
        match &decl.node {
            Decl::Val(_, n, _, _) | Decl::Fun(_, n, _, _, _) => {
                bound.insert(*n);
            }
            Decl::FunRec(vis) => {
                for (_, n, _, _, _) in vis {
                    bound.insert(*n);
                }
            }
            _ => {}
        }
    }
    bound
}

fn collect_mono_bound_named_ids(decls: &[mono::LocDecl]) -> HashSet<usize> {
    let mut bound = HashSet::new();
    for decl in decls {
        match &decl.node {
            mono::Decl::Val(_, n, _, _, _) => {
                bound.insert(*n);
            }
            mono::Decl::ValRec(vis) => {
                for (_, n, _, _, _) in vis {
                    bound.insert(*n);
                }
            }
            _ => {}
        }
    }
    bound
}

fn debug_validate_cjr_named_refs(decls: &[LocDecl], mono_bound: &HashSet<usize>) {
    fn visit_exp(
        exp: &LocExp,
        label: &str,
        bound: &HashSet<usize>,
        mono_bound: &HashSet<usize>,
        seen: &mut HashSet<(String, usize, usize, usize)>,
    ) {
        if let Exp::Named(n) = &exp.node {
            if !bound.contains(n) && debug_validate_named_span(&exp.span) {
                let key = (
                    label.to_string(),
                    *n,
                    exp.span.first.line as usize,
                    exp.span.first.col as usize,
                );
                if seen.insert(key) {
                    eprintln!(
                        "URWEB_DEBUG_CJR_VALIDATE missing named id={} in_mono={} decl={} {}:{} expr={:?}",
                        n,
                        mono_bound.contains(n),
                        label,
                        exp.span.file,
                        exp.span.first.line,
                        exp.node
                    );
                }
            }
        }

        match &exp.node {
            Exp::Prim(_) | Exp::Rel(_) | Exp::Named(_) | Exp::Ffi(_, _) | Exp::None(_) => {}
            Exp::Con(_, _, arg) => {
                if let Some(arg) = arg.as_deref() {
                    visit_exp(arg, label, bound, mono_bound, seen);
                }
            }
            Exp::Some(_, inner)
            | Exp::Unop(_, inner)
            | Exp::Field(inner, _)
            | Exp::Error(inner, _)
            | Exp::Write(inner)
            | Exp::Redirect(inner, _)
            | Exp::Uurlify(inner, _, _) => visit_exp(inner, label, bound, mono_bound, seen),
            Exp::FfiApp(_, _, args) => {
                for (arg, _) in args {
                    visit_exp(arg, label, bound, mono_bound, seen);
                }
            }
            Exp::App(left, right) => {
                visit_exp(left, label, bound, mono_bound, seen);
                for arg in right {
                    visit_exp(arg, label, bound, mono_bound, seen);
                }
            }
            Exp::Binop(_, left, right) | Exp::Seq(left, right) | Exp::Let(_, _, left, right) => {
                visit_exp(left, label, bound, mono_bound, seen);
                visit_exp(right, label, bound, mono_bound, seen);
            }
            Exp::Record(_, fields) => {
                for (_, inner) in fields {
                    visit_exp(inner, label, bound, mono_bound, seen);
                }
            }
            Exp::Case(disc, arms, _) => {
                visit_exp(disc, label, bound, mono_bound, seen);
                for (_, arm) in arms {
                    visit_exp(arm, label, bound, mono_bound, seen);
                }
            }
            Exp::Query(meta) => {
                visit_exp(&meta.query, label, bound, mono_bound, seen);
                visit_exp(&meta.body, label, bound, mono_bound, seen);
                visit_exp(&meta.initial, label, bound, mono_bound, seen);
            }
            Exp::Dml(meta) => {
                visit_exp(&meta.dml, label, bound, mono_bound, seen);
            }
            Exp::Nextval { seq, .. } => {
                visit_exp(seq, label, bound, mono_bound, seen);
            }
            Exp::Setval { seq, count } => {
                visit_exp(seq, label, bound, mono_bound, seen);
                visit_exp(count, label, bound, mono_bound, seen);
            }
            Exp::ReturnBlob {
                blob, mime_type, ..
            } => {
                if let Some(blob) = blob.as_deref() {
                    visit_exp(blob, label, bound, mono_bound, seen);
                }
                visit_exp(mime_type, label, bound, mono_bound, seen);
            }
        }
    }

    let mut seen = HashSet::new();
    let bound = collect_cjr_bound_named_ids(decls);
    for decl in decls {
        match &decl.node {
            Decl::Val(x, n, _, exp) => {
                visit_exp(exp, &format!("val:{x}:{n}"), &bound, mono_bound, &mut seen);
            }
            Decl::Fun(x, n, _, _, exp) => {
                visit_exp(exp, &format!("fun:{x}:{n}"), &bound, mono_bound, &mut seen);
            }
            Decl::FunRec(vis) => {
                for (x, n, _, _, exp) in vis {
                    visit_exp(
                        exp,
                        &format!("funrec:{x}:{n}"),
                        &bound,
                        mono_bound,
                        &mut seen,
                    );
                }
            }
            _ => {}
        }
    }
}

fn contains_debug_show_option_abs(exp: &mono::LocExp) -> bool {
    let loc = &exp.span;
    if loc.file.ends_with("/lib/ur/top.ur")
        && loc.first.line == 76
        && matches!(exp.node, mono::Exp::Abs(_, _, _, _))
    {
        return true;
    }

    match &exp.node {
        mono::Exp::Prim(_) | mono::Exp::Rel(_) | mono::Exp::Named(_) | mono::Exp::Ffi(_, _) => {
            false
        }
        mono::Exp::Con(_, _, arg) => arg.as_deref().is_some_and(contains_debug_show_option_abs),
        mono::Exp::None(_) => false,
        mono::Exp::Some(_, inner)
        | mono::Exp::Abs(_, _, _, inner)
        | mono::Exp::Unop(_, inner)
        | mono::Exp::Field(inner, _)
        | mono::Exp::Error(inner, _)
        | mono::Exp::Redirect(inner, _)
        | mono::Exp::Write(inner)
        | mono::Exp::Dml(inner, _)
        | mono::Exp::Nextval(inner)
        | mono::Exp::Uurlify(inner, _, _)
        | mono::Exp::JavaScript(_, inner)
        | mono::Exp::SignalReturn(inner)
        | mono::Exp::SignalSource(inner)
        | mono::Exp::Recv(inner, _)
        | mono::Exp::Sleep(inner)
        | mono::Exp::Spawn(inner) => contains_debug_show_option_abs(inner),
        mono::Exp::FfiApp(_, _, args) => args
            .iter()
            .any(|(arg, _)| contains_debug_show_option_abs(arg)),
        mono::Exp::App(left, right)
        | mono::Exp::Binop(_, _, left, right)
        | mono::Exp::Strcat(left, right)
        | mono::Exp::Seq(left, right)
        | mono::Exp::Let(_, _, left, right)
        | mono::Exp::SignalBind(left, right) => {
            contains_debug_show_option_abs(left) || contains_debug_show_option_abs(right)
        }
        mono::Exp::ServerCall(left, _, _, _) => contains_debug_show_option_abs(left),
        mono::Exp::Record(fields) => fields
            .iter()
            .any(|(_, inner, _)| contains_debug_show_option_abs(inner)),
        mono::Exp::Case(disc, arms, _) => {
            contains_debug_show_option_abs(disc)
                || arms
                    .iter()
                    .any(|(_, arm)| contains_debug_show_option_abs(arm))
        }
        mono::Exp::ReturnBlob {
            blob, mime_type, ..
        } => {
            blob.as_deref().is_some_and(contains_debug_show_option_abs)
                || contains_debug_show_option_abs(mime_type)
        }
        mono::Exp::Closure(_, envs) => envs.iter().any(contains_debug_show_option_abs),
        mono::Exp::Query(meta) => {
            contains_debug_show_option_abs(&meta.query)
                || contains_debug_show_option_abs(&meta.body)
                || contains_debug_show_option_abs(&meta.initial)
        }
        mono::Exp::Setval(left, right) => {
            contains_debug_show_option_abs(left) || contains_debug_show_option_abs(right)
        }
    }
}

fn debug_show_option_path(exp: &mono::LocExp) -> Option<Vec<String>> {
    let loc = &exp.span;
    if loc.file.ends_with("/lib/ur/top.ur")
        && loc.first.line == 76
        && matches!(exp.node, mono::Exp::Abs(_, _, _, _))
    {
        return Some(vec!["Abs(top.ur:76 show_option body)".to_string()]);
    }

    match &exp.node {
        mono::Exp::Prim(_) | mono::Exp::Rel(_) | mono::Exp::Named(_) | mono::Exp::Ffi(_, _) => None,
        mono::Exp::Con(_, _, arg) => {
            arg.as_deref()
                .and_then(debug_show_option_path)
                .map(|mut path| {
                    path.insert(0, "Con(arg)".to_string());
                    path
                })
        }
        mono::Exp::None(_) => None,
        mono::Exp::Some(_, inner) => debug_show_option_path(inner).map(|mut path| {
            path.insert(0, "Some(value)".to_string());
            path
        }),
        mono::Exp::Abs(_, _, _, inner)
        | mono::Exp::Unop(_, inner)
        | mono::Exp::Field(inner, _)
        | mono::Exp::Error(inner, _)
        | mono::Exp::Redirect(inner, _)
        | mono::Exp::Write(inner)
        | mono::Exp::Dml(inner, _)
        | mono::Exp::Nextval(inner)
        | mono::Exp::Uurlify(inner, _, _)
        | mono::Exp::JavaScript(_, inner)
        | mono::Exp::SignalReturn(inner)
        | mono::Exp::SignalSource(inner)
        | mono::Exp::Recv(inner, _)
        | mono::Exp::Sleep(inner)
        | mono::Exp::Spawn(inner) => debug_show_option_path(inner).map(|mut path| {
            let label = match &exp.node {
                mono::Exp::Abs(_, _, _, _) => "Abs(body)",
                mono::Exp::Unop(_, _) => "Unop(inner)",
                mono::Exp::Field(_, field) => {
                    return {
                        path.insert(0, format!("Field({field})"));
                        path
                    }
                }
                mono::Exp::Error(_, _) => "Error(inner)",
                mono::Exp::Redirect(_, _) => "Redirect(inner)",
                mono::Exp::Write(_) => "Write(inner)",
                mono::Exp::Dml(_, _) => "Dml(inner)",
                mono::Exp::Nextval(_) => "Nextval(inner)",
                mono::Exp::Uurlify(_, _, _) => "Uurlify(inner)",
                mono::Exp::JavaScript(_, _) => "JavaScript(inner)",
                mono::Exp::SignalReturn(_) => "SignalReturn(inner)",
                mono::Exp::SignalSource(_) => "SignalSource(inner)",
                mono::Exp::Recv(_, _) => "Recv(inner)",
                mono::Exp::Sleep(_) => "Sleep(inner)",
                mono::Exp::Spawn(_) => "Spawn(inner)",
                _ => unreachable!("covered above"),
            };
            path.insert(0, label.to_string());
            path
        }),
        mono::Exp::FfiApp(module, name, args) => {
            args.iter().enumerate().find_map(|(idx, (arg, _))| {
                debug_show_option_path(arg).map(|mut path| {
                    path.insert(0, format!("FfiApp({module}.{name}) arg#{idx}"));
                    path
                })
            })
        }
        mono::Exp::App(left, right)
        | mono::Exp::Binop(_, _, left, right)
        | mono::Exp::Strcat(left, right)
        | mono::Exp::Seq(left, right)
        | mono::Exp::Let(_, _, left, right)
        | mono::Exp::SignalBind(left, right) => debug_show_option_path(left)
            .map(|mut path| {
                let label = match &exp.node {
                    mono::Exp::App(_, _) => "App(fn)",
                    mono::Exp::Binop(_, _, _, _) => "Binop(left)",
                    mono::Exp::Strcat(_, _) => "Strcat(left)",
                    mono::Exp::Seq(_, _) => "Seq(first)",
                    mono::Exp::Let(name, _, _, _) => {
                        path.insert(0, format!("Let({name}) bound"));
                        return path;
                    }
                    mono::Exp::SignalBind(_, _) => "SignalBind(left)",
                    _ => unreachable!("covered above"),
                };
                path.insert(0, label.to_string());
                path
            })
            .or_else(|| {
                debug_show_option_path(right).map(|mut path| {
                    let label = match &exp.node {
                        mono::Exp::App(_, _) => "App(arg)",
                        mono::Exp::Binop(_, _, _, _) => "Binop(right)",
                        mono::Exp::Strcat(_, _) => "Strcat(right)",
                        mono::Exp::Seq(_, _) => "Seq(second)",
                        mono::Exp::Let(name, _, _, _) => {
                            path.insert(0, format!("Let({name}) body"));
                            return path;
                        }
                        mono::Exp::SignalBind(_, _) => "SignalBind(right)",
                        _ => unreachable!("covered above"),
                    };
                    path.insert(0, label.to_string());
                    path
                })
            }),
        mono::Exp::ServerCall(left, _, _, _) => debug_show_option_path(left).map(|mut path| {
            path.insert(0, "ServerCall(fn)".to_string());
            path
        }),
        mono::Exp::Record(fields) => fields.iter().find_map(|(name, inner, _)| {
            debug_show_option_path(inner).map(|mut path| {
                path.insert(0, format!("Record(field {name})"));
                path
            })
        }),
        mono::Exp::Case(disc, arms, _) => debug_show_option_path(disc)
            .map(|mut path| {
                path.insert(0, "Case(discriminant)".to_string());
                path
            })
            .or_else(|| {
                arms.iter().enumerate().find_map(|(idx, (_, arm))| {
                    debug_show_option_path(arm).map(|mut path| {
                        path.insert(0, format!("Case(arm {idx})"));
                        path
                    })
                })
            }),
        mono::Exp::ReturnBlob {
            blob, mime_type, ..
        } => blob
            .as_deref()
            .and_then(debug_show_option_path)
            .map(|mut path| {
                path.insert(0, "ReturnBlob(blob)".to_string());
                path
            })
            .or_else(|| {
                debug_show_option_path(mime_type).map(|mut path| {
                    path.insert(0, "ReturnBlob(mime_type)".to_string());
                    path
                })
            }),
        mono::Exp::Closure(_, envs) => envs.iter().enumerate().find_map(|(idx, inner)| {
            debug_show_option_path(inner).map(|mut path| {
                path.insert(0, format!("Closure(env {idx})"));
                path
            })
        }),
        mono::Exp::Query(meta) => debug_show_option_path(&meta.query)
            .map(|mut path| {
                path.insert(0, "Query(sql)".to_string());
                path
            })
            .or_else(|| {
                debug_show_option_path(&meta.body).map(|mut path| {
                    path.insert(0, "Query(body)".to_string());
                    path
                })
            })
            .or_else(|| {
                debug_show_option_path(&meta.initial).map(|mut path| {
                    path.insert(0, "Query(initial)".to_string());
                    path
                })
            }),
        mono::Exp::Setval(left, right) => debug_show_option_path(left)
            .map(|mut path| {
                path.insert(0, "Setval(left)".to_string());
                path
            })
            .or_else(|| {
                debug_show_option_path(right).map(|mut path| {
                    path.insert(0, "Setval(right)".to_string());
                    path
                })
            }),
    }
}

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

fn cjr_typ_eq(a: &Typ, b: &Typ) -> bool {
    match (a, b) {
        (Typ::Fun(a_dom, a_ran), Typ::Fun(b_dom, b_ran)) => {
            cjr_typ_eq(&a_dom.node, &b_dom.node) && cjr_typ_eq(&a_ran.node, &b_ran.node)
        }
        (Typ::Record(a_id), Typ::Record(b_id)) => a_id == b_id,
        (Typ::Datatype(_, a_id, _), Typ::Datatype(_, b_id, _)) => a_id == b_id,
        (Typ::Ffi(a_mod, a_name), Typ::Ffi(b_mod, b_name)) => a_mod == b_mod && a_name == b_name,
        (Typ::Option(a_inner), Typ::Option(b_inner)) => cjr_typ_eq(&a_inner.node, &b_inner.node),
        (Typ::List(a_inner, a_id), Typ::List(b_inner, b_id)) => {
            a_id == b_id && cjr_typ_eq(&a_inner.node, &b_inner.node)
        }
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
            if sorted.len() == 2 && sorted[0].0 == "1" && sorted[1].0 == "2" {
                if let Typ::List(inner, list_id) = &cjr_fields[1].1.node {
                    if cjr_typ_eq(&cjr_fields[0].1.node, &inner.node) {
                        return Located::new(Typ::Record(*list_id), loc);
                    }
                }
            }
            let id = sm.find(&sorted, cjr_fields);
            Located::new(Typ::Record(id), loc)
        }
        mono::Typ::Datatype(n, r) => {
            let constrs = {
                let guard = crate::compiler_diagnostics::lock_for_compile(
                    r.as_ref(),
                    "cjrize translation cell",
                );
                guard.constrs.clone()
            };
            if let Some(head) = mono_exact_list_element(*n, &constrs) {
                let c_head = cify_typ_dtmap(head, sm, dtmap);
                let id = sm.find_list(head, &c_head);
                return Located::new(Typ::List(Box::new(c_head), id), loc);
            }
            if let Some(r_cjr) = dtmap.get(n) {
                return Located::new(Typ::Datatype(DatatypeKind::Default, *n, r_cjr.clone()), loc);
            }
            let r_cjr: cjr::DatatypeRef = Arc::new(Mutex::new(vec![]));
            dtmap.insert(*n, r_cjr.clone());
            let kind = classify_constrs(*n, &constrs);
            let translated: Vec<(String, usize, Option<LocTyp>)> = constrs
                .iter()
                .map(|(x, cn, to)| {
                    let ct = to.as_ref().map(|t| cify_typ_dtmap(t, sm, dtmap));
                    (x.clone(), *cn, ct)
                })
                .collect();
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

fn mono_exact_list_element<'a>(
    datatype_id: usize,
    constrs: &'a [(String, usize, Option<mono::LocTyp>)],
) -> Option<&'a mono::LocTyp> {
    if constrs.len() != 2 {
        return None;
    }

    let has_nil = constrs
        .iter()
        .any(|(name, _, payload)| name == "Nil" && payload.is_none());
    let cons_payload = constrs.iter().find_map(|(name, _, payload)| {
        if name == "Cons" {
            payload.as_ref()
        } else {
            None
        }
    })?;

    let mono::Typ::Record(fields) = &cons_payload.node else {
        return None;
    };

    let mut head = None;
    let mut tail = None;
    for (name, field_t) in fields {
        match name.as_str() {
            "1" => head = Some(field_t),
            "2" => tail = Some(field_t),
            _ => {}
        }
    }

    let head = head?;
    let tail = tail?;
    (has_nil && mono_typ_mentions_datatype_id(tail, datatype_id)).then_some(head)
}

fn mono_typ_mentions_datatype_id(t: &mono::LocTyp, datatype_id: usize) -> bool {
    match &t.node {
        mono::Typ::Fun(dom, ran) => {
            mono_typ_mentions_datatype_id(dom, datatype_id)
                || mono_typ_mentions_datatype_id(ran, datatype_id)
        }
        mono::Typ::Record(fields) => fields
            .iter()
            .any(|(_, field_t)| mono_typ_mentions_datatype_id(field_t, datatype_id)),
        mono::Typ::Datatype(id, _) => *id == datatype_id,
        mono::Typ::Ffi(..) | mono::Typ::Source => false,
        mono::Typ::Option(inner)
        | mono::Typ::List(inner)
        | mono::Typ::Signal(inner)
        | mono::Typ::Transaction(inner) => mono_typ_mentions_datatype_id(inner, datatype_id),
    }
}

fn classify_constrs(
    datatype_id: usize,
    constrs: &[(String, usize, Option<mono::LocTyp>)],
) -> DatatypeKind {
    let nullary = constrs.iter().filter(|(_, _, o)| o.is_none()).count();
    let unary = constrs.iter().filter(|(_, _, o)| o.is_some()).count();
    if unary == 0 {
        DatatypeKind::Enum
    } else if nullary == 1
        && unary == 1
        && !constrs
            .iter()
            .filter_map(|(_, _, arg)| arg.as_ref())
            .any(|arg| mono_typ_mentions_datatype_id(arg, datatype_id))
    {
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

fn normalize_datatype_kind(kind: DatatypeKind, pat_con: &mono::PatCon) -> DatatypeKind {
    match pat_con {
        mono::PatCon::Var(constructor_id) => CJRIZE_CONSTRUCTOR_KINDS
            .with(|slot| slot.borrow().get(constructor_id).copied().unwrap_or(kind)),
        mono::PatCon::Ffi { .. } => kind,
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
            Located::new(Pat::Con(normalize_datatype_kind(*dk, pc), cpc, cp), loc)
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
    crate::monomorphized::environment::lift_exp_in_exp(depth, &e)
}

fn mono_expr_result_typ_for_eta(e: &mono::LocExp) -> Option<mono::LocTyp> {
    match &e.node {
        mono::Exp::Named(n) | mono::Exp::Closure(n, _) => {
            CJRIZE_RAW_NAMED_TYPES.with(|slot| slot.borrow().get(n).cloned())
        }
        mono::Exp::Abs(_, dom, ran, _) => Some(Located::new(
            mono::Typ::Fun(Box::new(dom.clone()), Box::new(ran.clone())),
            e.span.clone(),
        )),
        mono::Exp::App(_, _) => {
            let (head, args) = strip_mono_app_spine(e.clone());
            let head_typ = mono_expr_result_typ_for_eta(&head)?;
            mono_drop_applied_result_typ(&head_typ, &args)
        }
        mono::Exp::Field(inner, field) => {
            mono_expr_result_typ_for_eta(inner).and_then(|t| projected_field_result_typ(&t, field))
        }
        mono::Exp::Let(_, _, _, body) => mono_expr_result_typ_for_eta(body),
        _ => None,
    }
}

fn rebuild_decl_fun_type_from_exp(exp: &mono::LocExp) -> Option<mono::LocTyp> {
    match &exp.node {
        mono::Exp::Abs(_, dom, ran, body) => {
            let refreshed_ran = rebuild_decl_fun_type_from_exp(body).unwrap_or_else(|| ran.clone());
            Some(Located::new(
                mono::Typ::Fun(Box::new(dom.clone()), Box::new(refreshed_ran)),
                exp.span.clone(),
            ))
        }
        mono::Exp::Let(_, _, _, body) => rebuild_decl_fun_type_from_exp(body),
        _ => None,
    }
}

fn refresh_decl_type_from_exp(fallback: mono::LocTyp, exp: &mono::LocExp) -> mono::LocTyp {
    rebuild_decl_fun_type_from_exp(exp).unwrap_or(fallback)
}

fn mono_exp_needs_transaction_eta(e: &mono::LocExp) -> bool {
    if let Some(result_typ) = mono_expr_result_typ_for_eta(e) {
        return matches!(&result_typ.node, mono::Typ::Transaction(_));
    }

    match &e.node {
        mono::Exp::Named(_)
        | mono::Exp::Rel(_)
        | mono::Exp::Closure(_, _)
        | mono::Exp::Field(_, _) => true,
        mono::Exp::App(head, _) => mono_exp_needs_transaction_eta(head),
        mono::Exp::Let(_, _, _, body) => mono_exp_needs_transaction_eta(body),
        _ => false,
    }
}

/// Unravel a (CJR type, Mono expression) pair into function arguments + body.
///
/// For each `TFun(dom, ran)` layer, if the expression is `EAbs(x, _, _, body)`,
/// we peel the lambda. Otherwise we eta-expand.
///
/// Returns `(args, return_cjr_type, mono_body_to_cify)`.
fn unravel_fun_full(
    mono_t: mono::LocTyp,
    cjr_t: LocTyp,
    e: mono::LocExp,
    loc: &Span,
    sm: &mut Sm,
    args: &mut Vec<(String, LocTyp)>,
    mono_args: &mut Vec<mono::LocTyp>,
) -> (mono::LocTyp, LocTyp, mono::LocExp) {
    cjrize_test_tick();
    debug_chat_cjr(loc, "unravel", || {
        format!(
            "mono_t={:?} cjr_t={:?} exp={:?} args_so_far={:?}",
            mono_t.node, cjr_t.node, e.node, args
        )
    });
    const MAX_UNRAVEL: usize = 65_536;
    if args.len() >= MAX_UNRAVEL {
        return (mono_t, cjr_t, e);
    }
    match (mono_t.node.clone(), cjr_t.node.clone()) {
        (mono::Typ::Fun(mono_dom, mono_ran), Typ::Fun(dom, ran)) => match e.node {
            mono::Exp::Abs(ax, _, _, body) => {
                args.push((ax, *dom));
                mono_args.push(*mono_dom);
                unravel_fun_full(*mono_ran, *ran, *body, loc, sm, args, mono_args)
            }
            _ => {
                // Eta-expand explicit function layers that are still represented
                // as values. Even when the range eventually becomes a
                // transaction, a non-Abs expression here still denotes a
                // function value (for instance a named helper), so we must
                // apply the reified binder before unraveling the remaining
                // transaction thunk.
                let lifted = lift_mono_exp(0, e);
                let app = Located::new(
                    mono::Exp::App(
                        Box::new(lifted),
                        Box::new(Located::new(mono::Exp::Rel(0), loc.clone())),
                    ),
                    loc.clone(),
                );
                args.push(("x".to_string(), *dom));
                mono_args.push(*mono_dom);
                unravel_fun_full(*mono_ran, *ran, app, loc, sm, args, mono_args)
            }
        },
        (mono::Typ::Transaction(mono_ran), Typ::Fun(dom, ran)) => match e.node {
            mono::Exp::Abs(ax, abs_dom, abs_ran, body)
                if matches!(
                    &abs_ran.node,
                    mono::Typ::Fun(_, _) | mono::Typ::Transaction(_)
                ) =>
            {
                let cdom = cify_typ(&abs_dom, sm);
                let cjr_t = Located::new(Typ::Fun(dom.clone(), ran.clone()), loc.clone());
                args.push((ax, cdom));
                mono_args.push(abs_dom);
                unravel_fun_full(abs_ran, cjr_t, *body, loc, sm, args, mono_args)
            }
            mono::Exp::Abs(ax, abs_dom, _, body) => {
                args.push((ax, *dom));
                mono_args.push(abs_dom);
                unravel_fun_full(*mono_ran, *ran, *body, loc, sm, args, mono_args)
            }
            _ => {
                // Mono transactions are implicit thunks. Direct bodies like
                // DML/Query/Case should stay as bodies under the reified unit
                // binder, but named/app/field expressions at this point still
                // denote thunk values and need the unit argument applied.
                let lifted = lift_mono_exp(0, e.clone());
                let body = if mono_exp_needs_transaction_eta(&e) {
                    Located::new(
                        mono::Exp::App(
                            Box::new(lifted),
                            Box::new(Located::new(mono::Exp::Rel(0), loc.clone())),
                        ),
                        loc.clone(),
                    )
                } else {
                    lifted
                };
                args.push(("_".to_string(), *dom));
                mono_args.push(Located::new(mono::Typ::Record(vec![]), loc.clone()));
                unravel_fun_full(*mono_ran, *ran, body, loc, sm, args, mono_args)
            }
        },
        _ => (mono_t, cjr_t, e),
    }
}

#[cfg(test)]
fn unravel_fun(
    mono_t: mono::LocTyp,
    cjr_t: LocTyp,
    e: mono::LocExp,
    loc: &Span,
    sm: &mut Sm,
    args: &mut Vec<(String, LocTyp)>,
) -> (LocTyp, mono::LocExp) {
    let mut mono_args = Vec::new();
    let (_, ran, body) = unravel_fun_full(mono_t, cjr_t, e, loc, sm, args, &mut mono_args);
    (ran, body)
}

fn mono_rebuild_fun_type(arg_tys: &[mono::LocTyp], ran: mono::LocTyp, loc: &Span) -> mono::LocTyp {
    arg_tys.iter().rev().cloned().fold(ran, |acc, dom| {
        Located::new(mono::Typ::Fun(Box::new(dom), Box::new(acc)), loc.clone())
    })
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
        mono::Exp::Named(n) => {
            if debug_validate_named_enabled()
                && debug_validate_named_span(&loc)
                && CJRIZE_NAMED_TYPES.with(|slot| !slot.borrow().contains_key(n))
            {
                let current_decl = CJRIZE_CURRENT_DECL.with(|slot| slot.borrow().clone());
                eprintln!(
                    "URWEB_DEBUG_CJR_VALIDATE mono named id={} decl={current_decl:?} {}:{} expr={:?}",
                    n, loc.file, loc.first.line, e.node
                );
            }
            Located::new(Exp::Named(*n), loc)
        }

        mono::Exp::Con(dk, pc, eo) => {
            let cpc = cify_pat_con(pc, sm);
            let ceo = eo.as_ref().map(|e| Box::new(cify_exp(e, sm, errors)));
            Located::new(Exp::Con(normalize_datatype_kind(*dk, pc), cpc, ceo), loc)
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

        mono::Exp::App(_, _) => {
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
            let mut args = Vec::new();
            let f_ref = collect_args(e, &mut args, &mut spine_budget);
            let cf = cify_exp(f_ref, sm, errors);
            let mut cargs: Vec<LocExp> = args.iter().map(|a| cify_exp(a, sm, errors)).collect();
            if let mono::Exp::Named(n) = &f_ref.node {
                let forced_unit_count = CJRIZE_NAMED_TYPES.with(|named_types| {
                    named_types
                        .borrow()
                        .get(n)
                        .cloned()
                        .and_then(|t| mono_drop_applied_result_typ(&t, &args))
                        .and_then(|mut t| {
                            let unit_arg = Located::new(mono::Exp::Record(vec![]), loc.clone());
                            let mut forced = 0usize;
                            while mono_result_needs_forced_unit_arg(&t) {
                                t = mono_result_after_app(&t, &unit_arg)?;
                                forced += 1;
                            }
                            Some(forced)
                        })
                        .unwrap_or(0)
                });
                debug_cjr_lowered(&loc, "named-app", || {
                    format!(
                        "decl={:?} named={n} args={:?} forced_units={forced_unit_count}",
                        CJRIZE_CURRENT_DECL.with(|slot| slot.borrow().clone()),
                        args.iter()
                            .map(|arg| format!("{:?}", arg.node))
                            .collect::<Vec<_>>()
                    )
                });
                for _ in 0..forced_unit_count {
                    cargs.push(cify_exp(
                        &Located::new(mono::Exp::Record(vec![]), loc.clone()),
                        sm,
                        errors,
                    ));
                }
            }
            Located::new(Exp::App(Box::new(cf), cargs), loc)
        }

        mono::Exp::Abs(_, _, _, _) => {
            if let Some(forced) = force_spurious_unit_thunk(e) {
                return cify_exp(&forced, sm, errors);
            }
            if std::env::var("URWEB_DEBUG_CJR_ABS").ok().as_deref() == Some("1") {
                let current_decl = CJRIZE_CURRENT_DECL.with(|slot| slot.borrow().clone());
                eprintln!(
                    "URWEB_DEBUG_CJR_ABS decl={current_decl:?} {}:{:?}",
                    loc.file, e
                );
            }
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
            let si = if old_xts.len() == 2 && old_xts[0].0 == "1" && old_xts[1].0 == "2" {
                if let Typ::List(inner, list_id) = &cjr_xts[1].1.node {
                    if cjr_typ_eq(&cjr_xts[0].1.node, &inner.node) {
                        *list_id
                    } else {
                        sm.find(&old_xts, cjr_xts)
                    }
                } else {
                    sm.find(&old_xts, cjr_xts)
                }
            } else {
                sm.find(&old_xts, cjr_xts)
            };
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

fn is_unit_record_exp(e: &mono::LocExp) -> bool {
    matches!(&e.node, mono::Exp::Record(fields) if fields.is_empty())
}

fn is_unit_record_typ(t: &mono::LocTyp) -> bool {
    matches!(&t.node, mono::Typ::Record(fields) if fields.is_empty())
}

fn is_erased_mono_witness_app(arg: &mono::LocExp, dom: &mono::LocTyp) -> bool {
    match &arg.node {
        mono::Exp::Record(fields) if fields.is_empty() => !is_unit_record_typ(dom),
        mono::Exp::Prim(Prim::Int(0)) => match &dom.node {
            mono::Typ::Record(fields) if fields.is_empty() => false,
            mono::Typ::Ffi(module, name) if module == "Basis" && name == "int" => false,
            _ => true,
        },
        _ => false,
    }
}

fn is_non_function_mono_typ(t: &mono::LocTyp) -> bool {
    !matches!(&t.node, mono::Typ::Fun(_, _) | mono::Typ::Transaction(_))
}

fn force_spurious_unit_thunk(e: &mono::LocExp) -> Option<mono::LocExp> {
    match &e.node {
        mono::Exp::Abs(_, dom, ran, body)
            if is_unit_record_typ(dom)
                && !matches!(&ran.node, mono::Typ::Fun(_, _) | mono::Typ::Transaction(_)) =>
        {
            let unit = Located::new(mono::Exp::Record(vec![]), e.span.clone());
            Some(reduce_head_apps_for_cjr(
                crate::monomorphized::environment::sub_exp_in_exp(0, &unit, body),
            ))
        }
        mono::Exp::Abs(_, dom, ran, body)
            if is_unit_record_typ(dom)
                && matches!(&ran.node, mono::Typ::Fun(inner_dom, _) if is_unit_record_typ(inner_dom))
                && matches!(&body.node, mono::Exp::Abs(_, inner_dom, _, _) if is_unit_record_typ(inner_dom)) =>
        {
            let unit = Located::new(mono::Exp::Record(vec![]), e.span.clone());
            Some(reduce_head_apps_for_cjr(
                crate::monomorphized::environment::sub_exp_in_exp(0, &unit, body),
            ))
        }
        _ => None,
    }
}

fn record_field_typ(record_typ: &mono::LocTyp, field: &str) -> Option<mono::LocTyp> {
    match &record_typ.node {
        mono::Typ::Record(fields) => fields
            .iter()
            .find(|(name, _)| name == field)
            .map(|(_, typ)| typ.clone()),
        _ => None,
    }
}

fn current_rel_typ(index: usize) -> Option<mono::LocTyp> {
    CJRIZE_REL_TYPES.with(|slot| slot.borrow().get(index).cloned())
}

fn current_rel_has_direct_field(index: usize, field: &str) -> bool {
    current_rel_typ(index)
        .and_then(|typ| record_field_typ(&typ, field))
        .is_some()
}

fn nearest_rel_with_direct_field(field: &str) -> Option<usize> {
    CJRIZE_REL_TYPES.with(|slot| {
        slot.borrow()
            .iter()
            .position(|typ| record_field_typ(typ, field).is_some())
    })
}

fn mono_query_row_type(qm: &mono::QueryMeta, span: &Span) -> mono::LocTyp {
    let mut fields = qm.exps.clone();
    fields.extend(qm.tables.iter().map(|(table, xts)| {
        (
            table.clone(),
            Located::new(mono::Typ::Record(xts.clone()), span.clone()),
        )
    }));
    Located::new(mono::Typ::Record(fields), span.clone())
}

fn projected_field_result_typ(result_typ: &mono::LocTyp, field: &str) -> Option<mono::LocTyp> {
    match &result_typ.node {
        mono::Typ::Record(_) => record_field_typ(result_typ, field),
        mono::Typ::Fun(dom, ran) => projected_field_result_typ(ran, field).map(|projected_ran| {
            Located::new(
                mono::Typ::Fun(dom.clone(), Box::new(projected_ran)),
                result_typ.span.clone(),
            )
        }),
        mono::Typ::Transaction(ran) => {
            projected_field_result_typ(ran, field).map(|projected_ran| {
                Located::new(
                    mono::Typ::Transaction(Box::new(projected_ran)),
                    result_typ.span.clone(),
                )
            })
        }
        _ => None,
    }
}

fn mono_result_needs_forced_unit_arg(t: &mono::LocTyp) -> bool {
    matches!(&t.node, mono::Typ::Transaction(_))
        || matches!(
            &t.node,
            mono::Typ::Fun(dom, ran)
                if is_unit_record_typ(dom)
                    && (is_non_function_mono_typ(ran) || mono_result_needs_forced_unit_arg(ran))
        )
}

fn mono_result_after_app(result_typ: &mono::LocTyp, arg: &mono::LocExp) -> Option<mono::LocTyp> {
    match &result_typ.node {
        mono::Typ::Fun(_, ran) => Some((**ran).clone()),
        mono::Typ::Transaction(ran) if is_unit_record_exp(arg) => Some((**ran).clone()),
        _ => None,
    }
}

fn mono_drop_applied_result_typ(t: &mono::LocTyp, args: &[mono::LocExp]) -> Option<mono::LocTyp> {
    let mut current = t.clone();
    for arg in args {
        current = mono_result_after_app(&current, arg)?;
    }
    Some(current)
}

fn mono_exp_result_typ(e: &mono::LocExp) -> Option<mono::LocTyp> {
    match &e.node {
        mono::Exp::Prim(prim) => Some(Located::new(
            mono::Typ::Ffi(
                "Basis".into(),
                match prim {
                    Prim::Int(_) => "int",
                    Prim::Float(_) => "float",
                    Prim::String(_, _) => "string",
                    Prim::Char(_) => "char",
                }
                .into(),
            ),
            e.span.clone(),
        )),
        mono::Exp::Rel(n) => CJRIZE_REL_TYPES.with(|slot| slot.borrow().get(*n).cloned()),
        mono::Exp::Record(fields) => Some(Located::new(
            mono::Typ::Record(
                fields
                    .iter()
                    .map(|(name, _, typ)| (name.clone(), typ.clone()))
                    .collect(),
            ),
            e.span.clone(),
        )),
        mono::Exp::Abs(_, dom, ran, _) => Some(Located::new(
            mono::Typ::Fun(Box::new(dom.clone()), Box::new(ran.clone())),
            e.span.clone(),
        )),
        mono::Exp::Let(_, _, _, body) => mono_exp_result_typ(body),
        mono::Exp::Named(n) => {
            CJRIZE_NAMED_TYPES.with(|named_types| named_types.borrow().get(n).cloned())
        }
        mono::Exp::Field(inner, projected) => {
            mono_exp_result_typ(inner).and_then(|typ| record_field_typ(&typ, projected))
        }
        mono::Exp::App(_, _) => {
            let (head, args) = strip_mono_app_spine(e.clone());
            mono_exp_result_typ(&head).and_then(|typ| mono_drop_applied_result_typ(&typ, &args))
        }
        _ => None,
    }
}

fn append_forced_unit_args(
    mut expr: mono::LocExp,
    mut result_typ: mono::LocTyp,
    loc: &Span,
) -> mono::LocExp {
    while mono_result_needs_forced_unit_arg(&result_typ) {
        let unit = Located::new(mono::Exp::Record(vec![]), loc.clone());
        expr = Located::new(
            mono::Exp::App(Box::new(expr), Box::new(unit.clone())),
            loc.clone(),
        );
        let Some(next) = mono_result_after_app(&result_typ, &unit) else {
            break;
        };
        result_typ = next;
    }
    expr
}

fn force_question_slot_terminal(e: mono::LocExp) -> mono::LocExp {
    let loc = e.span.clone();
    let (head, args) = strip_mono_app_spine(e.clone());
    match &head.node {
        mono::Exp::Named(n) => {
            let forced = CJRIZE_NAMED_TYPES.with(|named_types| {
                named_types
                    .borrow()
                    .get(n)
                    .and_then(|t| mono_drop_applied_result_typ(t, &args))
                    .map(|t| append_forced_unit_args(e.clone(), t, &loc))
            });
            forced.unwrap_or(e)
        }
        _ => force_spurious_unit_thunk(&e).unwrap_or(e),
    }
}

fn resolve_question_slot(base: mono::LocExp, loc: &Span) -> mono::LocExp {
    let (head, args) = strip_mono_app_spine(base);
    match head.node {
        mono::Exp::Record(fields) => {
            if let Some((_, exp, _)) = fields.iter().find(|(name, _, _)| name == "?") {
                return reduce_head_apps_for_cjr(reapply_mono_app_spine(exp.clone(), args));
            }
            Located::new(
                mono::Exp::Field(
                    Box::new(reapply_mono_app_spine(
                        Located::new(mono::Exp::Record(fields), head.span),
                        args,
                    )),
                    "?".into(),
                ),
                loc.clone(),
            )
        }
        other => {
            let receiver = reapply_mono_app_spine(Located::new(other, head.span), args);
            match receiver.node {
                mono::Exp::Rel(_)
                | mono::Exp::Abs(_, _, _, _)
                | mono::Exp::Field(_, _)
                | mono::Exp::Let(_, _, _, _) => Located::new(
                    mono::Exp::Field(Box::new(receiver), "?".into()),
                    loc.clone(),
                ),
                _ => force_question_slot_terminal(receiver),
            }
        }
    }
}

fn strip_mono_app_spine(mut e: mono::LocExp) -> (mono::LocExp, Vec<mono::LocExp>) {
    let mut rev_args = Vec::new();
    loop {
        let span = e.span.clone();
        match e.node {
            mono::Exp::App(f, arg) => {
                rev_args.push(*arg);
                e = *f;
            }
            other => {
                rev_args.reverse();
                return (Located::new(other, span), rev_args);
            }
        }
    }
}

fn reapply_mono_app_spine(mut head: mono::LocExp, args: Vec<mono::LocExp>) -> mono::LocExp {
    for arg in args {
        let span = head.span.clone();
        head = Located::new(mono::Exp::App(Box::new(head), Box::new(arg)), span);
    }
    head
}

fn mono_record_distributes_application(e: &mono::LocExp) -> bool {
    matches!(
        &e.node,
        mono::Exp::Record(fields)
            if !fields.is_empty()
                && fields
                    .iter()
                    .all(|(_, _, field_t)| matches!(field_t.node, mono::Typ::Fun(..)))
    )
}

fn strip_spurious_app(function: mono::LocExp, arg: &mono::LocExp) -> Option<mono::LocExp> {
    if is_unit_record_exp(arg)
        && !matches!(function.node, mono::Exp::Abs(_, _, _, _))
        && !mono_record_distributes_application(&function)
        && mono_exp_result_typ(&function)
            .is_some_and(|result_typ| is_non_function_mono_typ(&result_typ))
    {
        return Some(function);
    }

    match &function.node {
        mono::Exp::Case(_, _, meta) if is_non_function_mono_typ(&meta.result) => Some(function),
        mono::Exp::Strcat(_, _) if is_unit_record_exp(arg) => Some(function),
        mono::Exp::FfiApp(module, name, _)
            if is_unit_record_exp(arg)
                && module == "Basis"
                && matches!(name.as_str(), "mstrcat" | "strcat") =>
        {
            Some(function)
        }
        mono::Exp::Query(_)
        | mono::Exp::Dml(_, _)
        | mono::Exp::Nextval(_)
        | mono::Exp::Setval(_, _)
            if is_unit_record_exp(arg) =>
        {
            Some(function)
        }
        _ => None,
    }
}

fn is_erased_mono_proof_arg(e: &mono::LocExp) -> bool {
    matches!(&e.node, mono::Exp::Record(fields) if fields.is_empty())
        || matches!(&e.node, mono::Exp::Prim(Prim::Int(0)))
}

fn mono_exp_may_project_field(e: &mono::LocExp, field: &str) -> bool {
    mono_exp_result_typ(e)
        .and_then(|typ| projected_field_result_typ(&typ, field))
        .is_some()
}

fn mono_exp_has_direct_field(e: &mono::LocExp, field: &str) -> bool {
    mono_exp_result_typ(e)
        .and_then(|typ| record_field_typ(&typ, field))
        .is_some()
}

fn can_reuse_existing_mono_projection(arg: &mono::LocExp, field: &str) -> bool {
    match &arg.node {
        mono::Exp::Field(inner, projected) if projected == field => {
            mono_exp_has_direct_field(inner, field) || mono_exp_may_project_field(inner, field)
        }
        _ => false,
    }
}

fn project_missing_field_from_mono_args(
    args: &[mono::LocExp],
    field: &str,
    loc: &Span,
) -> Option<mono::LocExp> {
    let idx = (0..args.len()).rev().find(|&idx| {
        let arg = &args[idx];
        !is_erased_mono_proof_arg(arg)
            && (mono_exp_may_project_field(arg, field)
                || can_reuse_existing_mono_projection(arg, field))
    })?;
    if let mono::Exp::Field(inner, projected) = &args[idx].node {
        if projected == field {
            let existing_projection = if idx + 1 < args.len() {
                Located::new(
                    mono::Exp::Field(
                        Box::new(reapply_mono_app_spine(
                            *inner.clone(),
                            args[idx + 1..].to_vec(),
                        )),
                        field.to_string(),
                    ),
                    loc.clone(),
                )
            } else {
                args[idx].clone()
            };
            debug_cjr_field(loc, "recover-existing", || {
                format!(
                    "field={field} idx={idx} arg={:?} tail={:?} reused={:?}",
                    args[idx].node,
                    args[idx + 1..]
                        .iter()
                        .map(|arg| format!("{:?}", arg.node))
                        .collect::<Vec<_>>(),
                    existing_projection.node
                )
            });
            return Some(existing_projection);
        }
    }

    let receiver = if mono_exp_has_direct_field(&args[idx], field) {
        args[idx].clone()
    } else {
        reapply_mono_app_spine(args[idx].clone(), args[idx + 1..].to_vec())
    };
    debug_cjr_field(loc, "recover", || {
        format!(
            "field={field} idx={idx} direct={} arg={:?} receiver={:?} tail={:?}",
            mono_exp_has_direct_field(&args[idx], field),
            args[idx].node,
            receiver.node,
            args[idx + 1..]
                .iter()
                .map(|arg| format!("{:?}", arg.node))
                .collect::<Vec<_>>()
        )
    });
    let projected = Located::new(
        mono::Exp::Field(Box::new(receiver), field.to_string()),
        loc.clone(),
    );
    Some(projected)
}

fn reduce_head_apps_for_cjr(e: mono::LocExp) -> mono::LocExp {
    let loc = e.span.clone();
    match e.node {
        mono::Exp::App(f, arg) => {
            let f = reduce_head_apps_for_cjr(*f);
            let arg = reduce_head_apps_for_cjr(*arg);
            if debug_cjr_field_span(&loc) {
                debug_cjr_field(&loc, "app", || {
                    format!("head={:?} arg={:?}", f.node, arg.node)
                });
            }
            if let Some(stripped) = strip_spurious_app(f.clone(), &arg) {
                return reduce_head_apps_for_cjr(stripped);
            }
            if let mono::Exp::Field(inner, _) = f.node.clone() {
                if let mono::Exp::Field(base, missing_field) = inner.node.clone() {
                    if let mono::Exp::Abs(_, _, ran, _) = base.node.clone() {
                        if projected_field_result_typ(&ran, &missing_field).is_none() {
                            return Located::new(mono::Exp::App(Box::new(f), Box::new(arg)), loc);
                        }
                    }
                }
            }
            if let mono::Exp::App(f2, arg1) = f.node.clone() {
                if let mono::Exp::Field(base, missing_field) = f2.node.clone() {
                    if let mono::Exp::Abs(_, _, ran, _) = base.node.clone() {
                        if projected_field_result_typ(&ran, &missing_field).is_none()
                            && mono_exp_has_direct_field(&arg, &missing_field)
                        {
                            return reduce_head_apps_for_cjr(Located::new(
                                mono::Exp::App(
                                    Box::new(Located::new(
                                        mono::Exp::Field(Box::new(arg.clone()), missing_field),
                                        f2.span.clone(),
                                    )),
                                    arg1,
                                ),
                                loc,
                            ));
                        }
                        if projected_field_result_typ(&ran, &missing_field).is_none()
                            && mono_exp_has_direct_field(&arg1, &missing_field)
                        {
                            return reduce_head_apps_for_cjr(Located::new(
                                mono::Exp::Field(Box::new((*arg1).clone()), missing_field),
                                f2.span.clone(),
                            ));
                        }
                    }
                }
                if let mono::Exp::Field(inner, subfield) = f2.node.clone() {
                    if let mono::Exp::Field(base, missing_field) = inner.node.clone() {
                        if let mono::Exp::Abs(_, _, ran, _) = base.node.clone() {
                            if projected_field_result_typ(&ran, &missing_field).is_none()
                                && mono_exp_has_direct_field(&arg, &missing_field)
                            {
                                return reduce_head_apps_for_cjr(Located::new(
                                    mono::Exp::App(
                                        Box::new(Located::new(
                                            mono::Exp::Field(
                                                Box::new(Located::new(
                                                    mono::Exp::Field(
                                                        Box::new(arg.clone()),
                                                        missing_field.clone(),
                                                    ),
                                                    inner.span.clone(),
                                                )),
                                                subfield.clone(),
                                            ),
                                            f2.span.clone(),
                                        )),
                                        arg1,
                                    ),
                                    loc,
                                ));
                            }
                            if projected_field_result_typ(&ran, &missing_field).is_none()
                                && mono_exp_has_direct_field(&arg1, &missing_field)
                            {
                                return reduce_head_apps_for_cjr(Located::new(
                                    mono::Exp::Field(
                                        Box::new(Located::new(
                                            mono::Exp::Field(
                                                Box::new((*arg1).clone()),
                                                missing_field,
                                            ),
                                            inner.span.clone(),
                                        )),
                                        subfield,
                                    ),
                                    f2.span.clone(),
                                ));
                            }
                            if projected_field_result_typ(&ran, &missing_field).is_none() {
                                return reduce_head_apps_for_cjr(Located::new(
                                    mono::Exp::App(
                                        Box::new(Located::new(
                                            mono::Exp::Field(
                                                Box::new(Located::new(
                                                    mono::Exp::Field(
                                                        Box::new(arg.clone()),
                                                        missing_field,
                                                    ),
                                                    inner.span.clone(),
                                                )),
                                                subfield,
                                            ),
                                            f2.span.clone(),
                                        )),
                                        arg1,
                                    ),
                                    loc,
                                ));
                            }
                        }
                    }
                }
            }
            if let mono::Exp::Field(base, missing_field) = f.node.clone() {
                if let mono::Exp::Abs(_, _, ran, _) = base.node.clone() {
                    if projected_field_result_typ(&ran, &missing_field).is_none()
                        && mono_exp_has_direct_field(&arg, &missing_field)
                    {
                        return reduce_head_apps_for_cjr(Located::new(
                            mono::Exp::Field(Box::new(arg), missing_field),
                            f.span.clone(),
                        ));
                    }
                }
            }
            match f.node {
                mono::Exp::Abs(x, dom, ran, body) => {
                    if is_erased_mono_witness_app(&arg, &dom) {
                        Located::new(mono::Exp::Abs(x, dom, ran, body), f.span)
                    } else {
                        reduce_head_apps_for_cjr(crate::monomorphized::environment::sub_exp_in_exp(
                            0, &arg, &body,
                        ))
                    }
                }
                mono::Exp::Let(x, t, e1, body) => {
                    let lifted_arg = lift_mono_exp(0, arg);
                    let app = Located::new(mono::Exp::App(body, Box::new(lifted_arg)), loc.clone());
                    reduce_head_apps_for_cjr(Located::new(
                        mono::Exp::Let(x, t, e1, Box::new(app)),
                        loc,
                    ))
                }
                mono::Exp::Case(disc, arms, meta) => {
                    let result = mono_result_after_app(&meta.result, &arg)
                        .unwrap_or_else(|| meta.result.clone());
                    reduce_head_apps_for_cjr(Located::new(
                        mono::Exp::Case(
                            disc,
                            arms.into_iter()
                                .map(|(pat, arm)| {
                                    (
                                        pat,
                                        reduce_head_apps_for_cjr(Located::new(
                                            mono::Exp::App(Box::new(arm), Box::new(arg.clone())),
                                            loc.clone(),
                                        )),
                                    )
                                })
                                .collect(),
                            mono::CaseMeta {
                                disc: meta.disc,
                                result,
                            },
                        ),
                        loc,
                    ))
                }
                mono::Exp::Field(inner, field)
                    if matches!(
                        inner.node,
                        mono::Exp::Abs(_, _, _, _)
                            | mono::Exp::App(_, _)
                            | mono::Exp::Field(_, _)
                            | mono::Exp::Record(_)
                            | mono::Exp::Let(_, _, _, _)
                    ) && !mono_exp_has_direct_field(&inner, &field) =>
                {
                    let applied_inner = Located::new(
                        mono::Exp::App(inner.clone(), Box::new(arg.clone())),
                        f.span.clone(),
                    );
                    if mono_exp_has_direct_field(&applied_inner, &field) {
                        reduce_head_apps_for_cjr(Located::new(
                            mono::Exp::Field(Box::new(applied_inner), field),
                            loc,
                        ))
                    } else {
                        Located::new(
                            mono::Exp::App(
                                Box::new(Located::new(mono::Exp::Field(inner, field), f.span)),
                                Box::new(arg),
                            ),
                            loc,
                        )
                    }
                }
                mono::Exp::Record(fields) if matches!(fields.as_slice(), [(name, _, _)] if name == "?") =>
                {
                    debug_cjr_field(&loc, "unwrap-singleton-record-app", || {
                        format!("record={fields:?} arg={:?}", arg.node)
                    });
                    let (_, field_exp, _) =
                        fields.into_iter().next().expect("singleton prechecked");
                    reduce_head_apps_for_cjr(Located::new(
                        mono::Exp::App(Box::new(field_exp), Box::new(arg)),
                        loc,
                    ))
                }
                mono::Exp::Record(fields)
                    if fields
                        .iter()
                        .all(|(_, _, field_t)| matches!(field_t.node, mono::Typ::Fun(..))) =>
                {
                    Located::new(
                        mono::Exp::Record(
                            fields
                                .into_iter()
                                .map(|(name, field_exp, field_t)| {
                                    let mono::Typ::Fun(_, ran) = field_t.node else {
                                        unreachable!("record-app fields prechecked above")
                                    };
                                    let applied = Located::new(
                                        mono::Exp::App(Box::new(field_exp), Box::new(arg.clone())),
                                        loc.clone(),
                                    );
                                    (name, reduce_head_apps_for_cjr(applied), *ran)
                                })
                                .collect(),
                        ),
                        loc,
                    )
                }
                other => Located::new(
                    mono::Exp::App(Box::new(Located::new(other, f.span)), Box::new(arg)),
                    loc,
                ),
            }
        }
        mono::Exp::Abs(x, dom, ran, body) => with_rel_binder(dom.clone(), || {
            Located::new(
                mono::Exp::Abs(x, dom, ran, Box::new(reduce_head_apps_for_cjr(*body))),
                loc,
            )
        }),
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
        mono::Exp::Field(inner, field) => {
            let inner = reduce_head_apps_for_cjr(*inner);
            let (head, args) = strip_mono_app_spine(inner);
            let head_span = head.span.clone();
            debug_cjr_field(&loc, "field-enter", || {
                format!(
                    "field={field} head={:?} args={:?}",
                    head.node,
                    args.iter()
                        .map(|arg| format!("{:?}", arg.node))
                        .collect::<Vec<_>>()
                )
            });
            if args.is_empty() {
                if let mono::Exp::Rel(rel) = head.node {
                    if !current_rel_has_direct_field(rel, &field) {
                        if let Some(correct_rel) = nearest_rel_with_direct_field(&field) {
                            if correct_rel != rel {
                                let projected_head = Located::new(
                                    mono::Exp::Field(
                                        Box::new(Located::new(
                                            mono::Exp::Rel(correct_rel),
                                            head_span.clone(),
                                        )),
                                        field.clone(),
                                    ),
                                    head_span,
                                );
                                return reduce_head_apps_for_cjr(reapply_mono_app_spine(
                                    projected_head,
                                    args,
                                ));
                            }
                        }
                    }
                }
            }
            if let mono::Exp::Rel(rel) = head.node {
                if rel > 0
                    && current_rel_has_direct_field(0, &field)
                    && !current_rel_has_direct_field(rel, &field)
                {
                    let projected_head = Located::new(
                        mono::Exp::Field(
                            Box::new(Located::new(mono::Exp::Rel(0), head_span.clone())),
                            field.clone(),
                        ),
                        head_span,
                    );
                    return reduce_head_apps_for_cjr(reapply_mono_app_spine(projected_head, args));
                }
            }
            if !args.is_empty() && mono_exp_has_direct_field(&head, &field) {
                let projected_head =
                    Located::new(mono::Exp::Field(Box::new(head), field.clone()), head_span);
                return reduce_head_apps_for_cjr(reapply_mono_app_spine(projected_head, args));
            }
            if !args.is_empty() && matches!(head.node, mono::Exp::Rel(_)) {
                let projected_head =
                    Located::new(mono::Exp::Field(Box::new(head), field.clone()), head_span);
                return reduce_head_apps_for_cjr(reapply_mono_app_spine(projected_head, args));
            }
            if let mono::Exp::Field(base, passthrough) = head.node.clone() {
                if passthrough == "?" {
                    let current = resolve_question_slot(*base, &loc);
                    let unresolved_question =
                        matches!(&current.node, mono::Exp::Field(_, field) if field == "?");
                    if field == "?" {
                        return if unresolved_question {
                            reapply_mono_app_spine(current, args)
                        } else {
                            reduce_head_apps_for_cjr(reapply_mono_app_spine(current, args))
                        };
                    }
                    if unresolved_question {
                        if let Some(projected_tail) =
                            project_missing_field_from_mono_args(&args, &field, &loc)
                        {
                            return reduce_head_apps_for_cjr(projected_tail);
                        }
                        return Located::new(
                            mono::Exp::Field(
                                Box::new(reapply_mono_app_spine(current, args)),
                                field,
                            ),
                            loc,
                        );
                    }
                    let projected = Located::new(
                        mono::Exp::Field(Box::new(current), field.clone()),
                        head_span,
                    );
                    return reduce_head_apps_for_cjr(reapply_mono_app_spine(projected, args));
                }
            }
            match head.node {
                mono::Exp::Record(fields) => {
                    if let Some((_, exp, _)) = fields.iter().find(|(name, _, _)| name == &field) {
                        reduce_head_apps_for_cjr(reapply_mono_app_spine(exp.clone(), args))
                    } else if field == "?" {
                        Located::new(
                            mono::Exp::Field(
                                Box::new(reapply_mono_app_spine(
                                    Located::new(mono::Exp::Record(fields), head_span),
                                    args,
                                )),
                                field,
                            ),
                            loc,
                        )
                    } else if let Some(projected_tail) =
                        project_missing_field_from_mono_args(&args, &field, &loc)
                    {
                        reduce_head_apps_for_cjr(projected_tail)
                    } else {
                        Located::new(
                            mono::Exp::Field(
                                Box::new(reapply_mono_app_spine(
                                    Located::new(mono::Exp::Record(fields), head_span),
                                    args,
                                )),
                                field,
                            ),
                            loc,
                        )
                    }
                }
                mono::Exp::Let(x, t, e1, e2) => {
                    let projected = Located::new(
                        mono::Exp::Field(
                            Box::new(with_rel_binder(t.clone(), || {
                                reduce_head_apps_for_cjr(reapply_mono_app_spine(*e2, args))
                            })),
                            field.clone(),
                        ),
                        head_span.clone(),
                    );
                    reduce_head_apps_for_cjr(Located::new(
                        mono::Exp::Let(x, t, e1, Box::new(projected)),
                        loc,
                    ))
                }
                mono::Exp::Abs(x, dom, ran, body) => {
                    if let Some(projected_ran) = projected_field_result_typ(&ran, &field) {
                        let projected =
                            Located::new(mono::Exp::Field(body, field.clone()), head_span.clone());
                        reduce_head_apps_for_cjr(reapply_mono_app_spine(
                            Located::new(
                                mono::Exp::Abs(
                                    x,
                                    dom,
                                    projected_ran,
                                    Box::new(reduce_head_apps_for_cjr(projected)),
                                ),
                                loc,
                            ),
                            args,
                        ))
                    } else if let Some(projected_tail) =
                        project_missing_field_from_mono_args(&args, &field, &loc)
                    {
                        reduce_head_apps_for_cjr(projected_tail)
                    } else {
                        Located::new(
                            mono::Exp::Field(
                                Box::new(reapply_mono_app_spine(
                                    Located::new(mono::Exp::Abs(x, dom, ran, body), head_span),
                                    args,
                                )),
                                field,
                            ),
                            loc,
                        )
                    }
                }
                other => {
                    if field == "?" {
                        let receiver = reapply_mono_app_spine(Located::new(other, head_span), args);
                        match receiver.node {
                            mono::Exp::Rel(_)
                            | mono::Exp::Abs(_, _, _, _)
                            | mono::Exp::Field(_, _)
                            | mono::Exp::Let(_, _, _, _) => {
                                Located::new(mono::Exp::Field(Box::new(receiver), field), loc)
                            }
                            _ => force_question_slot_terminal(receiver),
                        }
                    } else if let Some(projected_tail) =
                        project_missing_field_from_mono_args(&args, &field, &loc)
                    {
                        reduce_head_apps_for_cjr(projected_tail)
                    } else {
                        Located::new(
                            mono::Exp::Field(
                                Box::new(reapply_mono_app_spine(
                                    Located::new(other, head_span),
                                    args,
                                )),
                                field,
                            ),
                            loc,
                        )
                    }
                }
            }
        }
        mono::Exp::Case(disc, arms, meta) => Located::new(
            mono::Exp::Case(
                Box::new(reduce_head_apps_for_cjr(*disc)),
                arms.into_iter()
                    .map(|(pat, arm)| {
                        let reduced_arm =
                            with_rel_pattern_binders(&pat, || reduce_head_apps_for_cjr(arm));
                        (pat, reduced_arm)
                    })
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
        mono::Exp::Let(x, t, e1, e2) => {
            let reduced_e1 = reduce_head_apps_for_cjr(*e1);
            let reduced_e2 = with_rel_binder(t.clone(), || reduce_head_apps_for_cjr(*e2));
            Located::new(
                mono::Exp::Let(x, t, Box::new(reduced_e1), Box::new(reduced_e2)),
                loc,
            )
        }
        mono::Exp::Closure(n, envs) => Located::new(
            mono::Exp::Closure(n, envs.into_iter().map(reduce_head_apps_for_cjr).collect()),
            loc,
        ),
        mono::Exp::Query(qm) => {
            let row_t = mono_query_row_type(&qm, &loc);
            let state_t = qm.state.clone();
            Located::new(
                mono::Exp::Query(mono::QueryMeta {
                    exps: qm.exps,
                    tables: qm.tables,
                    state: qm.state,
                    query: Box::new(reduce_head_apps_for_cjr(*qm.query)),
                    body: Box::new(with_rel_binder(row_t, || {
                        with_rel_binder(state_t, || reduce_head_apps_for_cjr(*qm.body))
                    })),
                    initial: Box::new(reduce_head_apps_for_cjr(*qm.initial)),
                }),
                loc,
            )
        }
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
                    let kind = classify_constrs(dt.id, &dt.constrs);
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
            let refreshed_t = refresh_decl_type_from_exp(t.clone(), e);
            if type_has_signal(&refreshed_t.node) {
                return (None, None);
            }
            // For script declarations, stub out the body.
            let effective_e = if _s == "<script>" {
                stub_body(&refreshed_t, &loc)
            } else {
                e.clone()
            };

            if std::env::var("URWEB_DEBUG_CJR_ABS_DECL").ok().as_deref() == Some("1")
                && contains_debug_show_option_abs(&effective_e)
            {
                let path = debug_show_option_path(&effective_e)
                    .map(|segments| segments.join(" -> "))
                    .unwrap_or_else(|| "<path unavailable>".to_string());
                eprintln!(
                    "URWEB_DEBUG_CJR_ABS_DECL val name={x} id={n} src={_s} path={path} body={:?}",
                    effective_e
                );
            }

            let ct = cify_typ(&refreshed_t, sm);
            debug_chat_cjr(&loc, "decl", || {
                format!(
                    "name={x} id={n} mono_t={:?} cjr_t={:?} exp={:?}",
                    refreshed_t.node, ct.node, e.node
                )
            });
            debug_cjr_pre_unravel(&loc, "val", || {
                format!(
                    "name={x} id={n} mono_t={:?} cjr_t={:?} exp={:?}",
                    refreshed_t.node, ct.node, effective_e.node
                )
            });

            let d = with_current_decl(format!("val:{x}:{n}"), || match &ct.node {
                Typ::Fun(..) => {
                    let mut args = Vec::new();
                    let mut mono_args = Vec::new();
                    let (mono_ran, ran, body) = unravel_fun_full(
                        refreshed_t.clone(),
                        ct.clone(),
                        effective_e,
                        &loc,
                        sm,
                        &mut args,
                        &mut mono_args,
                    );
                    let lowered_t = mono_rebuild_fun_type(&mono_args, mono_ran, &loc);
                    debug_cjr_lowered(&loc, "val-fun", || {
                        format!(
                            "name={x} id={n} lowered_t={:?} args={args:?}",
                            lowered_t.node
                        )
                    });
                    CJRIZE_NAMED_TYPES.with(|slot| {
                        slot.borrow_mut().insert(*n, lowered_t);
                    });
                    let rel_types = mono_args.iter().rev().cloned().collect();
                    let raw_body = body.clone();
                    let body = with_rel_types(rel_types, || reduce_head_apps_for_cjr(body));
                    if std::env::var("URWEB_DEBUG_CJR_ABS_DECL").ok().as_deref() == Some("1")
                        && contains_debug_show_option_abs(&body)
                    {
                        let path = debug_show_option_path(&body)
                            .map(|segments| segments.join(" -> "))
                            .unwrap_or_else(|| "<path unavailable>".to_string());
                        eprintln!(
                            "URWEB_DEBUG_CJR_ABS_DECL decl-fun name={x} id={n} args={args:?} ran={:?} path={path} body={:?}",
                            ran.node, body
                        );
                    }
                    debug_chat_cjr(&loc, "decl-fun", || {
                        format!(
                            "name={x} id={n} args={args:?} ran={:?} body={:?}",
                            ran.node, body.node
                        )
                    });
                    debug_cjr_top_lambda(&loc, "val", || {
                        format!(
                            "name={x} id={n} args={args:?} ran={:?} pre={:?} body={:?}",
                            ran.node, raw_body.node, body.node
                        )
                    });
                    let cbody = cify_exp(&body, sm, errors);
                    debug_cjr_top_lambda(&loc, "val-cjr", || {
                        format!(
                            "name={x} id={n} args={args:?} ran={:?} cbody={:?}",
                            ran.node, cbody.node
                        )
                    });
                    Decl::Fun(x.clone(), *n, args, ran, cbody)
                }
                _ => {
                    let ce = cify_exp(&effective_e, sm, errors);
                    Decl::Val(x.clone(), *n, ct, ce)
                }
            });
            (Some(Located::new(d, loc)), None)
        }

        mono::Decl::ValRec(vis) => {
            // Drop signal-typed members.
            let vis: Vec<_> = vis
                .iter()
                .filter(|(_, _, t, e, _)| {
                    !type_has_signal(&refresh_decl_type_from_exp(t.clone(), e).node)
                })
                .collect();
            if vis.is_empty() {
                return (None, None);
            }
            let any_script_member = vis.iter().any(|(_, _, _, _, s)| *s == "<script>");
            enum PreparedFun {
                Lowered {
                    name: String,
                    id: usize,
                    label: String,
                    args: Vec<(String, LocTyp)>,
                    mono_args: Vec<mono::LocTyp>,
                    mono_ran: mono::LocTyp,
                    ran: LocTyp,
                    body: mono::LocExp,
                },
                Plain {
                    name: String,
                    id: usize,
                    label: String,
                    ct: LocTyp,
                    body: mono::LocExp,
                },
            }

            let prepared: Vec<PreparedFun> = vis
                .iter()
                .map(|(x, n, t, e, s)| {
                    let label = format!("valrec:{x}:{n}");
                    with_current_decl(label.clone(), || {
                        let refreshed_t = refresh_decl_type_from_exp(t.clone(), e);
                        let effective_e = if any_script_member || *s == "<script>" {
                            stub_body(&refreshed_t, &loc)
                        } else {
                            e.clone()
                        };
                        if std::env::var("URWEB_DEBUG_CJR_ABS_DECL").ok().as_deref() == Some("1")
                            && contains_debug_show_option_abs(&effective_e)
                        {
                            let path = debug_show_option_path(&effective_e)
                                .map(|segments| segments.join(" -> "))
                                .unwrap_or_else(|| "<path unavailable>".to_string());
                            eprintln!(
                                "URWEB_DEBUG_CJR_ABS_DECL valrec name={x} id={n} src={s} path={path} body={:?}",
                                effective_e
                            );
                        }
                        let ct = cify_typ(&refreshed_t, sm);
                        debug_cjr_pre_unravel(&loc, "valrec", || {
                            format!(
                                "name={x} id={n} mono_t={:?} cjr_t={:?} exp={:?}",
                                refreshed_t.node, ct.node, effective_e.node
                            )
                        });
                        match &ct.node {
                            Typ::Fun(..) => {
                                let mut args = Vec::new();
                                let mut mono_args = Vec::new();
                                let (mono_ran, ran, body) = unravel_fun_full(
                                    refreshed_t,
                                    ct,
                                    effective_e,
                                    &loc,
                                    sm,
                                    &mut args,
                                    &mut mono_args,
                                );
                                debug_cjr_lowered(&loc, "valrec-fun", || {
                                    format!(
                                        "name={x} id={n} lowered_t={:?} args={args:?}",
                                        mono_rebuild_fun_type(&mono_args, mono_ran.clone(), &loc).node
                                    )
                                });
                                let raw_body = body.clone();
                                debug_cjr_top_lambda(&loc, "valrec-pre", || {
                                    format!(
                                        "name={x} id={n} args={args:?} ran={:?} pre={:?}",
                                        ran.node, raw_body.node
                                    )
                                });
                                PreparedFun::Lowered {
                                    name: x.clone(),
                                    id: *n,
                                    label,
                                    args,
                                    mono_args,
                                    mono_ran,
                                    ran,
                                    body: raw_body,
                                }
                            }
                            _ => PreparedFun::Plain {
                                name: x.clone(),
                                id: *n,
                                label,
                                ct,
                                body: effective_e,
                            },
                        }
                    })
                })
                .collect();

            for prepared_fun in &prepared {
                if let PreparedFun::Lowered {
                    id,
                    mono_args,
                    mono_ran,
                    ..
                } = prepared_fun
                {
                    CJRIZE_NAMED_TYPES.with(|slot| {
                        slot.borrow_mut().insert(
                            *id,
                            mono_rebuild_fun_type(mono_args, mono_ran.clone(), &loc),
                        );
                    });
                }
            }

            let cfuns: Vec<(String, usize, Vec<(String, LocTyp)>, LocTyp, LocExp)> = prepared
                .into_iter()
                .map(|prepared_fun| match prepared_fun {
                    PreparedFun::Lowered {
                        name,
                        id,
                        label,
                        args,
                        mono_args,
                        ran,
                        body,
                        ..
                    } => with_current_decl(label, || {
                        let rel_types = mono_args.iter().rev().cloned().collect();
                        let body = with_rel_types(rel_types, || reduce_head_apps_for_cjr(body));
                        if std::env::var("URWEB_DEBUG_CJR_ABS_DECL").ok().as_deref()
                            == Some("1")
                            && contains_debug_show_option_abs(&body)
                        {
                            let path = debug_show_option_path(&body)
                                .map(|segments| segments.join(" -> "))
                                .unwrap_or_else(|| "<path unavailable>".to_string());
                            eprintln!(
                                "URWEB_DEBUG_CJR_ABS_DECL valrec-fun name={name} id={id} args={args:?} ran={:?} path={path} body={:?}",
                                ran.node, body
                            );
                        }
                        debug_cjr_top_lambda(&loc, "valrec", || {
                            format!(
                                "name={name} id={id} args={args:?} ran={:?} body={:?}",
                                ran.node, body.node
                            )
                        });
                        let cbody = cify_exp(&body, sm, errors);
                        debug_cjr_top_lambda(&loc, "valrec-cjr", || {
                            format!(
                                "name={name} id={id} args={args:?} ran={:?} cbody={:?}",
                                ran.node, cbody.node
                            )
                        });
                        (name, id, args, ran, cbody)
                    }),
                    PreparedFun::Plain {
                        name,
                        id,
                        label,
                        ct,
                        body,
                    } => with_current_decl(label, || {
                        errors.report_at(
                            loc.clone(),
                            DiagnosticPayload::new(
                                DiagnosticId::CjrizeFunctionNotExplicitAtCodegen,
                                Vec::new(),
                            ),
                        );
                        (name, id, vec![], ct, cify_exp(&body, sm, errors))
                    }),
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
    let mono_bound = collect_mono_bound_named_ids(&mono_decls);
    let mut sm = Sm::new();
    // dsf = "front" declarations: struct defs, type forward decls, datatypes
    let mut dsf: Vec<LocDecl> = Vec::new();
    // ds = regular declarations
    let mut ds: Vec<LocDecl> = Vec::new();
    // export entries (without sidedness — to be filled from mono_ps)
    let mut ps_raw: Vec<(ExportKind, String, usize, Vec<LocTyp>, LocTyp, bool)> = Vec::new();
    let mut named: HashMap<usize, mono::LocExp> = HashMap::new();
    let mut named_types: HashMap<usize, mono::LocTyp> = HashMap::new();

    for mono_decl in &mono_decls {
        match &mono_decl.node {
            mono::Decl::Val(_, n, t, e, _) => {
                named.insert(*n, e.clone());
                named_types.insert(*n, refresh_decl_type_from_exp(t.clone(), e));
            }
            mono::Decl::ValRec(vis) => {
                for (_, n, t, e, _) in vis {
                    named.insert(*n, e.clone());
                    named_types.insert(*n, refresh_decl_type_from_exp(t.clone(), e));
                }
            }
            _ => {}
        }
    }

    CJRIZE_NAMED_TYPES.with(|slot| {
        *slot.borrow_mut() = named_types.clone();
    });
    CJRIZE_RAW_NAMED_TYPES.with(|slot| {
        *slot.borrow_mut() = named_types;
    });
    CJRIZE_REL_TYPES.with(|slot| slot.borrow_mut().clear());
    CJRIZE_CONSTRUCTOR_KINDS.with(|slot| {
        let mut kinds = slot.borrow_mut();
        kinds.clear();
        for mono_decl in &mono_decls {
            if let mono::Decl::Datatype(dts) = &mono_decl.node {
                for dt in dts {
                    if mono_exact_list_element(dt.id, &dt.constrs).is_some() {
                        continue;
                    }
                    let kind = classify_constrs(dt.id, &dt.constrs);
                    for (_, constructor_id, _) in &dt.constrs {
                        kinds.insert(*constructor_id, kind);
                    }
                }
            }
        }
    });

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

    CJRIZE_NAMED_TYPES.with(|slot| slot.borrow_mut().clear());
    CJRIZE_RAW_NAMED_TYPES.with(|slot| slot.borrow_mut().clear());
    CJRIZE_REL_TYPES.with(|slot| slot.borrow_mut().clear());
    CJRIZE_CONSTRUCTOR_KINDS.with(|slot| slot.borrow_mut().clear());

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
    if debug_validate_named_enabled() {
        debug_validate_cjr_named_refs(&dsf, &mono_bound);
    }
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
    fn reduce_head_apps_projects_record_field() -> anyhow::Result<()> {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let fn_t = Located::new(
            mono::Typ::Fun(Box::new(unit_t.clone()), Box::new(unit_t.clone())),
            span.clone(),
        );
        let record = Located::new(
            mono::Exp::Record(vec![
                (
                    "Inject".into(),
                    Located::new(mono::Exp::Prim(Prim::Int(7)), span.clone()),
                    int_t,
                ),
                (
                    "Widget".into(),
                    Located::new(
                        mono::Exp::Abs(
                            "_".into(),
                            unit_t.clone(),
                            unit_t.clone(),
                            Box::new(Located::new(mono::Exp::Record(vec![]), span.clone())),
                        ),
                        span.clone(),
                    ),
                    fn_t,
                ),
            ]),
            span.clone(),
        );
        let projected = Located::new(
            mono::Exp::Field(Box::new(record), "Inject".into()),
            span.clone(),
        );
        let reduced = reduce_head_apps_for_cjr(projected);
        assert!(matches!(reduced.node, mono::Exp::Prim(Prim::Int(7))));
        Ok(())
    }

    #[test]
    fn reduce_head_apps_drop_erased_witness_binder_before_runtime_arg() -> anyhow::Result<()> {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let meta_t = Located::new(
            mono::Typ::Record(vec![("NewState".into(), int_t.clone())]),
            span.clone(),
        );
        let body = Located::new(
            mono::Exp::Abs(
                "row".into(),
                meta_t.clone(),
                int_t.clone(),
                Box::new(Located::new(
                    mono::Exp::Field(
                        Box::new(Located::new(mono::Exp::Rel(0), span.clone())),
                        "NewState".into(),
                    ),
                    span.clone(),
                )),
            ),
            span.clone(),
        );
        let app = Located::new(
            mono::Exp::App(
                Box::new(Located::new(
                    mono::Exp::Abs("m".into(), meta_t, int_t, Box::new(body)),
                    span.clone(),
                )),
                Box::new(Located::new(mono::Exp::Record(vec![]), span.clone())),
            ),
            span,
        );

        let reduced = reduce_head_apps_for_cjr(app);
        assert!(matches!(
            reduced.node,
            mono::Exp::Abs(_, _, _, ref body)
                if matches!(
                    body.node,
                    mono::Exp::Field(ref inner, ref name)
                        if name == "NewState"
                            && matches!(inner.node, mono::Exp::Rel(0))
                )
        ));
        Ok(())
    }

    #[test]
    fn reduce_head_apps_drops_empty_record_witness_even_for_int_domain() -> anyhow::Result<()> {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let step = Located::new(
            mono::Exp::Abs(
                "n".into(),
                int_t.clone(),
                Located::new(
                    mono::Typ::Fun(Box::new(int_t.clone()), Box::new(int_t.clone())),
                    span.clone(),
                ),
                Box::new(Located::new(
                    mono::Exp::Abs(
                        "acc".into(),
                        int_t.clone(),
                        int_t.clone(),
                        Box::new(Located::new(
                            mono::Exp::Binop(
                                mono::BinopIntness::Int,
                                "+".into(),
                                Box::new(Located::new(mono::Exp::Rel(1), span.clone())),
                                Box::new(Located::new(mono::Exp::Rel(0), span.clone())),
                            ),
                            span.clone(),
                        )),
                    ),
                    span.clone(),
                )),
            ),
            span.clone(),
        );
        let malformed = Located::new(
            mono::Exp::App(
                Box::new(Located::new(
                    mono::Exp::App(
                        Box::new(Located::new(
                            mono::Exp::App(
                                Box::new(step),
                                Box::new(Located::new(mono::Exp::Record(vec![]), span.clone())),
                            ),
                            span.clone(),
                        )),
                        Box::new(Located::new(mono::Exp::Prim(Prim::Int(1)), span.clone())),
                    ),
                    span.clone(),
                )),
                Box::new(Located::new(mono::Exp::Prim(Prim::Int(0)), span.clone())),
            ),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(malformed);
        assert!(
            matches!(
                reduced.node,
                mono::Exp::Binop(_, ref op, ref left, ref right)
                    if op == "+"
                        && matches!(left.node, mono::Exp::Prim(Prim::Int(1)))
                        && matches!(right.node, mono::Exp::Prim(Prim::Int(0)))
            ),
            "unexpected reduced expression: {:?}",
            reduced.node
        );
        Ok(())
    }

    #[test]
    fn reduce_head_apps_preserves_real_zero_int_runtime_args() -> anyhow::Result<()> {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let step = Located::new(
            mono::Exp::Abs(
                "n".into(),
                int_t.clone(),
                Located::new(
                    mono::Typ::Fun(Box::new(int_t.clone()), Box::new(int_t.clone())),
                    span.clone(),
                ),
                Box::new(Located::new(
                    mono::Exp::Abs(
                        "acc".into(),
                        int_t.clone(),
                        int_t.clone(),
                        Box::new(Located::new(
                            mono::Exp::Binop(
                                mono::BinopIntness::Int,
                                "+".into(),
                                Box::new(Located::new(mono::Exp::Rel(1), span.clone())),
                                Box::new(Located::new(mono::Exp::Rel(0), span.clone())),
                            ),
                            span.clone(),
                        )),
                    ),
                    span.clone(),
                )),
            ),
            span.clone(),
        );
        let applied = Located::new(
            mono::Exp::App(
                Box::new(Located::new(
                    mono::Exp::App(
                        Box::new(step),
                        Box::new(Located::new(mono::Exp::Prim(Prim::Int(0)), span.clone())),
                    ),
                    span.clone(),
                )),
                Box::new(Located::new(mono::Exp::Prim(Prim::Int(1)), span.clone())),
            ),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(applied);
        assert!(matches!(
            reduced.node,
            mono::Exp::Binop(_, ref op, ref left, ref right)
                if op == "+"
                    && matches!(left.node, mono::Exp::Prim(Prim::Int(0)))
                    && matches!(right.node, mono::Exp::Prim(Prim::Int(1)))
        ));
        Ok(())
    }

    #[test]
    fn reduce_head_apps_preserves_real_unit_thunk_beta_reduction() -> anyhow::Result<()> {
        let span = Span::dummy();
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let applied = Located::new(
            mono::Exp::App(
                Box::new(Located::new(
                    mono::Exp::Abs(
                        "_".into(),
                        unit_t.clone(),
                        int_t,
                        Box::new(Located::new(mono::Exp::Rel(1), span.clone())),
                    ),
                    span.clone(),
                )),
                Box::new(Located::new(mono::Exp::Record(vec![]), span.clone())),
            ),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(applied);
        assert!(
            matches!(reduced.node, mono::Exp::Rel(0)),
            "unexpected reduced expression: {:?}",
            reduced.node
        );
        Ok(())
    }

    #[test]
    fn reduce_head_apps_pushes_unit_app_through_case_arm_binder() -> anyhow::Result<()> {
        let span = Span::dummy();
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let option_int_t = Located::new(mono::Typ::Option(Box::new(int_t.clone())), span.clone());
        let case = Located::new(
            mono::Exp::Case(
                Box::new(Located::new(mono::Exp::Rel(0), span.clone())),
                vec![
                    (
                        Located::new(
                            mono::Pat::Some(
                                int_t.clone(),
                                Box::new(Located::new(
                                    mono::Pat::Var("r".into(), int_t.clone()),
                                    span.clone(),
                                )),
                            ),
                            span.clone(),
                        ),
                        Located::new(
                            mono::Exp::Abs(
                                "_".into(),
                                unit_t.clone(),
                                int_t.clone(),
                                Box::new(Located::new(mono::Exp::Rel(1), span.clone())),
                            ),
                            span.clone(),
                        ),
                    ),
                    (
                        Located::new(mono::Pat::None(int_t.clone()), span.clone()),
                        Located::new(
                            mono::Exp::Abs(
                                "_".into(),
                                unit_t.clone(),
                                int_t.clone(),
                                Box::new(Located::new(mono::Exp::Prim(Prim::Int(0)), span.clone())),
                            ),
                            span.clone(),
                        ),
                    ),
                ],
                mono::CaseMeta {
                    disc: option_int_t.clone(),
                    result: Located::new(
                        mono::Typ::Fun(Box::new(unit_t.clone()), Box::new(int_t.clone())),
                        span.clone(),
                    ),
                },
            ),
            span.clone(),
        );
        let applied = Located::new(
            mono::Exp::App(
                Box::new(case),
                Box::new(Located::new(mono::Exp::Record(vec![]), span.clone())),
            ),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(applied);
        assert!(
            matches!(
                reduced.node,
                mono::Exp::Case(_, ref arms, _)
                    if matches!(arms[0].1.node, mono::Exp::Rel(0))
                        && matches!(arms[1].1.node, mono::Exp::Prim(Prim::Int(0)))
            ),
            "unexpected reduced expression: {:?}",
            reduced.node
        );
        Ok(())
    }

    #[test]
    fn reduce_head_apps_recovers_case_arm_projection_from_bound_row() -> anyhow::Result<()> {
        let span = Span::dummy();
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let channel_t = Located::new(
            mono::Typ::Ffi("Basis".into(), "channel".into()),
            span.clone(),
        );
        let client_t = Located::new(
            mono::Typ::Ffi("Basis".into(), "client".into()),
            span.clone(),
        );
        let inner_row_t = Located::new(
            mono::Typ::Record(vec![("Channel".into(), channel_t.clone())]),
            span.clone(),
        );
        let case_row_t = Located::new(
            mono::Typ::Record(vec![("T".into(), inner_row_t.clone())]),
            span.clone(),
        );
        let case = Located::new(
            mono::Exp::Case(
                Box::new(Located::new(mono::Exp::Rel(0), span.clone())),
                vec![(
                    Located::new(mono::Pat::Var("r".into(), case_row_t.clone()), span.clone()),
                    Located::new(
                        mono::Exp::Abs(
                            "_".into(),
                            unit_t.clone(),
                            channel_t.clone(),
                            Box::new(Located::new(
                                mono::Exp::Field(
                                    Box::new(Located::new(
                                        mono::Exp::Field(
                                            Box::new(Located::new(mono::Exp::Rel(2), span.clone())),
                                            "T".into(),
                                        ),
                                        span.clone(),
                                    )),
                                    "Channel".into(),
                                ),
                                span.clone(),
                            )),
                        ),
                        span.clone(),
                    ),
                )],
                mono::CaseMeta {
                    disc: case_row_t.clone(),
                    result: Located::new(
                        mono::Typ::Transaction(Box::new(channel_t.clone())),
                        span.clone(),
                    ),
                },
            ),
            span.clone(),
        );
        let applied = Located::new(
            mono::Exp::App(
                Box::new(case),
                Box::new(Located::new(mono::Exp::Record(vec![]), span.clone())),
            ),
            span.clone(),
        );

        let reduced = with_rel_types(vec![client_t], || reduce_head_apps_for_cjr(applied));
        assert!(
            matches!(
                reduced.node,
                mono::Exp::Case(_, ref arms, ref meta)
                    if matches!(meta.result.node, mono::Typ::Ffi(ref module, ref name) if module == "Basis" && name == "channel")
                        && matches!(
                            arms[0].1.node,
                            mono::Exp::Field(ref outer, ref channel_field)
                                if channel_field == "Channel"
                                    && matches!(
                                        outer.node,
                                        mono::Exp::Field(ref inner, ref t_field)
                                            if t_field == "T"
                                                && matches!(inner.node, mono::Exp::Rel(0))
                                    )
                        )
            ),
            "unexpected reduced expression: {:?}",
            reduced.node
        );
        Ok(())
    }

    #[test]
    fn reduce_head_apps_recovers_query_body_projection_from_row_binder() -> anyhow::Result<()> {
        let span = Span::dummy();
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let channel_t = Located::new(
            mono::Typ::Ffi("Basis".into(), "channel".into()),
            span.clone(),
        );
        let inner_row_t = Located::new(
            mono::Typ::Record(vec![("Channel".into(), channel_t.clone())]),
            span.clone(),
        );
        let malformed_body = Located::new(
            mono::Exp::Field(
                Box::new(Located::new(
                    mono::Exp::Field(
                        Box::new(Located::new(mono::Exp::Rel(0), span.clone())),
                        "T".into(),
                    ),
                    span.clone(),
                )),
                "Channel".into(),
            ),
            span.clone(),
        );
        let query = Located::new(
            mono::Exp::Query(mono::QueryMeta {
                exps: vec![("T".into(), inner_row_t)],
                tables: vec![],
                state: unit_t.clone(),
                query: Box::new(Located::new(mono::Exp::Record(vec![]), span.clone())),
                body: Box::new(malformed_body),
                initial: Box::new(Located::new(mono::Exp::Record(vec![]), span.clone())),
            }),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(query);
        assert!(
            matches!(
                reduced.node,
                mono::Exp::Query(ref qm)
                    if matches!(
                        qm.body.node,
                        mono::Exp::Field(ref outer, ref channel_field)
                            if channel_field == "Channel"
                                && matches!(
                                    outer.node,
                                    mono::Exp::Field(ref inner, ref t_field)
                                        if t_field == "T"
                                            && matches!(inner.node, mono::Exp::Rel(1))
                                )
                    )
            ),
            "unexpected reduced expression: {:?}",
            reduced.node
        );
        Ok(())
    }

    #[test]
    fn reduce_head_apps_yanks_field_through_let() -> anyhow::Result<()> {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let record_t = Located::new(
            mono::Typ::Record(vec![("Inject".into(), int_t.clone())]),
            span.clone(),
        );
        let bound = Located::new(mono::Exp::Prim(Prim::Int(9)), span.clone());
        let body = Located::new(
            mono::Exp::Record(vec![(
                "Inject".into(),
                Located::new(mono::Exp::Rel(0), span.clone()),
                int_t.clone(),
            )]),
            span.clone(),
        );
        let projected = Located::new(
            mono::Exp::Field(
                Box::new(Located::new(
                    mono::Exp::Let("r".into(), record_t, Box::new(bound), Box::new(body)),
                    span.clone(),
                )),
                "Inject".into(),
            ),
            span.clone(),
        );
        let reduced = reduce_head_apps_for_cjr(projected);
        match reduced.node {
            mono::Exp::Let(_, _, bound, body) => {
                assert!(matches!(bound.node, mono::Exp::Prim(Prim::Int(9))));
                assert!(matches!(body.node, mono::Exp::Rel(0)));
            }
            other => panic!("expected Let after field projection through let, got {other:?}"),
        }
        Ok(())
    }

    #[test]
    fn reduce_head_apps_projects_field_through_abs_then_beta_reduces() -> anyhow::Result<()> {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let record_t = Located::new(
            mono::Typ::Record(vec![("Inject".into(), int_t.clone())]),
            span.clone(),
        );
        let projected_app = Located::new(
            mono::Exp::App(
                Box::new(Located::new(
                    mono::Exp::Field(
                        Box::new(Located::new(
                            mono::Exp::Abs(
                                "r".into(),
                                int_t.clone(),
                                record_t,
                                Box::new(Located::new(
                                    mono::Exp::Record(vec![(
                                        "Inject".into(),
                                        Located::new(mono::Exp::Rel(0), span.clone()),
                                        int_t.clone(),
                                    )]),
                                    span.clone(),
                                )),
                            ),
                            span.clone(),
                        )),
                        "Inject".into(),
                    ),
                    span.clone(),
                )),
                Box::new(Located::new(mono::Exp::Prim(Prim::Int(11)), span.clone())),
            ),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(projected_app);
        assert!(matches!(reduced.node, mono::Exp::Prim(Prim::Int(11))));
        Ok(())
    }

    #[test]
    fn reduce_head_apps_projects_field_through_curried_abs_then_beta_reduces() -> anyhow::Result<()>
    {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let record_t = Located::new(
            mono::Typ::Record(vec![("Inject".into(), int_t.clone())]),
            span.clone(),
        );
        let unit_exp = Located::new(mono::Exp::Record(vec![]), span.clone());
        let projected_app = Located::new(
            mono::Exp::App(
                Box::new(Located::new(
                    mono::Exp::App(
                        Box::new(Located::new(
                            mono::Exp::Field(
                                Box::new(Located::new(
                                    mono::Exp::Abs(
                                        "_".into(),
                                        unit_t.clone(),
                                        Located::new(
                                            mono::Typ::Fun(
                                                Box::new(unit_t.clone()),
                                                Box::new(record_t.clone()),
                                            ),
                                            span.clone(),
                                        ),
                                        Box::new(Located::new(
                                            mono::Exp::Abs(
                                                "_".into(),
                                                unit_t.clone(),
                                                record_t,
                                                Box::new(Located::new(
                                                    mono::Exp::Record(vec![(
                                                        "Inject".into(),
                                                        Located::new(
                                                            mono::Exp::Prim(Prim::Int(13)),
                                                            span.clone(),
                                                        ),
                                                        int_t.clone(),
                                                    )]),
                                                    span.clone(),
                                                )),
                                            ),
                                            span.clone(),
                                        )),
                                    ),
                                    span.clone(),
                                )),
                                "Inject".into(),
                            ),
                            span.clone(),
                        )),
                        Box::new(unit_exp.clone()),
                    ),
                    span.clone(),
                )),
                Box::new(unit_exp),
            ),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(projected_app);
        assert!(matches!(reduced.node, mono::Exp::Prim(Prim::Int(13))));
        Ok(())
    }

    #[test]
    fn reduce_head_apps_projects_field_after_record_application() -> anyhow::Result<()> {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let fn_t = Located::new(
            mono::Typ::Fun(Box::new(int_t.clone()), Box::new(int_t.clone())),
            span.clone(),
        );
        let record = Located::new(
            mono::Exp::Record(vec![(
                "Inject".into(),
                Located::new(
                    mono::Exp::Abs(
                        "x".into(),
                        int_t.clone(),
                        int_t.clone(),
                        Box::new(Located::new(mono::Exp::Rel(0), span.clone())),
                    ),
                    span.clone(),
                ),
                fn_t,
            )]),
            span.clone(),
        );
        let projected = Located::new(
            mono::Exp::Field(
                Box::new(Located::new(
                    mono::Exp::App(
                        Box::new(record),
                        Box::new(Located::new(mono::Exp::Prim(Prim::Int(21)), span.clone())),
                    ),
                    span.clone(),
                )),
                "Inject".into(),
            ),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(projected);
        assert!(matches!(reduced.node, mono::Exp::Prim(Prim::Int(21))));
        Ok(())
    }

    #[test]
    fn reduce_head_apps_unwraps_singleton_function_record_before_applying() -> anyhow::Result<()> {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let fn_t = Located::new(
            mono::Typ::Fun(Box::new(unit_t.clone()), Box::new(int_t.clone())),
            span.clone(),
        );
        let unit_exp = Located::new(mono::Exp::Record(vec![]), span.clone());
        let wrapped = Located::new(
            mono::Exp::Record(vec![(
                "?".into(),
                Located::new(
                    mono::Exp::Abs(
                        "_".into(),
                        unit_t.clone(),
                        int_t.clone(),
                        Box::new(Located::new(mono::Exp::Prim(Prim::Int(33)), span.clone())),
                    ),
                    span.clone(),
                ),
                fn_t,
            )]),
            span.clone(),
        );
        let applied = Located::new(
            mono::Exp::App(Box::new(wrapped), Box::new(unit_exp)),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(applied);
        assert!(matches!(reduced.node, mono::Exp::Prim(Prim::Int(33))));
        Ok(())
    }

    #[test]
    fn cify_exp_preserves_three_argument_application_order() -> anyhow::Result<()> {
        let span = Span::dummy();
        let app = Located::new(
            mono::Exp::App(
                Box::new(Located::new(
                    mono::Exp::App(
                        Box::new(Located::new(
                            mono::Exp::App(
                                Box::new(Located::new(mono::Exp::Named(7), span.clone())),
                                Box::new(Located::new(mono::Exp::Prim(Prim::Int(1)), span.clone())),
                            ),
                            span.clone(),
                        )),
                        Box::new(Located::new(mono::Exp::Prim(Prim::Int(2)), span.clone())),
                    ),
                    span.clone(),
                )),
                Box::new(Located::new(mono::Exp::Prim(Prim::Int(3)), span.clone())),
            ),
            span.clone(),
        );

        let mut sm = Sm::new();
        let mut errors = ErrorReporter::new();
        let cexp = cify_exp(&app, &mut sm, &mut errors);
        assert!(!errors.has_errors());

        let Exp::App(_, args) = cexp.node else {
            anyhow::bail!("expected cify_exp to lower to Exp::App");
        };
        let ints: Vec<i64> = args
            .into_iter()
            .map(|arg| match arg.node {
                Exp::Prim(Prim::Int(i)) => Ok(i),
                other => anyhow::bail!("expected integer argument, got {other:?}"),
            })
            .collect::<anyhow::Result<_>>()?;

        assert_eq!(ints, vec![1, 2, 3]);
        Ok(())
    }

    #[test]
    fn cify_exp_saturates_named_residual_unit_thunk() -> anyhow::Result<()> {
        let span = Span::dummy();
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let named_t = Located::new(
            mono::Typ::Fun(
                Box::new(unit_t.clone()),
                Box::new(Located::new(
                    mono::Typ::Fun(Box::new(unit_t.clone()), Box::new(unit_t.clone())),
                    span.clone(),
                )),
            ),
            span.clone(),
        );
        let previous = CJRIZE_NAMED_TYPES.with(|slot| slot.borrow().clone());
        CJRIZE_NAMED_TYPES.with(|slot| {
            slot.borrow_mut().insert(7, named_t);
        });

        let app = Located::new(
            mono::Exp::App(
                Box::new(Located::new(mono::Exp::Named(7), span.clone())),
                Box::new(Located::new(mono::Exp::Record(vec![]), span.clone())),
            ),
            span.clone(),
        );

        let mut sm = Sm::new();
        let mut errors = ErrorReporter::new();
        let cexp = cify_exp(&app, &mut sm, &mut errors);
        CJRIZE_NAMED_TYPES.with(|slot| *slot.borrow_mut() = previous);
        assert!(!errors.has_errors());

        let Exp::App(_, args) = cexp.node else {
            anyhow::bail!("expected named unit-thunk app to stay an App");
        };
        assert_eq!(args.len(), 2);
        assert!(matches!(args[0].node, Exp::Record(_, ref fields) if fields.is_empty()));
        assert!(matches!(args[1].node, Exp::Record(_, ref fields) if fields.is_empty()));
        Ok(())
    }

    #[test]
    fn cify_exp_saturates_named_unit_then_transaction_thunk() -> anyhow::Result<()> {
        let span = Span::dummy();
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let string_t = Located::new(
            mono::Typ::Ffi("Basis".into(), "string".into()),
            span.clone(),
        );
        let named_t = Located::new(
            mono::Typ::Fun(
                Box::new(Located::new(
                    mono::Typ::Option(Box::new(int_t.clone())),
                    span.clone(),
                )),
                Box::new(Located::new(
                    mono::Typ::Fun(
                        Box::new(unit_t.clone()),
                        Box::new(Located::new(
                            mono::Typ::Transaction(Box::new(string_t)),
                            span.clone(),
                        )),
                    ),
                    span.clone(),
                )),
            ),
            span.clone(),
        );
        let previous = CJRIZE_NAMED_TYPES.with(|slot| slot.borrow().clone());
        CJRIZE_NAMED_TYPES.with(|slot| {
            slot.borrow_mut().insert(8, named_t);
        });

        let app = Located::new(
            mono::Exp::App(
                Box::new(Located::new(mono::Exp::Named(8), span.clone())),
                Box::new(Located::new(mono::Exp::None(int_t), span.clone())),
            ),
            span.clone(),
        );

        let mut sm = Sm::new();
        let mut errors = ErrorReporter::new();
        let cexp = cify_exp(&app, &mut sm, &mut errors);
        CJRIZE_NAMED_TYPES.with(|slot| *slot.borrow_mut() = previous);
        assert!(!errors.has_errors());

        let Exp::App(_, args) = cexp.node else {
            anyhow::bail!("expected named thunk app to stay an App");
        };
        assert_eq!(args.len(), 3);
        assert!(matches!(args[1].node, Exp::Record(_, ref fields) if fields.is_empty()));
        assert!(matches!(args[2].node, Exp::Record(_, ref fields) if fields.is_empty()));
        Ok(())
    }

    #[test]
    fn unravel_fun_keeps_explicit_unit_argument_before_transaction_thunk() -> anyhow::Result<()> {
        let span = Span::dummy();
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let mono_t = Located::new(
            mono::Typ::Transaction(Box::new(unit_t.clone())),
            span.clone(),
        );
        let body = Located::new(
            mono::Exp::Abs(
                "_".into(),
                unit_t.clone(),
                unit_t.clone(),
                Box::new(Located::new(mono::Exp::Record(vec![]), span.clone())),
            ),
            span.clone(),
        );
        let exp = Located::new(
            mono::Exp::Abs("x".into(), unit_t.clone(), mono_t.clone(), Box::new(body)),
            span.clone(),
        );

        let mut sm = Sm::new();
        let cjr_t = cify_typ(&mono_t, &mut sm);
        let mut args = Vec::new();
        let (ran, lowered_body) = unravel_fun(mono_t, cjr_t, exp, &span, &mut sm, &mut args);

        assert_eq!(args.len(), 2);
        assert!(matches!(args[0].1.node, Typ::Record(0)));
        assert!(matches!(args[1].1.node, Typ::Record(0)));
        assert!(matches!(ran.node, Typ::Record(0)));
        assert!(matches!(lowered_body.node, mono::Exp::Record(ref fields) if fields.is_empty()));
        Ok(())
    }

    #[test]
    fn unravel_fun_does_not_eta_expand_already_forced_transaction_app() -> anyhow::Result<()> {
        let span = Span::dummy();
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let string_t = Located::new(
            mono::Typ::Ffi("Basis".into(), "string".into()),
            span.clone(),
        );
        let named_t = Located::new(
            mono::Typ::Fun(
                Box::new(unit_t.clone()),
                Box::new(Located::new(
                    mono::Typ::Transaction(Box::new(string_t.clone())),
                    span.clone(),
                )),
            ),
            span.clone(),
        );
        let previous_raw = CJRIZE_RAW_NAMED_TYPES.with(|slot| slot.borrow().clone());
        CJRIZE_RAW_NAMED_TYPES.with(|slot| {
            slot.borrow_mut().insert(42, named_t);
        });

        let forced = Located::new(
            mono::Exp::App(
                Box::new(Located::new(
                    mono::Exp::App(
                        Box::new(Located::new(mono::Exp::Named(42), span.clone())),
                        Box::new(Located::new(mono::Exp::Record(vec![]), span.clone())),
                    ),
                    span.clone(),
                )),
                Box::new(Located::new(mono::Exp::Record(vec![]), span.clone())),
            ),
            span.clone(),
        );

        let mono_t = Located::new(mono::Typ::Transaction(Box::new(string_t)), span.clone());
        let mut sm = Sm::new();
        let cjr_t = cify_typ(&mono_t, &mut sm);
        let mut args = Vec::new();
        let (ran, lowered_body) = unravel_fun(mono_t, cjr_t, forced, &span, &mut sm, &mut args);
        CJRIZE_RAW_NAMED_TYPES.with(|slot| *slot.borrow_mut() = previous_raw);

        assert_eq!(args.len(), 1);
        assert!(matches!(args[0].1.node, Typ::Record(0)));
        assert!(matches!(ran.node, Typ::Ffi(ref m, ref x) if m == "Basis" && x == "string"));

        let (head, lowered_args) = strip_mono_app_spine(lowered_body);
        assert!(matches!(head.node, mono::Exp::Named(42)));
        assert_eq!(lowered_args.len(), 2);
        assert!(lowered_args
            .iter()
            .all(|arg| matches!(arg.node, mono::Exp::Record(ref fields) if fields.is_empty())));
        Ok(())
    }

    #[test]
    fn force_spurious_unit_thunk_preserves_transaction_thunks() -> anyhow::Result<()> {
        let span = Span::dummy();
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let thunk = Located::new(
            mono::Exp::Abs(
                "_".into(),
                unit_t,
                Located::new(
                    mono::Typ::Transaction(Box::new(int_t.clone())),
                    span.clone(),
                ),
                Box::new(Located::new(mono::Exp::Prim(Prim::Int(41)), span.clone())),
            ),
            span,
        );

        assert!(force_spurious_unit_thunk(&thunk).is_none());
        Ok(())
    }

    #[test]
    fn force_spurious_unit_thunk_peels_nested_unit_thunks() -> anyhow::Result<()> {
        let span = Span::dummy();
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let string_t = Located::new(
            mono::Typ::Ffi("Basis".into(), "string".into()),
            span.clone(),
        );
        let nested = Located::new(
            mono::Exp::Abs(
                "_".into(),
                unit_t.clone(),
                Located::new(
                    mono::Typ::Fun(Box::new(unit_t.clone()), Box::new(string_t.clone())),
                    span.clone(),
                ),
                Box::new(Located::new(
                    mono::Exp::Abs(
                        "_".into(),
                        unit_t.clone(),
                        string_t.clone(),
                        Box::new(Located::new(
                            mono::Exp::Prim(Prim::String(StringMode::Normal, "ok".into())),
                            span.clone(),
                        )),
                    ),
                    span.clone(),
                )),
            ),
            span.clone(),
        );

        let forced_outer = force_spurious_unit_thunk(&nested).expect("outer thunk should peel");
        assert!(matches!(forced_outer.node, mono::Exp::Abs(_, _, _, _)));

        let forced_inner =
            force_spurious_unit_thunk(&forced_outer).expect("inner thunk should force");
        assert!(matches!(
            forced_inner.node,
            mono::Exp::Prim(Prim::String(StringMode::Normal, ref value)) if value == "ok"
        ));
        Ok(())
    }

    #[test]
    fn project_missing_field_prefers_arg_that_can_supply_field() -> anyhow::Result<()> {
        let span = Span::dummy();
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let source_t = Located::new(mono::Typ::Source, span.clone());
        let meta_arg = Located::new(
            mono::Exp::Record(vec![(
                "NewState".into(),
                Located::new(mono::Exp::Prim(Prim::Int(0)), span.clone()),
                source_t.clone(),
            )]),
            span.clone(),
        );
        let acc_arg = Located::new(
            mono::Exp::Abs(
                "_".into(),
                unit_t.clone(),
                Located::new(
                    mono::Typ::Transaction(Box::new(unit_t.clone())),
                    span.clone(),
                ),
                Box::new(Located::new(mono::Exp::Record(vec![]), span.clone())),
            ),
            span.clone(),
        );

        let projected =
            project_missing_field_from_mono_args(&[meta_arg.clone(), acc_arg], "NewState", &span)
                .expect("project missing field");
        assert!(matches!(
            projected.node,
            mono::Exp::Field(inner, ref field)
                if field == "NewState"
                    && matches!(inner.node, mono::Exp::Record(ref fields)
                        if fields.iter().any(|(name, _, _)| name == "NewState"))
        ));
        Ok(())
    }

    #[test]
    fn project_missing_field_prefers_later_arg_when_multiple_supply_field() -> anyhow::Result<()> {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let first = Located::new(
            mono::Exp::Record(vec![(
                "A".into(),
                Located::new(mono::Exp::Prim(Prim::Int(7)), span.clone()),
                int_t.clone(),
            )]),
            span.clone(),
        );
        let second = Located::new(
            mono::Exp::Record(vec![(
                "A".into(),
                Located::new(mono::Exp::Prim(Prim::Int(9)), span.clone()),
                int_t.clone(),
            )]),
            span.clone(),
        );

        let projected = project_missing_field_from_mono_args(&[first, second], "A", &span)
            .expect("project missing field");
        assert!(matches!(
            projected.node,
            mono::Exp::Field(inner, ref field)
                if field == "A"
                    && matches!(inner.node, mono::Exp::Record(ref fields)
                        if fields.iter().any(|(name, exp, _)| name == "A"
                            && matches!(exp.node, mono::Exp::Prim(Prim::Int(9)))))
        ));
        Ok(())
    }

    #[test]
    fn project_missing_field_rejects_unrelated_tail_args() -> anyhow::Result<()> {
        let span = Span::dummy();
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let string_t = Located::new(
            mono::Typ::Ffi("Basis".into(), "string".into()),
            span.clone(),
        );
        let unrelated = Located::new(
            mono::Exp::Abs(
                "_".into(),
                unit_t.clone(),
                string_t,
                Box::new(Located::new(
                    mono::Exp::Prim(Prim::String(StringMode::Normal, String::new())),
                    span.clone(),
                )),
            ),
            span.clone(),
        );
        let proof = Located::new(mono::Exp::Record(vec![]), span.clone());

        assert!(
            project_missing_field_from_mono_args(&[proof, unrelated], "Name", &span).is_none(),
            "missing-field recovery should not invent a receiver from unrelated tail args"
        );
        Ok(())
    }

    #[test]
    fn project_missing_field_reuses_existing_projection_without_nesting() -> anyhow::Result<()> {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let arg = Located::new(
            mono::Exp::Field(
                Box::new(Located::new(
                    mono::Exp::Record(vec![(
                        "A".into(),
                        Located::new(mono::Exp::Prim(Prim::Int(7)), span.clone()),
                        int_t.clone(),
                    )]),
                    span.clone(),
                )),
                "A".into(),
            ),
            span.clone(),
        );

        let projected = project_missing_field_from_mono_args(&[arg.clone()], "A", &span)
            .expect("project missing field");
        assert!(matches!(
            projected.node,
            mono::Exp::Field(inner, ref field)
                if field == "A"
                    && matches!(inner.node, mono::Exp::Record(ref fields)
                        if fields.iter().any(|(name, _, _)| name == "A"))
        ));
        Ok(())
    }

    #[test]
    fn project_missing_field_skips_unstable_existing_projection() -> anyhow::Result<()> {
        let span = Span::dummy();
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let string_t = Located::new(
            mono::Typ::Ffi("Basis".into(), "string".into()),
            span.clone(),
        );
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let unstable = Located::new(
            mono::Exp::Field(
                Box::new(Located::new(
                    mono::Exp::Abs(
                        "_".into(),
                        unit_t.clone(),
                        string_t,
                        Box::new(Located::new(
                            mono::Exp::Prim(Prim::String(StringMode::Normal, String::new())),
                            span.clone(),
                        )),
                    ),
                    span.clone(),
                )),
                "A".into(),
            ),
            span.clone(),
        );
        let stable = Located::new(
            mono::Exp::Field(
                Box::new(Located::new(
                    mono::Exp::Record(vec![(
                        "A".into(),
                        Located::new(mono::Exp::Prim(Prim::Int(7)), span.clone()),
                        int_t.clone(),
                    )]),
                    span.clone(),
                )),
                "A".into(),
            ),
            span.clone(),
        );

        let projected =
            project_missing_field_from_mono_args(&[unstable, stable.clone()], "A", &span)
                .expect("project missing field");
        assert!(matches!(
            projected.node,
            mono::Exp::Field(inner, ref field)
                if field == "A"
                    && matches!(inner.node, mono::Exp::Record(ref fields)
                        if fields.iter().any(|(name, _, _)| name == "A"))
        ));
        Ok(())
    }

    #[test]
    fn project_missing_field_accepts_nested_record_from_existing_projection() -> anyhow::Result<()>
    {
        let span = Span::dummy();
        let string_t = Located::new(
            mono::Typ::Ffi("Basis".into(), "string".into()),
            span.clone(),
        );
        let meta_t = Located::new(
            mono::Typ::Record(vec![
                ("Name".into(), string_t.clone()),
                ("Show".into(), string_t.clone()),
            ]),
            span.clone(),
        );
        let holder = Located::new(
            mono::Exp::Field(
                Box::new(Located::new(
                    mono::Exp::Record(vec![(
                        "A".into(),
                        Located::new(
                            mono::Exp::Record(vec![
                                (
                                    "Name".into(),
                                    Located::new(
                                        mono::Exp::Prim(Prim::String(
                                            StringMode::Normal,
                                            "n".into(),
                                        )),
                                        span.clone(),
                                    ),
                                    string_t.clone(),
                                ),
                                (
                                    "Show".into(),
                                    Located::new(
                                        mono::Exp::Prim(Prim::String(
                                            StringMode::Normal,
                                            "call".into(),
                                        )),
                                        span.clone(),
                                    ),
                                    string_t.clone(),
                                ),
                            ]),
                            span.clone(),
                        ),
                        meta_t,
                    )]),
                    span.clone(),
                )),
                "A".into(),
            ),
            span.clone(),
        );

        let projected = project_missing_field_from_mono_args(&[holder], "Show", &span)
            .expect("project missing nested field");
        assert!(matches!(
            projected.node,
            mono::Exp::Field(inner, ref field)
                if field == "Show"
                    && matches!(inner.node, mono::Exp::Field(_, ref key) if key == "A")
        ));
        Ok(())
    }

    #[test]
    fn reduce_head_apps_projects_missing_field_from_concat_like_record_tail() -> anyhow::Result<()>
    {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let tail_record_t = Located::new(
            mono::Typ::Record(vec![("A".into(), int_t.clone())]),
            span.clone(),
        );
        let unit_exp = Located::new(mono::Exp::Record(vec![]), span.clone());
        let projected = Located::new(
            mono::Exp::Field(
                Box::new(Located::new(
                    mono::Exp::App(
                        Box::new(Located::new(
                            mono::Exp::App(
                                Box::new(Located::new(
                                    mono::Exp::Record(vec![(
                                        "B".into(),
                                        Located::new(mono::Exp::Prim(Prim::Int(9)), span.clone()),
                                        int_t.clone(),
                                    )]),
                                    span.clone(),
                                )),
                                Box::new(Located::new(
                                    mono::Exp::Abs(
                                        "_".into(),
                                        unit_t.clone(),
                                        tail_record_t,
                                        Box::new(Located::new(
                                            mono::Exp::Record(vec![(
                                                "A".into(),
                                                Located::new(
                                                    mono::Exp::Prim(Prim::Int(7)),
                                                    span.clone(),
                                                ),
                                                int_t.clone(),
                                            )]),
                                            span.clone(),
                                        )),
                                    ),
                                    span.clone(),
                                )),
                            ),
                            span.clone(),
                        )),
                        Box::new(unit_exp),
                    ),
                    span.clone(),
                )),
                "A".into(),
            ),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(projected);
        assert!(matches!(reduced.node, mono::Exp::Prim(Prim::Int(7))));
        Ok(())
    }

    #[test]
    fn reduce_head_apps_projects_missing_field_from_abs_tail_args() -> anyhow::Result<()> {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let b_record_t = Located::new(
            mono::Typ::Record(vec![("B".into(), int_t.clone())]),
            span.clone(),
        );
        let unit_exp = Located::new(mono::Exp::Record(vec![]), span.clone());
        let projected = Located::new(
            mono::Exp::Field(
                Box::new(Located::new(
                    mono::Exp::App(
                        Box::new(Located::new(
                            mono::Exp::App(
                                Box::new(Located::new(
                                    mono::Exp::Abs(
                                        "_".into(),
                                        unit_t.clone(),
                                        b_record_t,
                                        Box::new(Located::new(
                                            mono::Exp::Record(vec![(
                                                "B".into(),
                                                Located::new(
                                                    mono::Exp::Prim(Prim::Int(9)),
                                                    span.clone(),
                                                ),
                                                int_t.clone(),
                                            )]),
                                            span.clone(),
                                        )),
                                    ),
                                    span.clone(),
                                )),
                                Box::new(unit_exp.clone()),
                            ),
                            span.clone(),
                        )),
                        Box::new(Located::new(
                            mono::Exp::Record(vec![(
                                "A".into(),
                                Located::new(mono::Exp::Prim(Prim::Int(7)), span.clone()),
                                int_t.clone(),
                            )]),
                            span.clone(),
                        )),
                    ),
                    span.clone(),
                )),
                "A".into(),
            ),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(projected);
        assert!(matches!(reduced.node, mono::Exp::Prim(Prim::Int(7))));
        Ok(())
    }

    #[test]
    fn reduce_head_apps_projects_missing_field_past_erased_proof_arg() -> anyhow::Result<()> {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let projected = Located::new(
            mono::Exp::Field(
                Box::new(Located::new(
                    mono::Exp::App(
                        Box::new(Located::new(
                            mono::Exp::App(
                                Box::new(Located::new(
                                    mono::Exp::Record(vec![(
                                        "B".into(),
                                        Located::new(mono::Exp::Prim(Prim::Int(9)), span.clone()),
                                        int_t.clone(),
                                    )]),
                                    span.clone(),
                                )),
                                Box::new(Located::new(mono::Exp::Prim(Prim::Int(0)), span.clone())),
                            ),
                            span.clone(),
                        )),
                        Box::new(Located::new(
                            mono::Exp::Record(vec![(
                                "A".into(),
                                Located::new(mono::Exp::Prim(Prim::Int(7)), span.clone()),
                                int_t.clone(),
                            )]),
                            span.clone(),
                        )),
                    ),
                    span.clone(),
                )),
                "A".into(),
            ),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(projected);
        assert!(matches!(reduced.node, mono::Exp::Prim(Prim::Int(7))));
        Ok(())
    }

    #[test]
    fn reduce_head_apps_pushes_apps_through_missing_field_projection() -> anyhow::Result<()> {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let b_record_t = Located::new(
            mono::Typ::Record(vec![("B".into(), int_t.clone())]),
            span.clone(),
        );
        let unit_exp = Located::new(mono::Exp::Record(vec![]), span.clone());
        let projected_app = Located::new(
            mono::Exp::App(
                Box::new(Located::new(
                    mono::Exp::App(
                        Box::new(Located::new(
                            mono::Exp::Field(
                                Box::new(Located::new(
                                    mono::Exp::Abs(
                                        "_".into(),
                                        unit_t.clone(),
                                        b_record_t,
                                        Box::new(Located::new(
                                            mono::Exp::Record(vec![(
                                                "B".into(),
                                                Located::new(
                                                    mono::Exp::Prim(Prim::Int(9)),
                                                    span.clone(),
                                                ),
                                                int_t.clone(),
                                            )]),
                                            span.clone(),
                                        )),
                                    ),
                                    span.clone(),
                                )),
                                "A".into(),
                            ),
                            span.clone(),
                        )),
                        Box::new(unit_exp.clone()),
                    ),
                    span.clone(),
                )),
                Box::new(Located::new(
                    mono::Exp::Record(vec![(
                        "A".into(),
                        Located::new(mono::Exp::Prim(Prim::Int(7)), span.clone()),
                        int_t.clone(),
                    )]),
                    span.clone(),
                )),
            ),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(projected_app);
        assert!(matches!(reduced.node, mono::Exp::Prim(Prim::Int(7))));
        Ok(())
    }

    #[test]
    fn reduce_head_apps_redirects_nested_missing_field_to_tail_arg() -> anyhow::Result<()> {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let inject_fun_t = Located::new(
            mono::Typ::Fun(Box::new(unit_t.clone()), Box::new(int_t.clone())),
            span.clone(),
        );
        let meta_t = Located::new(
            mono::Typ::Record(vec![("Inject".into(), inject_fun_t.clone())]),
            span.clone(),
        );
        let b_record_t = Located::new(
            mono::Typ::Record(vec![("B".into(), meta_t.clone())]),
            span.clone(),
        );
        let unit_exp = Located::new(mono::Exp::Record(vec![]), span.clone());
        let projected_app = Located::new(
            mono::Exp::App(
                Box::new(Located::new(
                    mono::Exp::App(
                        Box::new(Located::new(
                            mono::Exp::Field(
                                Box::new(Located::new(
                                    mono::Exp::Field(
                                        Box::new(Located::new(
                                            mono::Exp::Abs(
                                                "_".into(),
                                                unit_t.clone(),
                                                b_record_t,
                                                Box::new(Located::new(
                                                    mono::Exp::Record(vec![(
                                                        "B".into(),
                                                        Located::new(
                                                            mono::Exp::Record(vec![(
                                                                "Inject".into(),
                                                                Located::new(
                                                                    mono::Exp::Abs(
                                                                        "_".into(),
                                                                        unit_t.clone(),
                                                                        int_t.clone(),
                                                                        Box::new(Located::new(
                                                                            mono::Exp::Prim(
                                                                                Prim::Int(9),
                                                                            ),
                                                                            span.clone(),
                                                                        )),
                                                                    ),
                                                                    span.clone(),
                                                                ),
                                                                inject_fun_t.clone(),
                                                            )]),
                                                            span.clone(),
                                                        ),
                                                        meta_t.clone(),
                                                    )]),
                                                    span.clone(),
                                                )),
                                            ),
                                            span.clone(),
                                        )),
                                        "A".into(),
                                    ),
                                    span.clone(),
                                )),
                                "Inject".into(),
                            ),
                            span.clone(),
                        )),
                        Box::new(unit_exp.clone()),
                    ),
                    span.clone(),
                )),
                Box::new(Located::new(
                    mono::Exp::Record(vec![(
                        "A".into(),
                        Located::new(
                            mono::Exp::Record(vec![(
                                "Inject".into(),
                                Located::new(
                                    mono::Exp::Abs(
                                        "_".into(),
                                        unit_t.clone(),
                                        int_t.clone(),
                                        Box::new(Located::new(
                                            mono::Exp::Prim(Prim::Int(7)),
                                            span.clone(),
                                        )),
                                    ),
                                    span.clone(),
                                ),
                                inject_fun_t,
                            )]),
                            span.clone(),
                        ),
                        meta_t,
                    )]),
                    span.clone(),
                )),
            ),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(projected_app);
        assert!(matches!(reduced.node, mono::Exp::Prim(Prim::Int(7))));
        Ok(())
    }

    #[test]
    fn reduce_head_apps_redirects_nested_missing_field_to_earlier_arg() -> anyhow::Result<()> {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let row_t = Located::new(
            mono::Typ::Record(vec![("A".into(), int_t.clone())]),
            span.clone(),
        );
        let unit_exp = Located::new(mono::Exp::Record(vec![]), span.clone());
        let projected_app = Located::new(
            mono::Exp::App(
                Box::new(Located::new(
                    mono::Exp::App(
                        Box::new(Located::new(
                            mono::Exp::Field(
                                Box::new(Located::new(
                                    mono::Exp::Abs(
                                        "_".into(),
                                        row_t.clone(),
                                        Located::new(
                                            mono::Typ::Fun(
                                                Box::new(unit_t.clone()),
                                                Box::new(int_t.clone()),
                                            ),
                                            span.clone(),
                                        ),
                                        Box::new(Located::new(
                                            mono::Exp::Abs(
                                                "_".into(),
                                                unit_t.clone(),
                                                int_t.clone(),
                                                Box::new(Located::new(
                                                    mono::Exp::Prim(Prim::Int(0)),
                                                    span.clone(),
                                                )),
                                            ),
                                            span.clone(),
                                        )),
                                    ),
                                    span.clone(),
                                )),
                                "A".into(),
                            ),
                            span.clone(),
                        )),
                        Box::new(Located::new(
                            mono::Exp::Record(vec![(
                                "A".into(),
                                Located::new(mono::Exp::Prim(Prim::Int(7)), span.clone()),
                                int_t.clone(),
                            )]),
                            span.clone(),
                        )),
                    ),
                    span.clone(),
                )),
                Box::new(unit_exp),
            ),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(projected_app);
        assert!(matches!(reduced.node, mono::Exp::Prim(Prim::Int(7))));
        Ok(())
    }

    #[test]
    fn reduce_head_apps_redirects_simple_missing_field_to_row_arg() -> anyhow::Result<()> {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let row_t = Located::new(
            mono::Typ::Record(vec![("A".into(), int_t.clone())]),
            span.clone(),
        );
        let curried_acc = Located::new(
            mono::Exp::Abs(
                "r".into(),
                row_t.clone(),
                Located::new(
                    mono::Typ::Fun(Box::new(unit_t.clone()), Box::new(int_t.clone())),
                    span.clone(),
                ),
                Box::new(Located::new(
                    mono::Exp::Abs(
                        "_".into(),
                        unit_t,
                        int_t.clone(),
                        Box::new(Located::new(mono::Exp::Prim(Prim::Int(0)), span.clone())),
                    ),
                    span.clone(),
                )),
            ),
            span.clone(),
        );
        let projected_app = Located::new(
            mono::Exp::App(
                Box::new(Located::new(
                    mono::Exp::Field(Box::new(curried_acc), "A".into()),
                    span.clone(),
                )),
                Box::new(Located::new(
                    mono::Exp::Record(vec![(
                        "A".into(),
                        Located::new(mono::Exp::Prim(Prim::Int(7)), span.clone()),
                        int_t,
                    )]),
                    span.clone(),
                )),
            ),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(projected_app);
        assert!(matches!(reduced.node, mono::Exp::Prim(Prim::Int(7))));
        Ok(())
    }

    #[test]
    fn reduce_head_apps_redirects_nested_missing_field_before_applying_mixed_record(
    ) -> anyhow::Result<()> {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let string_t = Located::new(
            mono::Typ::Ffi("Basis".into(), "string".into()),
            span.clone(),
        );
        let show_fun_t = Located::new(
            mono::Typ::Fun(Box::new(int_t.clone()), Box::new(string_t.clone())),
            span.clone(),
        );
        let meta_t = Located::new(
            mono::Typ::Record(vec![
                ("Name".into(), string_t.clone()),
                ("Show".into(), show_fun_t.clone()),
            ]),
            span.clone(),
        );
        let b_record_t = Located::new(
            mono::Typ::Record(vec![("B".into(), string_t.clone())]),
            span.clone(),
        );
        let projected_app = Located::new(
            mono::Exp::App(
                Box::new(Located::new(
                    mono::Exp::App(
                        Box::new(Located::new(
                            mono::Exp::Field(
                                Box::new(Located::new(
                                    mono::Exp::Field(
                                        Box::new(Located::new(
                                            mono::Exp::Abs(
                                                "_".into(),
                                                unit_t.clone(),
                                                b_record_t,
                                                Box::new(Located::new(
                                                    mono::Exp::Record(vec![(
                                                        "B".into(),
                                                        Located::new(
                                                            mono::Exp::Prim(Prim::String(
                                                                StringMode::Normal,
                                                                "ignored".into(),
                                                            )),
                                                            span.clone(),
                                                        ),
                                                        string_t.clone(),
                                                    )]),
                                                    span.clone(),
                                                )),
                                            ),
                                            span.clone(),
                                        )),
                                        "A".into(),
                                    ),
                                    span.clone(),
                                )),
                                "Show".into(),
                            ),
                            span.clone(),
                        )),
                        Box::new(Located::new(mono::Exp::Prim(Prim::Int(7)), span.clone())),
                    ),
                    span.clone(),
                )),
                Box::new(Located::new(
                    mono::Exp::Record(vec![(
                        "A".into(),
                        Located::new(
                            mono::Exp::Record(vec![
                                (
                                    "Name".into(),
                                    Located::new(
                                        mono::Exp::Prim(Prim::String(
                                            StringMode::Normal,
                                            "n".into(),
                                        )),
                                        span.clone(),
                                    ),
                                    string_t,
                                ),
                                (
                                    "Show".into(),
                                    Located::new(
                                        mono::Exp::Abs(
                                            "x".into(),
                                            int_t.clone(),
                                            Located::new(
                                                mono::Typ::Ffi("Basis".into(), "string".into()),
                                                span.clone(),
                                            ),
                                            Box::new(Located::new(
                                                mono::Exp::Prim(Prim::String(
                                                    StringMode::Normal,
                                                    "ok".into(),
                                                )),
                                                span.clone(),
                                            )),
                                        ),
                                        span.clone(),
                                    ),
                                    show_fun_t,
                                ),
                            ]),
                            span.clone(),
                        ),
                        meta_t,
                    )]),
                    span.clone(),
                )),
            ),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(projected_app);
        assert!(matches!(
            reduced.node,
            mono::Exp::Prim(Prim::String(StringMode::Normal, ref value)) if value == "ok"
        ));
        Ok(())
    }

    #[test]
    fn reduce_head_apps_preserves_direct_field_projection_on_projected_record() -> anyhow::Result<()>
    {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let string_t = Located::new(
            mono::Typ::Ffi("Basis".into(), "string".into()),
            span.clone(),
        );
        let show_fun_t = Located::new(
            mono::Typ::Fun(Box::new(int_t.clone()), Box::new(string_t.clone())),
            span.clone(),
        );
        let meta_t = Located::new(
            mono::Typ::Record(vec![("Show".into(), show_fun_t.clone())]),
            span.clone(),
        );
        let holder = Located::new(
            mono::Exp::Record(vec![(
                "A".into(),
                Located::new(
                    mono::Exp::Record(vec![(
                        "Show".into(),
                        Located::new(
                            mono::Exp::Abs(
                                "x".into(),
                                int_t.clone(),
                                string_t.clone(),
                                Box::new(Located::new(
                                    mono::Exp::Prim(Prim::String(StringMode::Normal, "ok".into())),
                                    span.clone(),
                                )),
                            ),
                            span.clone(),
                        ),
                        show_fun_t,
                    )]),
                    span.clone(),
                ),
                meta_t,
            )]),
            span.clone(),
        );
        let applied = Located::new(
            mono::Exp::App(
                Box::new(Located::new(
                    mono::Exp::Field(
                        Box::new(Located::new(
                            mono::Exp::Field(Box::new(holder), "A".into()),
                            span.clone(),
                        )),
                        "Show".into(),
                    ),
                    span.clone(),
                )),
                Box::new(Located::new(mono::Exp::Prim(Prim::Int(7)), span.clone())),
            ),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(applied);
        assert!(matches!(
            reduced.node,
            mono::Exp::Prim(Prim::String(StringMode::Normal, ref value)) if value == "ok"
        ));
        Ok(())
    }

    #[test]
    fn reduce_head_apps_projects_direct_field_from_head_before_applying_arg() -> anyhow::Result<()>
    {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let string_t = Located::new(
            mono::Typ::Ffi("Basis".into(), "string".into()),
            span.clone(),
        );
        let show_fun_t = Located::new(
            mono::Typ::Fun(Box::new(int_t.clone()), Box::new(string_t.clone())),
            span.clone(),
        );
        let meta_t = Located::new(
            mono::Typ::Record(vec![("Show".into(), show_fun_t.clone())]),
            span.clone(),
        );
        let holder = Located::new(
            mono::Exp::Record(vec![(
                "A".into(),
                Located::new(
                    mono::Exp::Record(vec![(
                        "Show".into(),
                        Located::new(
                            mono::Exp::Abs(
                                "x".into(),
                                int_t.clone(),
                                string_t.clone(),
                                Box::new(Located::new(
                                    mono::Exp::Prim(Prim::String(StringMode::Normal, "ok".into())),
                                    span.clone(),
                                )),
                            ),
                            span.clone(),
                        ),
                        show_fun_t,
                    )]),
                    span.clone(),
                ),
                meta_t,
            )]),
            span.clone(),
        );
        let malformed = Located::new(
            mono::Exp::Field(
                Box::new(Located::new(
                    mono::Exp::App(
                        Box::new(Located::new(
                            mono::Exp::Field(Box::new(holder), "A".into()),
                            span.clone(),
                        )),
                        Box::new(Located::new(mono::Exp::Prim(Prim::Int(7)), span.clone())),
                    ),
                    span.clone(),
                )),
                "Show".into(),
            ),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(malformed);
        assert!(matches!(
            reduced.node,
            mono::Exp::Prim(Prim::String(StringMode::Normal, ref value)) if value == "ok"
        ));
        Ok(())
    }

    #[test]
    fn reduce_head_apps_projects_missing_field_from_projected_record_arg() -> anyhow::Result<()> {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let string_t = Located::new(
            mono::Typ::Ffi("Basis".into(), "string".into()),
            span.clone(),
        );
        let show_fun_t = Located::new(
            mono::Typ::Fun(Box::new(int_t.clone()), Box::new(string_t.clone())),
            span.clone(),
        );
        let meta_t = Located::new(
            mono::Typ::Record(vec![("Show".into(), show_fun_t.clone())]),
            span.clone(),
        );
        let meta_arg = Located::new(
            mono::Exp::Field(
                Box::new(Located::new(
                    mono::Exp::Record(vec![(
                        "A".into(),
                        Located::new(
                            mono::Exp::Record(vec![(
                                "Show".into(),
                                Located::new(
                                    mono::Exp::Abs(
                                        "x".into(),
                                        int_t.clone(),
                                        string_t.clone(),
                                        Box::new(Located::new(
                                            mono::Exp::Prim(Prim::String(
                                                StringMode::Normal,
                                                "ok".into(),
                                            )),
                                            span.clone(),
                                        )),
                                    ),
                                    span.clone(),
                                ),
                                show_fun_t.clone(),
                            )]),
                            span.clone(),
                        ),
                        meta_t.clone(),
                    )]),
                    span.clone(),
                )),
                "A".into(),
            ),
            span.clone(),
        );
        let projected_app = Located::new(
            mono::Exp::App(
                Box::new(Located::new(
                    mono::Exp::Field(
                        Box::new(Located::new(
                            mono::Exp::App(
                                Box::new(Located::new(
                                    mono::Exp::Field(
                                        Box::new(Located::new(
                                            mono::Exp::Record(vec![(
                                                "A".into(),
                                                Located::new(
                                                    mono::Exp::Abs(
                                                        "m".into(),
                                                        meta_t.clone(),
                                                        meta_t.clone(),
                                                        Box::new(Located::new(
                                                            mono::Exp::Rel(0),
                                                            span.clone(),
                                                        )),
                                                    ),
                                                    span.clone(),
                                                ),
                                                Located::new(
                                                    mono::Typ::Fun(
                                                        Box::new(meta_t.clone()),
                                                        Box::new(meta_t.clone()),
                                                    ),
                                                    span.clone(),
                                                ),
                                            )]),
                                            span.clone(),
                                        )),
                                        "A".into(),
                                    ),
                                    span.clone(),
                                )),
                                Box::new(meta_arg),
                            ),
                            span.clone(),
                        )),
                        "Show".into(),
                    ),
                    span.clone(),
                )),
                Box::new(Located::new(mono::Exp::Prim(Prim::Int(7)), span.clone())),
            ),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(projected_app);
        assert!(matches!(
            reduced.node,
            mono::Exp::Prim(Prim::String(StringMode::Normal, ref value)) if value == "ok"
        ));
        Ok(())
    }

    #[test]
    fn reduce_head_apps_projects_rel_field_before_applying_args() -> anyhow::Result<()> {
        let span = Span::dummy();
        let projected = Located::new(
            mono::Exp::Field(
                Box::new(Located::new(
                    mono::Exp::App(
                        Box::new(Located::new(mono::Exp::Rel(0), span.clone())),
                        Box::new(Located::new(mono::Exp::Prim(Prim::Int(7)), span.clone())),
                    ),
                    span.clone(),
                )),
                "Show".into(),
            ),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(projected);
        assert!(matches!(
            reduced.node,
            mono::Exp::App(fun, arg)
                if matches!(&fun.node, mono::Exp::Field(inner, field)
                    if field == "Show" && matches!(inner.node, mono::Exp::Rel(0)))
                    && matches!(arg.node, mono::Exp::Prim(Prim::Int(7)))
        ));
        Ok(())
    }

    #[test]
    fn reduce_head_apps_keeps_projected_function_field_on_rel_projected_record(
    ) -> anyhow::Result<()> {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let string_t = Located::new(
            mono::Typ::Ffi("Basis".into(), "string".into()),
            span.clone(),
        );
        let show_fun_t = Located::new(
            mono::Typ::Fun(Box::new(int_t.clone()), Box::new(string_t.clone())),
            span.clone(),
        );
        let meta_t = Located::new(
            mono::Typ::Record(vec![("Show".into(), show_fun_t.clone())]),
            span.clone(),
        );
        let cols_t = Located::new(mono::Typ::Record(vec![("A".into(), meta_t)]), span.clone());
        let projected_app = Located::new(
            mono::Exp::App(
                Box::new(Located::new(
                    mono::Exp::Field(
                        Box::new(Located::new(
                            mono::Exp::Field(
                                Box::new(Located::new(mono::Exp::Rel(0), span.clone())),
                                "A".into(),
                            ),
                            span.clone(),
                        )),
                        "Show".into(),
                    ),
                    span.clone(),
                )),
                Box::new(Located::new(
                    mono::Exp::Field(
                        Box::new(Located::new(
                            mono::Exp::Record(vec![(
                                "A".into(),
                                Located::new(mono::Exp::Prim(Prim::Int(7)), span.clone()),
                                int_t,
                            )]),
                            span.clone(),
                        )),
                        "A".into(),
                    ),
                    span.clone(),
                )),
            ),
            span.clone(),
        );

        let reduced = with_rel_types(vec![cols_t], || reduce_head_apps_for_cjr(projected_app));
        assert!(matches!(
            reduced.node,
            mono::Exp::App(fun, arg)
                if matches!(&fun.node, mono::Exp::Field(inner, field)
                    if field == "Show"
                        && matches!(&inner.node, mono::Exp::Field(base, projected)
                            if projected == "A" && matches!(base.node, mono::Exp::Rel(0))))
                    && matches!(arg.node, mono::Exp::Prim(Prim::Int(7)))
        ));
        Ok(())
    }

    #[test]
    fn reduce_head_apps_keeps_projected_function_field_on_applied_record_builder(
    ) -> anyhow::Result<()> {
        let span = Span::dummy();
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let string_t = Located::new(
            mono::Typ::Ffi("Basis".into(), "string".into()),
            span.clone(),
        );
        let show_fun_t = Located::new(
            mono::Typ::Fun(Box::new(int_t.clone()), Box::new(string_t.clone())),
            span.clone(),
        );
        let show_fun = Located::new(
            mono::Exp::Abs(
                "x".into(),
                int_t.clone(),
                string_t.clone(),
                Box::new(Located::new(
                    mono::Exp::Prim(Prim::String(StringMode::Normal, "ok".into())),
                    span.clone(),
                )),
            ),
            span.clone(),
        );
        let record_t = Located::new(
            mono::Typ::Record(vec![("Show".into(), show_fun_t.clone())]),
            span.clone(),
        );
        let builder = Located::new(
            mono::Exp::Abs(
                "_meta".into(),
                unit_t.clone(),
                record_t,
                Box::new(Located::new(
                    mono::Exp::Record(vec![("Show".into(), show_fun, show_fun_t)]),
                    span.clone(),
                )),
            ),
            span.clone(),
        );
        let projected = Located::new(
            mono::Exp::App(
                Box::new(Located::new(
                    mono::Exp::Field(
                        Box::new(Located::new(
                            mono::Exp::App(
                                Box::new(builder),
                                Box::new(Located::new(mono::Exp::Record(vec![]), span.clone())),
                            ),
                            span.clone(),
                        )),
                        "Show".into(),
                    ),
                    span.clone(),
                )),
                Box::new(Located::new(mono::Exp::Prim(Prim::Int(7)), span.clone())),
            ),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(projected);
        assert!(matches!(
            reduced.node,
            mono::Exp::Prim(Prim::String(StringMode::Normal, ref value)) if value == "ok"
        ));
        Ok(())
    }

    #[test]
    fn reduce_head_apps_keeps_unresolved_question_record_intact() -> anyhow::Result<()> {
        let span = Span::dummy();
        let int_t = Located::new(mono::Typ::Ffi("Basis".into(), "int".into()), span.clone());
        let projected = Located::new(
            mono::Exp::Field(
                Box::new(Located::new(
                    mono::Exp::Record(vec![
                        (
                            "A".into(),
                            Located::new(mono::Exp::Prim(Prim::Int(1)), span.clone()),
                            int_t.clone(),
                        ),
                        (
                            "B".into(),
                            Located::new(mono::Exp::Prim(Prim::Int(2)), span.clone()),
                            int_t,
                        ),
                    ]),
                    span.clone(),
                )),
                "?".into(),
            ),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(projected);
        assert!(matches!(
            reduced.node,
            mono::Exp::Field(inner, ref field)
                if field == "?"
                    && matches!(inner.node, mono::Exp::Record(ref fields) if fields.len() == 2)
        ));
        Ok(())
    }

    #[test]
    fn resolve_question_slot_keeps_abs_placeholder_when_unresolved() -> anyhow::Result<()> {
        let span = Span::dummy();
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let string_t = Located::new(
            mono::Typ::Ffi("Basis".into(), "string".into()),
            span.clone(),
        );
        let abs = Located::new(
            mono::Exp::Abs(
                "_".into(),
                unit_t,
                string_t,
                Box::new(Located::new(
                    mono::Exp::Prim(Prim::String(StringMode::Html, String::new())),
                    span.clone(),
                )),
            ),
            span.clone(),
        );

        let resolved = resolve_question_slot(abs, &span);
        assert!(matches!(
            resolved.node,
            mono::Exp::Field(inner, ref field)
                if field == "?"
                    && matches!(inner.node, mono::Exp::Abs(_, _, _, _))
        ));
        Ok(())
    }

    #[test]
    fn reduce_head_apps_does_not_recurse_forever_on_unresolved_question_field() -> anyhow::Result<()>
    {
        let span = Span::dummy();
        let unit_t = Located::new(mono::Typ::Record(vec![]), span.clone());
        let string_t = Located::new(
            mono::Typ::Ffi("Basis".into(), "string".into()),
            span.clone(),
        );
        let projected = Located::new(
            mono::Exp::Field(
                Box::new(Located::new(
                    mono::Exp::Field(
                        Box::new(Located::new(
                            mono::Exp::Abs(
                                "_".into(),
                                unit_t,
                                string_t,
                                Box::new(Located::new(
                                    mono::Exp::Prim(Prim::String(StringMode::Html, String::new())),
                                    span.clone(),
                                )),
                            ),
                            span.clone(),
                        )),
                        "?".into(),
                    ),
                    span.clone(),
                )),
                "Name".into(),
            ),
            span.clone(),
        );

        let reduced = reduce_head_apps_for_cjr(projected);
        assert!(matches!(
            reduced.node,
            mono::Exp::Field(inner, ref field)
                if field == "Name"
                    && matches!(inner.node, mono::Exp::Field(_, ref question) if question == "?")
        ));
        Ok(())
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
        let c: Vec<(String, usize, Option<mono::LocTyp>)> =
            vec![("A".into(), 0, None), ("B".into(), 1, None)];
        assert_eq!(
            classify_constrs(1, &c),
            DatatypeKind::Enum,
            "all nullary => Enum (catches unary==0 check)"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn classify_constrs_option() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let unit = Located::dummy(mono::Typ::Ffi("Basis".into(), "unit".into()));
        let c: Vec<(String, usize, Option<mono::LocTyp>)> =
            vec![("None".into(), 0, None), ("Some".into(), 1, Some(unit))];
        assert_eq!(
            classify_constrs(1, &c),
            DatatypeKind::Option,
            "1 nullary && 1 unary => Option"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn classify_constrs_default() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let unit = Located::dummy(mono::Typ::Ffi("Basis".into(), "unit".into()));
        let c: Vec<(String, usize, Option<mono::LocTyp>)> = vec![
            ("A".into(), 0, None),
            ("B".into(), 0, None),
            ("C".into(), 1, Some(unit)),
        ];
        assert_eq!(
            classify_constrs(1, &c),
            DatatypeKind::Default,
            "2 nullary 1 unary => Default (catches nullary==1 && unary==1)"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn classify_constrs_recursive_unary_defaults() -> anyhow::Result<()> {
        let datatype_id = 7;
        let recursive_ref = Arc::new(Mutex::new(mono::DatatypeDef {
            kind: DatatypeKind::Default,
            constrs: vec![],
        }));
        let unit = Located::dummy(mono::Typ::Ffi("Basis".into(), "unit".into()));
        let recursive = Located::dummy(mono::Typ::Datatype(datatype_id, recursive_ref));
        let payload = Located::dummy(mono::Typ::Record(vec![
            ("_1".into(), unit),
            ("_2".into(), recursive),
        ]));
        let c: Vec<(String, usize, Option<mono::LocTyp>)> =
            vec![("Nil".into(), 0, None), ("Cons".into(), 1, Some(payload))];
        assert_eq!(
            classify_constrs(datatype_id, &c),
            DatatypeKind::Default,
            "recursive unary payloads must not be lowered as Option"
        );
        Ok(())
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
