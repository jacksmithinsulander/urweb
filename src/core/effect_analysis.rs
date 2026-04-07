//! Effect annotation pass for the Core IR.
//!
//! Determines which exported pages/actions/RPCs can write (side-effects),
//! read cookies, or push data (write+read via RPC), and annotates the
//! `DExport` declarations accordingly.
//!
//! Mirrors `effectize.sml`.

use std::collections::HashMap;

use crate::core::utilities::expression as exp_util;
use crate::core::*;
use crate::error_types::Span;
use crate::export::{Effect, ExportKind};
use crate::settings::Settings;

// ---------------------------------------------------------------------------
// State: maps from named-id → (span, source-name)
// ---------------------------------------------------------------------------

type EffectMap = HashMap<usize, (Span, String)>;

// ---------------------------------------------------------------------------
// Predicates (mirrors the inner `fun` helpers in effectize.sml)
// ---------------------------------------------------------------------------

/// True iff the given FFI reference could have a server-side side effect.
fn is_effectful_ffi(module: &str, function: &str, settings: &Settings) -> bool {
    settings.is_effectful(&(module.into(), function.into()))
        && !settings.is_client_only(&(module.into(), function.into()))
}

/// `couldWriteOnload evs e`: does expression node e (top-level) represent
/// an onload write effect?
fn could_write_onload_node(
    evs: &EffectMap,
    settings: &Settings,
    expression_node: &Expression,
) -> bool {
    match expression_node {
        Expression::Ffi(module, function) => is_effectful_ffi(module, function, settings),
        Expression::FfiApp(module, function, _) => is_effectful_ffi(module, function, settings),
        Expression::Named(name_id) => evs.contains_key(name_id),
        Expression::ServerCall(name_id, _, _, _) => evs.contains_key(name_id),
        _ => false,
    }
}

/// `couldWrite evs e`: does expression node e represent a write effect,
/// including onload handlers?
fn could_write_node(
    writers: &EffectMap,
    settings: &Settings,
    expression_node: &Expression,
) -> bool {
    match expression_node {
        Expression::Ffi(module, function) => is_effectful_ffi(module, function, settings),
        Expression::FfiApp(module, function, _) => is_effectful_ffi(module, function, settings),
        Expression::Named(name_id) => writers.contains_key(name_id),
        Expression::Record(xets) => xets.iter().any(|(name, body, _)| {
            // If the field is named "Onload", check if body could write on load
            if let Constructor::Name(field_name) = &name.node {
                if field_name == "Onload" {
                    return exp_util::exists(body, &|_k| false, &|_c| false, &|e_inner| {
                        could_write_onload_node(writers, settings, &e_inner.node)
                    });
                }
            }
            false
        }),
        _ => false,
    }
}

/// `couldReadCookie evs e`: does expression node e read a cookie/header/env var?
fn could_read_cookie_node(readers: &EffectMap, expression_node: &Expression) -> bool {
    match expression_node {
        Expression::Ffi(module, function) => module == "Basis" && function == "getCookie",
        Expression::FfiApp(module, function, _) => {
            module == "Basis" && (function == "getHeader" || function == "getenv")
        }
        Expression::Named(name_id) => readers.contains_key(name_id),
        Expression::ServerCall(name_id, _, _, _) => readers.contains_key(name_id),
        _ => false,
    }
}

/// `couldWriteWithRpc writers readers pushers e`: does e call an RPC that
/// itself reads+writes?
fn could_write_with_rpc_node(
    writers: &EffectMap,
    readers: &EffectMap,
    pushers: &EffectMap,
    expression_node: &Expression,
) -> bool {
    match expression_node {
        Expression::Named(name_id) => pushers.contains_key(name_id),
        Expression::ServerCall(name_id, _, _, _) => {
            writers.contains_key(name_id) && readers.contains_key(name_id)
        }
        _ => false,
    }
}

/// Walk expression e and check if any sub-expression satisfies the predicate.
fn exp_has_write(expression: &LocatedExpression, writers: &EffectMap, settings: &Settings) -> bool {
    exp_util::exists(expression, &|_k| false, &|_c| false, &|e_inner| {
        could_write_node(writers, settings, &e_inner.node)
    })
}

fn exp_has_read_cookie(expression: &LocatedExpression, readers: &EffectMap) -> bool {
    exp_util::exists(expression, &|_k| false, &|_c| false, &|e_inner| {
        could_read_cookie_node(readers, &e_inner.node)
    })
}

fn exp_has_push(
    expression: &LocatedExpression,
    writers: &EffectMap,
    readers: &EffectMap,
    pushers: &EffectMap,
) -> bool {
    exp_util::exists(expression, &|_k| false, &|_c| false, &|e_inner| {
        could_write_with_rpc_node(writers, readers, pushers, &e_inner.node)
    })
}

// ---------------------------------------------------------------------------
// Remove JS event handlers (the `dejs` transform in SML)
// ---------------------------------------------------------------------------

/// Strip out JS event-handler fields from record expressions (e.g., onClick,
/// onMouseOver, etc.), keeping only "Onload" and non-"On*" fields. This mirrors
/// the SML `dejs` transform which prevents JS-side effects from tainting the
/// server-side effectfulness analysis.
fn dejs(expression: LocatedExpression) -> LocatedExpression {
    let span = expression.span.clone();
    let new_node = match expression.node {
        Expression::Record(fields) => {
            let filtered = fields
                .into_iter()
                .filter(|(name, _, _)| match &name.node {
                    Constructor::Name(s) => s == "Onload" || !s.starts_with("On"),
                    _ => true,
                })
                .collect();
            Expression::Record(filtered)
        }
        other => other,
    };
    Located {
        node: new_node,
        span,
    }
}

/// Apply dejs recursively to all sub-expressions (shallow: only at record level).
/// The SML `dejs` is defined as a U.Exp.map; we mirror that here.
fn dejs_exp(expression: LocatedExpression) -> LocatedExpression {
    exp_util::map(
        expression,
        &|kind| kind,
        &|constructor| constructor,
        &|inner_expression| dejs(inner_expression),
    )
}

// ---------------------------------------------------------------------------
// Per-declaration analysis
// ---------------------------------------------------------------------------

fn analyze_decl(
    d: LocatedDeclaration,
    writers: &mut EffectMap,
    readers: &mut EffectMap,
    pushers: &mut EffectMap,
    settings: &Settings,
    errors: &mut Vec<(Span, String)>,
) -> LocatedDeclaration {
    let span = d.span.clone();
    match d.node {
        Declaration::Val(x, n, t, e, s) => {
            let e_dejs = dejs_exp(e.clone());
            if exp_has_write(&e_dejs, writers, settings) {
                writers.insert(n, (span.clone(), s.clone()));
            }
            if exp_has_read_cookie(&e_dejs, readers) {
                readers.insert(n, (span.clone(), s.clone()));
            }
            if exp_has_push(&e, writers, readers, pushers) {
                pushers.insert(n, (span.clone(), s.clone()));
            }
            Located {
                node: Declaration::Val(x, n, t, e, s),
                span,
            }
        }

        Declaration::ValRec(vis) => {
            // Precompute dejs_exp once per member to avoid repeated work in the fixed-point loop.
            let precomputed: Vec<(usize, LocatedExpression, LocatedExpression, String)> = vis
                .iter()
                .map(|(_, n, _, e, s)| (*n, dejs_exp(e.clone()), e.clone(), s.clone()))
                .collect();
            // Fixed-point: iterate until no new additions (bounded to prevent runaway mutants).
            const MAX_VALREC_ITERATIONS: usize = 10_000;
            for _ in 0..MAX_VALREC_ITERATIONS {
                let mut changed = false;
                for (n, e_dejs, e, s) in &precomputed {
                    if exp_has_write(e_dejs, writers, settings) && !writers.contains_key(n) {
                        writers.insert(*n, (span.clone(), s.clone()));
                        changed = true;
                    }
                    if exp_has_read_cookie(e_dejs, readers) && !readers.contains_key(n) {
                        readers.insert(*n, (span.clone(), s.clone()));
                        changed = true;
                    }
                    if exp_has_push(e, writers, readers, pushers) && !pushers.contains_key(n) {
                        pushers.insert(*n, (span.clone(), s.clone()));
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }
            Located {
                node: Declaration::ValRec(vis),
                span,
            }
        }

        Declaration::Export(ExportKind::Link(_), n, _) => {
            // Link exports accessed via GET — warn if they could cause side effects
            if let Some((loc, s)) = writers.get(&n) {
                if !settings.is_safe_get(s) {
                    errors.push((
                        loc.clone(),
                        format!(
                            "A handler (URI prefix \"{}\") accessible via GET \
                             could cause side effects; try accessing it only via forms, \
                             removing it from the signature of the main program module, \
                             or whitelisting it with the 'safeGet' .urp directive",
                            s
                        ),
                    ));
                }
            }
            let effect = compute_effect(n, writers, readers);
            let has_state = pushers.contains_key(&n);
            Located {
                node: Declaration::Export(ExportKind::Link(effect), n, has_state),
                span,
            }
        }

        Declaration::Export(ExportKind::Action(_), n, _) => {
            let effect = compute_effect(n, writers, readers);
            let has_state = pushers.contains_key(&n);
            Located {
                node: Declaration::Export(ExportKind::Action(effect), n, has_state),
                span,
            }
        }

        Declaration::Export(ExportKind::Rpc(_), n, _) => {
            let effect = compute_effect(n, writers, readers);
            let has_state = pushers.contains_key(&n);
            Located {
                node: Declaration::Export(ExportKind::Rpc(effect), n, has_state),
                span,
            }
        }

        Declaration::Export(ExportKind::Extern(_), n, _) => {
            let effect = compute_effect(n, writers, readers);
            let has_state = pushers.contains_key(&n);
            Located {
                node: Declaration::Export(ExportKind::Extern(effect), n, has_state),
                span,
            }
        }

        other => Located { node: other, span },
    }
}

fn compute_effect(n: usize, writers: &EffectMap, readers: &EffectMap) -> Effect {
    match (writers.contains_key(&n), readers.contains_key(&n)) {
        (true, true) => Effect::ReadCookieWrite,
        (true, false) => Effect::ReadWrite,
        (false, _) => Effect::ReadOnly,
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Annotate all `DExport` declarations in `file` with correct effect information.
///
/// Returns the annotated file and a list of errors (span + message) for any
/// GET-accessible handlers that could cause side effects.
pub fn effectize(file: File, settings: &Settings) -> (File, Vec<(Span, String)>) {
    let mut writers: EffectMap = HashMap::new();
    let mut readers: EffectMap = HashMap::new();
    let mut pushers: EffectMap = HashMap::new();
    let mut errors = Vec::new();

    let result = file
        .into_iter()
        .map(|d| {
            analyze_decl(
                d,
                &mut writers,
                &mut readers,
                &mut pushers,
                settings,
                &mut errors,
            )
        })
        .collect();

    (result, errors)
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::core::{Constructor, Declaration, Expression};
    use crate::error_types::{Located, Span};
    use crate::export::{Effect, ExportKind};
    use crate::primitives::Prim;
    use crate::settings::{FailureMode, Settings};

    use super::*;

    fn dummy_span() -> Span {
        Span::dummy()
    }

    #[test]
    fn is_effectful_ffi_true_when_effectful_not_client_only() {
        let s = Settings::new();
        assert!(is_effectful_ffi("Basis", "dml", &s));
    }

    #[test]
    fn is_effectful_ffi_false_when_client_only() {
        let s = Settings::new();
        assert!(!is_effectful_ffi("Basis", "recv", &s));
    }

    #[test]
    fn is_effectful_ffi_false_when_neither() {
        let s = Settings::new();
        assert!(!is_effectful_ffi("Other", "foo", &s));
    }

    #[test]
    fn could_write_onload_node_ffi() {
        let s = Settings::new();
        let evs: EffectMap = HashMap::new();
        assert!(could_write_onload_node(
            &evs,
            &s,
            &Expression::Ffi("Basis".into(), "dml".into())
        ));
    }

    #[test]
    fn could_write_onload_node_ffi_app() {
        let s = Settings::new();
        let evs: EffectMap = HashMap::new();
        let args = vec![(
            Located::dummy(Expression::Prim(Prim::Int(0))),
            Located::dummy(Constructor::Unit),
        )];
        assert!(could_write_onload_node(
            &evs,
            &s,
            &Expression::FfiApp("Basis".into(), "dml".into(), args)
        ));
    }

    #[test]
    fn could_write_onload_node_named_in_evs() {
        let s = Settings::new();
        let mut evs: EffectMap = HashMap::new();
        evs.insert(42, (dummy_span(), "x".into()));
        assert!(could_write_onload_node(&evs, &s, &Expression::Named(42)));
        assert!(!could_write_onload_node(&evs, &s, &Expression::Named(99)));
    }

    #[test]
    fn could_write_onload_node_server_call() {
        let s = Settings::new();
        let mut evs: EffectMap = HashMap::new();
        evs.insert(1, (dummy_span(), "f".into()));
        assert!(could_write_onload_node(
            &evs,
            &s,
            &Expression::ServerCall(
                1,
                vec![],
                Located::dummy(Constructor::Unit),
                FailureMode::Error
            )
        ));
    }

    #[test]
    fn could_write_onload_node_other_false() {
        let s = Settings::new();
        let evs: EffectMap = HashMap::new();
        assert!(!could_write_onload_node(
            &evs,
            &s,
            &Expression::Prim(Prim::Int(0))
        ));
    }

    #[test]
    fn could_write_node_ffi() {
        // Catches mutant: delete match arm Expression::Ffi in could_write_node.
        let s = Settings::new();
        let writers: EffectMap = HashMap::new();
        assert!(could_write_node(
            &writers,
            &s,
            &Expression::Ffi("Basis".into(), "dml".into())
        ));
    }

    #[test]
    fn could_write_node_named() {
        let s = Settings::new();
        let mut writers: EffectMap = HashMap::new();
        writers.insert(10, (dummy_span(), "w".into()));
        assert!(could_write_node(&writers, &s, &Expression::Named(10)));
    }

    #[test]
    fn could_write_node_record_onload_with_write() {
        let s = Settings::new();
        let mut writers: EffectMap = HashMap::new();
        writers.insert(7, (dummy_span(), "onload".into()));
        let onload_name = Located::dummy(Constructor::Name("Onload".into()));
        let body_with_write = Located::dummy(Expression::Named(7));
        let unit_ty = Located::dummy(Constructor::Unit);
        let record = Expression::Record(vec![(onload_name, body_with_write, unit_ty.clone())]);
        assert!(could_write_node(&writers, &s, &record));
    }

    #[test]
    fn could_write_node_record_onload_no_write() {
        let s = Settings::new();
        let writers: EffectMap = HashMap::new();
        let onload_name = Located::dummy(Constructor::Name("Onload".into()));
        let body = Located::dummy(Expression::Prim(Prim::Int(0)));
        let unit_ty = Located::dummy(Constructor::Unit);
        let record = Expression::Record(vec![(onload_name, body, unit_ty)]);
        assert!(!could_write_node(&writers, &s, &record));
    }

    #[test]
    fn could_read_cookie_node_ffi_get_cookie() {
        let readers: EffectMap = HashMap::new();
        assert!(could_read_cookie_node(
            &readers,
            &Expression::Ffi("Basis".into(), "getCookie".into())
        ));
        assert!(!could_read_cookie_node(
            &readers,
            &Expression::Ffi("Basis".into(), "other".into())
        ));
    }

    #[test]
    fn could_read_cookie_node_ffi_app_get_header_getenv() {
        let readers: EffectMap = HashMap::new();
        let args = vec![(
            Located::dummy(Expression::Prim(Prim::Int(0))),
            Located::dummy(Constructor::Unit),
        )];
        assert!(could_read_cookie_node(
            &readers,
            &Expression::FfiApp("Basis".into(), "getHeader".into(), args.clone())
        ));
        assert!(could_read_cookie_node(
            &readers,
            &Expression::FfiApp("Basis".into(), "getenv".into(), args)
        ));
    }

    #[test]
    fn could_read_cookie_node_named_and_server_call() {
        let mut readers: EffectMap = HashMap::new();
        readers.insert(5, (dummy_span(), "r".into()));
        assert!(could_read_cookie_node(&readers, &Expression::Named(5)));
        assert!(could_read_cookie_node(
            &readers,
            &Expression::ServerCall(
                5,
                vec![],
                Located::dummy(Constructor::Unit),
                FailureMode::Error
            )
        ));
    }

    #[test]
    fn could_write_with_rpc_node_named_pusher() {
        let writers: EffectMap = HashMap::new();
        let readers: EffectMap = HashMap::new();
        let mut pushers: EffectMap = HashMap::new();
        pushers.insert(3, (dummy_span(), "p".into()));
        assert!(could_write_with_rpc_node(
            &writers,
            &readers,
            &pushers,
            &Expression::Named(3)
        ));
    }

    #[test]
    fn could_write_with_rpc_node_server_call_both() {
        let mut writers: EffectMap = HashMap::new();
        let mut readers: EffectMap = HashMap::new();
        writers.insert(1, (dummy_span(), "w".into()));
        readers.insert(1, (dummy_span(), "r".into()));
        let pushers: EffectMap = HashMap::new();
        assert!(could_write_with_rpc_node(
            &writers,
            &readers,
            &pushers,
            &Expression::ServerCall(
                1,
                vec![],
                Located::dummy(Constructor::Unit),
                FailureMode::Error
            )
        ));
    }

    #[test]
    fn could_write_with_rpc_node_server_call_writer_only_false() {
        let mut writers: EffectMap = HashMap::new();
        writers.insert(1, (dummy_span(), "w".into()));
        let readers: EffectMap = HashMap::new();
        let pushers: EffectMap = HashMap::new();
        assert!(!could_write_with_rpc_node(
            &writers,
            &readers,
            &pushers,
            &Expression::ServerCall(
                1,
                vec![],
                Located::dummy(Constructor::Unit),
                FailureMode::Error
            )
        ));
    }

    #[test]
    fn exp_has_write_nested() {
        let s = Settings::new();
        let mut writers: EffectMap = HashMap::new();
        writers.insert(2, (dummy_span(), "x".into()));
        let e = Located::dummy(Expression::Let(
            "a".into(),
            Located::dummy(Constructor::Unit),
            Box::new(Located::dummy(Expression::Named(2))),
            Box::new(Located::dummy(Expression::Rel(0))),
        ));
        assert!(exp_has_write(&e, &writers, &s));
    }

    #[test]
    fn exp_has_read_cookie_nested() {
        let mut readers: EffectMap = HashMap::new();
        readers.insert(3, (dummy_span(), "y".into()));
        let e = Located::dummy(Expression::App(
            Box::new(Located::dummy(Expression::Named(3))),
            Box::new(Located::dummy(Expression::Rel(0))),
        ));
        assert!(exp_has_read_cookie(&e, &readers));
    }

    #[test]
    fn exp_has_push_nested() {
        let mut pushers: EffectMap = HashMap::new();
        pushers.insert(4, (dummy_span(), "z".into()));
        let writers: EffectMap = HashMap::new();
        let readers: EffectMap = HashMap::new();
        let e = Located::dummy(Expression::Named(4));
        assert!(exp_has_push(&e, &writers, &readers, &pushers));
    }

    #[test]
    fn dejs_keeps_onload_strips_on_click() {
        let onload = Located::dummy(Constructor::Name("Onload".into()));
        let onclick = Located::dummy(Constructor::Name("OnClick".into())); // capital O to match starts_with("On")
        let other = Located::dummy(Constructor::Name("value".into()));
        let unit_ty = Located::dummy(Constructor::Unit);
        let prim = Located::dummy(Expression::Prim(Prim::Int(0)));
        let record = Located::dummy(Expression::Record(vec![
            (onload.clone(), prim.clone(), unit_ty.clone()),
            (onclick, prim.clone(), unit_ty.clone()),
            (other.clone(), prim, unit_ty),
        ]));
        let out = dejs(record);
        let fields = match &out.node {
            Expression::Record(fs) => fs,
            _ => panic!("expected Record"),
        };
        let names: Vec<&str> = fields
            .iter()
            .map(|(c, _, _)| match &c.node {
                Constructor::Name(s) => s.as_str(),
                _ => "",
            })
            .collect();
        assert_eq!(
            names,
            ["Onload", "value"],
            "Onload and value kept, onClick stripped"
        );
    }

    #[test]
    fn dejs_non_record_unchanged() {
        let prim = Located::dummy(Expression::Prim(Prim::Int(42)));
        let out = dejs(prim.clone());
        assert!(matches!(out.node, Expression::Prim(Prim::Int(42))));
    }

    #[test]
    fn effectize_annotates_export_effect() {
        let s = Settings::new();
        let span = Span::dummy();
        let file: File = vec![
            Located::new(
                Declaration::Val(
                    "main".into(),
                    100,
                    Located::dummy(Constructor::Unit),
                    Located::dummy(Expression::FfiApp("Basis".into(), "dml".into(), vec![])),
                    "main".into(),
                ),
                span.clone(),
            ),
            Located::new(
                Declaration::Export(ExportKind::Action(Effect::ReadOnly), 100, false),
                span,
            ),
        ];
        let (out, errs) = effectize(file, &s);
        assert!(errs.is_empty());
        let export = out
            .iter()
            .find(|d| matches!(d.node, Declaration::Export(_, _, _)))
            .unwrap();
        match &export.node {
            Declaration::Export(ExportKind::Action(effect), n, has_state) => {
                assert_eq!(*n, 100);
                assert_eq!(*effect, Effect::ReadWrite);
                assert!(!*has_state);
            }
            _ => panic!("expected Action export with effect"),
        }
    }

    #[test]
    fn effectize_annotates_readonly_when_no_write() {
        // Catches mutant: replace exp_has_write -> bool with true.
        let s = Settings::new();
        let span = Span::dummy();
        let file: File = vec![
            Located::new(
                Declaration::Val(
                    "main".into(),
                    100,
                    Located::dummy(Constructor::Unit),
                    Located::dummy(Expression::Prim(Prim::Int(0))),
                    "main".into(),
                ),
                span.clone(),
            ),
            Located::new(
                Declaration::Export(ExportKind::Action(Effect::ReadOnly), 100, false),
                span,
            ),
        ];
        let (out, errs) = effectize(file, &s);
        assert!(errs.is_empty());
        let export = out
            .iter()
            .find(|d| matches!(d.node, Declaration::Export(_, _, _)))
            .unwrap();
        match &export.node {
            Declaration::Export(ExportKind::Action(effect), _, _) => {
                assert_eq!(*effect, Effect::ReadOnly);
            }
            _ => panic!("expected Action export"),
        }
    }

    #[test]
    fn effectize_valrec_fixed_point_and_writer_conditions() {
        // Catches mutants: && with ||, delete ! in ValRec analyze_decl.
        // ValRec: a has write, b has no write. Export b -> ReadOnly.
        // If we wrongly add b to writers (&& -> ||), export would be ReadWrite.
        let s = Settings::new();
        let span = Span::dummy();
        let file: File = vec![
            Located::new(
                Declaration::ValRec(vec![
                    (
                        "a".into(),
                        10,
                        Located::dummy(Constructor::Unit),
                        Located::dummy(Expression::FfiApp("Basis".into(), "dml".into(), vec![])),
                        "a".into(),
                    ),
                    (
                        "b".into(),
                        11,
                        Located::dummy(Constructor::Unit),
                        Located::dummy(Expression::Prim(Prim::Int(0))),
                        "b".into(),
                    ),
                ]),
                span.clone(),
            ),
            Located::new(
                Declaration::Export(ExportKind::Action(Effect::ReadOnly), 11, false),
                span.clone(),
            ),
            Located::new(
                Declaration::Export(ExportKind::Action(Effect::ReadOnly), 10, false),
                span,
            ),
        ];
        let (out, errs) = effectize(file, &s);
        assert!(errs.is_empty());
        let exports: Vec<_> = out
            .iter()
            .filter(|d| matches!(d.node, Declaration::Export(_, _, _)))
            .collect();
        let exp_b = exports
            .iter()
            .find(|d| matches!(&d.node, Declaration::Export(_, n, _) if *n == 11));
        match exp_b.unwrap().node {
            Declaration::Export(ExportKind::Action(effect), 11, _) => {
                assert_eq!(
                    effect,
                    Effect::ReadOnly,
                    "b has no write (catches && -> || mutant)"
                );
            }
            _ => panic!("expected Action export for b"),
        }
        let exp_a = exports
            .iter()
            .find(|d| matches!(&d.node, Declaration::Export(_, n, _) if *n == 10));
        match exp_a.unwrap().node {
            Declaration::Export(ExportKind::Action(effect), 10, _) => {
                assert_eq!(
                    effect,
                    Effect::ReadWrite,
                    "a has write, must be in writers (catches delete ! in writers.contains_key)"
                );
            }
            _ => panic!("expected Action export for a"),
        }
    }

    #[test]
    fn effectize_valrec_both_write_and_read_cookie() {
        // Catches mutant: exp_has_read_cookie && !readers (line 219).
        // Member with both dml and getCookie -> must be in writers AND readers -> ReadCookieWrite.
        // If we fail to add to readers, effect would be ReadWrite.
        let s = Settings::new();
        let span = Span::dummy();
        let unit_ty = Located::dummy(Constructor::Unit);
        let body = Expression::Let(
            "_".into(),
            unit_ty.clone(),
            Box::new(Located::dummy(Expression::FfiApp(
                "Basis".into(),
                "dml".into(),
                vec![],
            ))),
            Box::new(Located::dummy(Expression::Ffi(
                "Basis".into(),
                "getCookie".into(),
            ))),
        );
        let file: File = vec![
            Located::new(
                Declaration::ValRec(vec![(
                    "both".into(),
                    14,
                    Located::dummy(Constructor::Unit),
                    Located::dummy(body),
                    "both".into(),
                )]),
                span.clone(),
            ),
            Located::new(
                Declaration::Export(ExportKind::Action(Effect::ReadOnly), 14, false),
                span,
            ),
        ];
        let (out, errs) = effectize(file, &s);
        assert!(errs.is_empty());
        let export = out
            .iter()
            .find(|d| matches!(&d.node, Declaration::Export(_, 14, _)))
            .unwrap();
        match &export.node {
            Declaration::Export(ExportKind::Action(effect), 14, _) => {
                assert_eq!(
                    *effect,
                    Effect::ReadCookieWrite,
                    "member with dml+getCookie must be in writers and readers (catches line 219 && mutant)"
                );
            }
            _ => panic!("expected Export(Action(ReadCookieWrite), 14, _)"),
        }
    }

    #[test]
    fn effectize_valrec_push_populates_pushers() {
        // Catches mutant: exp_has_push && !pushers.contains_key -> || would wrongly add.
        // ValRec: 10 calls 11 via ServerCall; 11 has dml+getCookie (writers+readers).
        // So 10's body has ServerCall(11) -> could_write_with_rpc true -> 10 gets into pushers.
        let s = Settings::new();
        let span = Span::dummy();
        let unit_ty = Located::dummy(Constructor::Unit);
        let body_11 = Expression::Let(
            "_".into(),
            unit_ty.clone(),
            Box::new(Located::dummy(Expression::FfiApp(
                "Basis".into(),
                "dml".into(),
                vec![],
            ))),
            Box::new(Located::dummy(Expression::Ffi(
                "Basis".into(),
                "getCookie".into(),
            ))),
        );
        let body_10 = Expression::ServerCall(11, vec![], unit_ty.clone(), FailureMode::Error);
        let file: File = vec![
            Located::new(
                Declaration::ValRec(vec![
                    (
                        "caller".into(),
                        10,
                        unit_ty.clone(),
                        Located::dummy(body_10),
                        "caller".into(),
                    ),
                    (
                        "callee".into(),
                        11,
                        unit_ty,
                        Located::dummy(body_11),
                        "callee".into(),
                    ),
                ]),
                span.clone(),
            ),
            Located::new(
                Declaration::Export(ExportKind::Action(Effect::ReadOnly), 10, false),
                span,
            ),
        ];
        let (out, errs) = effectize(file, &s);
        assert!(errs.is_empty());
        let export = out
            .iter()
            .find(|d| matches!(&d.node, Declaration::Export(_, n, _) if *n == 10))
            .unwrap();
        match &export.node {
            Declaration::Export(ExportKind::Action(_effect), 10, has_state) => {
                assert!(
                    *has_state,
                    "caller must have has_state (in pushers) (catches exp_has_push && !pushers mutant)"
                );
            }
            _ => panic!("expected Action export for 10"),
        }
    }

    #[test]
    fn effectize_valrec_iteration_converges() {
        // Catches mutant: iterations >= MAX -> < would never break; !changed || iterations >= MAX.
        // ValRec that converges in 2-3 iterations; must complete without panic.
        let s = Settings::new();
        let span = Span::dummy();
        let file: File = vec![
            Located::new(
                Declaration::ValRec(vec![(
                    "x".into(),
                    1,
                    Located::dummy(Constructor::Unit),
                    Located::dummy(Expression::Prim(Prim::Int(0))),
                    "x".into(),
                )]),
                span.clone(),
            ),
            Located::new(
                Declaration::Export(ExportKind::Action(Effect::ReadOnly), 1, false),
                span,
            ),
        ];
        let (out, errs) = effectize(file, &s);
        assert!(errs.is_empty());
        assert_eq!(out.len(), 2, "valrec + export");
        match &out[0].node {
            Declaration::ValRec(vis) => assert_eq!(vis.len(), 1),
            _ => panic!("expected ValRec"),
        }
    }

    // --- Plan: Catch Missed Mutants - effect_analysis ---

    #[test]
    fn effectize_valrec_writer_propagates_second_iteration() {
        // Kills: iterations += 1, !changed || iterations >= MAX, &&, !writers.contains_key.
        // ValRec [B, A] with B=Named(A), A=dml. Iter 1: add A. Iter 2: add B. Export B -> ReadWrite.
        let s = Settings::new();
        let span = Span::dummy();
        let unit_ty = Located::dummy(Constructor::Unit);
        let file: File = vec![
            Located::new(
                Declaration::ValRec(vec![
                    (
                        "b".into(),
                        2,
                        unit_ty.clone(),
                        Located::dummy(Expression::Named(1)),
                        "b".into(),
                    ),
                    (
                        "a".into(),
                        1,
                        unit_ty,
                        Located::dummy(Expression::FfiApp("Basis".into(), "dml".into(), vec![])),
                        "a".into(),
                    ),
                ]),
                span.clone(),
            ),
            Located::new(
                Declaration::Export(ExportKind::Action(Effect::ReadOnly), 2, false),
                span,
            ),
        ];
        let (out, errs) = effectize(file, &s);
        assert!(errs.is_empty());
        let export = out
            .iter()
            .find(|d| matches!(&d.node, Declaration::Export(_, n, _) if *n == 2))
            .unwrap();
        match &export.node {
            Declaration::Export(ExportKind::Action(effect), 2, _) => {
                assert_eq!(
                    *effect,
                    Effect::ReadWrite,
                    "b calls a (writer); must propagate to writers in 2nd iteration"
                );
            }
            _ => panic!("expected Action export for 2"),
        }
    }

    #[test]
    fn effectize_valrec_writer_and_reader_both_propagated() {
        // Kills: &&/|| in conditions. A writes, B reads, C calls both -> C gets ReadCookieWrite.
        let s = Settings::new();
        let span = Span::dummy();
        let unit_ty = Located::dummy(Constructor::Unit);
        let body_c = Expression::Let(
            "x".into(),
            unit_ty.clone(),
            Box::new(Located::dummy(Expression::Named(1))), // write
            Box::new(Located::dummy(Expression::Named(2))), // read
        );
        let file: File = vec![
            Located::new(
                Declaration::ValRec(vec![
                    (
                        "a".into(),
                        1,
                        unit_ty.clone(),
                        Located::dummy(Expression::FfiApp("Basis".into(), "dml".into(), vec![])),
                        "a".into(),
                    ),
                    (
                        "b".into(),
                        2,
                        unit_ty.clone(),
                        Located::dummy(Expression::Ffi("Basis".into(), "getCookie".into())),
                        "b".into(),
                    ),
                    ("c".into(), 3, unit_ty, Located::dummy(body_c), "c".into()),
                ]),
                span.clone(),
            ),
            Located::new(
                Declaration::Export(ExportKind::Action(Effect::ReadOnly), 3, false),
                span,
            ),
        ];
        let (out, errs) = effectize(file, &s);
        assert!(errs.is_empty());
        let export = out
            .iter()
            .find(|d| matches!(&d.node, Declaration::Export(_, n, _) if *n == 3))
            .unwrap();
        match &export.node {
            Declaration::Export(ExportKind::Action(effect), 3, _) => {
                assert_eq!(
                    *effect,
                    Effect::ReadCookieWrite,
                    "c calls both writer and reader -> ReadCookieWrite"
                );
            }
            _ => panic!("expected Action export for 3"),
        }
    }

    #[test]
    fn effectize_valrec_iterations_eventually_stop() {
        // Kills: iterations >= MAX break condition. ValRec with no side effects converges immediately.
        let s = Settings::new();
        let span = Span::dummy();
        let file: File = vec![
            Located::new(
                Declaration::ValRec(vec![
                    (
                        "a".into(),
                        1,
                        Located::dummy(Constructor::Unit),
                        Located::dummy(Expression::Prim(Prim::Int(0))),
                        "a".into(),
                    ),
                    (
                        "b".into(),
                        2,
                        Located::dummy(Constructor::Unit),
                        Located::dummy(Expression::Prim(Prim::Int(1))),
                        "b".into(),
                    ),
                ]),
                span.clone(),
            ),
            Located::new(
                Declaration::Export(ExportKind::Action(Effect::ReadOnly), 1, false),
                span,
            ),
        ];
        let (out, errs) = effectize(file, &s);
        assert!(errs.is_empty());
        assert_eq!(out.len(), 2);
    }

    #[test]
    fn effectize_link_export_with_writer_emits_error_when_not_safe_get() {
        // Catches mutant: delete ! in if !settings.is_safe_get(&s).
        let s = Settings::new();
        let span = Span::dummy();
        let file: File = vec![
            Located::new(
                Declaration::Val(
                    "main".into(),
                    100,
                    Located::dummy(Constructor::Unit),
                    Located::dummy(Expression::FfiApp("Basis".into(), "dml".into(), vec![])),
                    "/page".into(),
                ),
                span.clone(),
            ),
            Located::new(
                Declaration::Export(ExportKind::Link(Effect::ReadOnly), 100, false),
                span,
            ),
        ];
        let (_, errs) = effectize(file, &s);
        assert!(
            !errs.is_empty(),
            "Link export with writer and default safe_get=false must emit error"
        );
    }
}
