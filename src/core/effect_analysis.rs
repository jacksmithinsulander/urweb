//! Effect annotation pass for the Core IR.
//!
//! Determines which exported pages/actions/RPCs can write (side-effects),
//! read cookies, or push data (write+read via RPC), and annotates the
//! `DExport` declarations accordingly.
//!
//! Mirrors `effectize.sml`.

#![allow(dead_code)]

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
            (module == "Basis" && function == "getHeader")
                || (module == "Basis" && function == "getenv")
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
            // Fixed-point: iterate until no new additions
            loop {
                let mut changed = false;
                for (_, n, _, e, s) in &vis {
                    let e_dejs = dejs_exp(e.clone());
                    if exp_has_write(&e_dejs, writers, settings) && !writers.contains_key(n) {
                        writers.insert(*n, (span.clone(), s.clone()));
                        changed = true;
                    }
                    if exp_has_read_cookie(&e_dejs, readers) && !readers.contains_key(n) {
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
                if !settings.is_safe_get(&s) {
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
