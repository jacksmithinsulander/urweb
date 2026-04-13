//! RPC identification and `EServerCall` injection pass.
//!
//! Scans the Core file to find all places where the canonical RPC FFI bindings
//! ([`crate::intrinsics::web_ffi`]) are applied to a named transaction function, then replaces those
//! applications with `EServerCall` nodes and emits corresponding
//! `DExport(Rpc(ReadWrite), n, false)` declarations.
//!
//! Mirrors `rpcify.sml`.

use std::collections::{HashMap, HashSet};

use crate::core::*;
use crate::diagnostics::{DiagnosticId, DiagnosticPayload};
use crate::error_types::{Located, Span};
use crate::export::{Effect, ExportKind};
use crate::intrinsics::web_ffi::{is_basis_rpc_ffi, is_basis_try_rpc_ffi};
use crate::settings::FailureMode;

// ---------------------------------------------------------------------------
// Transaction function info
// ---------------------------------------------------------------------------

/// Info about a named function that returns a transaction (`ran` in `transaction ran`).
struct TFunc {
    ran: LocatedConstructor,
}

// ---------------------------------------------------------------------------
// State threaded through the pass
// ---------------------------------------------------------------------------

struct State {
    exported: HashSet<usize>,
    export_decls: Vec<LocatedDeclaration>,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Peels off nested `EApp` applications, collecting arguments.
///
/// Returns `Some((function_id, args))` if the head is `ENamed n`.
fn get_app(
    expression: &Expression,
    mut args: Vec<LocatedExpression>,
) -> Option<(usize, Vec<LocatedExpression>)> {
    match expression {
        Expression::Named(name_id) => Some((*name_id, args)),
        Expression::App(function, argument) => {
            args.insert(0, *argument.clone());
            get_app(&function.node, args)
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Main transform
// ---------------------------------------------------------------------------

pub fn rpcify(file: File, error_reporter: &mut impl FnMut(&Span, DiagnosticPayload)) -> File {
    // Pass 1: find base IDs for Basis.rpc and Basis.tryRpc (may be aliased)
    let mut rpc_base_ids: HashSet<usize> = HashSet::new();
    let mut trpc_base_ids: HashSet<usize> = HashSet::new();

    for d in &file {
        if let Declaration::Val(_, n, _, e, _) = &d.node {
            match &e.node {
                Expression::Ffi(m, f) if is_basis_rpc_ffi(m, f) => {
                    rpc_base_ids.insert(*n);
                }
                Expression::Ffi(m, f) if is_basis_try_rpc_ffi(m, f) => {
                    trpc_base_ids.insert(*n);
                }
                Expression::Named(n2) => {
                    if rpc_base_ids.contains(n2) {
                        rpc_base_ids.insert(*n);
                    } else if trpc_base_ids.contains(n2) {
                        trpc_base_ids.insert(*n);
                    }
                }
                _ => {}
            }
        }
    }

    // Pass 2: collect transaction functions
    // A "transaction function" is a named Val/ValRec whose type is
    // `fun args... -> transaction ran` (CApp(named_transaction, ran)).
    let mut tfuncs: HashMap<usize, TFunc> = HashMap::new();

    for d in &file {
        let mut vis_refs: Vec<(
            &String,
            &usize,
            &LocatedConstructor,
            &LocatedExpression,
            &String,
        )> = vec![];
        match &d.node {
            Declaration::Val(x, n, t, e, s) => {
                vis_refs.push((x, n, t, e, s));
            }
            Declaration::ValRec(vis) => {
                for (x, n, t, e, s) in vis {
                    vis_refs.push((x, n, t, e, s));
                }
            }
            _ => {}
        }

        for (_x, n, t, e, _s) in vis_refs {
            // Crawl through TCFun/TFun/EAbs/ECAbs to find the transaction return type
            fn crawl(
                t: &LocatedConstructor,
                e: &LocatedExpression,
                args: &mut Vec<(String, LocatedConstructor)>,
                span: &Span,
            ) -> Option<LocatedConstructor> {
                match (&t.node, &e.node) {
                    // CApp(_, ran) is "transaction ran" — we've found the transaction result
                    (Constructor::App(_, ran), _) => Some(*ran.clone()),
                    // TFun(arg, rest) with EAbs(x, _, _, body)
                    (Constructor::TFun(arg, rest), Expression::Abs(arg_name, _, _, body)) => {
                        args.push((arg_name.clone(), *arg.clone()));
                        crawl(rest, body, args, span)
                    }
                    // TFun(arg, rest) without EAbs — eta-expand
                    (Constructor::TFun(arg, rest), _) => {
                        let n = args.len();
                        let eta_arg_name = "x".to_string();
                        let eta_app = Located {
                            node: Expression::App(
                                Box::new(e.clone()),
                                Box::new(Located {
                                    node: Expression::Rel(n),
                                    span: span.clone(),
                                }),
                            ),
                            span: span.clone(),
                        };
                        args.push((eta_arg_name, *arg.clone()));
                        crawl(rest, &eta_app, args, span)
                    }
                    _ => None,
                }
            }

            let mut args = Vec::new();
            if let Some(ran) = crawl(t, e, &mut args, &e.span) {
                tfuncs.insert(*n, TFunc { ran });
            }
        }
    }

    // Pass 3: rewrite rpc/tryRpc calls to EServerCall
    let mut state = State {
        exported: HashSet::new(),
        export_decls: Vec::new(),
    };

    let mut result: Vec<LocatedDeclaration> = Vec::new();

    for d in file {
        let span = d.span.clone();

        // Rewrite expressions inside the declaration
        let d = rewrite_decl(
            d,
            &rpc_base_ids,
            &trpc_base_ids,
            &tfuncs,
            &mut state,
            error_reporter,
        );

        // Prepend any newly generated export declarations
        result.append(&mut state.export_decls);
        result.push(Located { node: d.node, span });
    }

    result
}

fn rewrite_decl(
    d: LocatedDeclaration,
    rpc_base_ids: &HashSet<usize>,
    trpc_base_ids: &HashSet<usize>,
    tfuncs: &HashMap<usize, TFunc>,
    state: &mut State,
    error_reporter: &mut impl FnMut(&Span, DiagnosticPayload),
) -> LocatedDeclaration {
    let span = d.span.clone();
    let node = match d.node {
        Declaration::Val(x, n, t, e, s) => {
            let e2 = rewrite_exp(
                e,
                rpc_base_ids,
                trpc_base_ids,
                tfuncs,
                state,
                error_reporter,
            );
            Declaration::Val(x, n, t, e2, s)
        }
        Declaration::ValRec(vis) => {
            let vis2 = vis
                .into_iter()
                .map(|(x, n, t, e, s)| {
                    let e2 = rewrite_exp(
                        e,
                        rpc_base_ids,
                        trpc_base_ids,
                        tfuncs,
                        state,
                        error_reporter,
                    );
                    (x, n, t, e2, s)
                })
                .collect();
            Declaration::ValRec(vis2)
        }
        Declaration::Task(e1, e2) => {
            let e1b = rewrite_exp(
                e1,
                rpc_base_ids,
                trpc_base_ids,
                tfuncs,
                state,
                error_reporter,
            );
            let e2b = rewrite_exp(
                e2,
                rpc_base_ids,
                trpc_base_ids,
                tfuncs,
                state,
                error_reporter,
            );
            Declaration::Task(e1b, e2b)
        }
        Declaration::Policy(e) => {
            let e2 = rewrite_exp(
                e,
                rpc_base_ids,
                trpc_base_ids,
                tfuncs,
                state,
                error_reporter,
            );
            Declaration::Policy(e2)
        }
        other => other,
    };
    Located { node, span }
}

fn rewrite_exp(
    e: LocatedExpression,
    rpc_base_ids: &HashSet<usize>,
    trpc_base_ids: &HashSet<usize>,
    tfuncs: &HashMap<usize, TFunc>,
    state: &mut State,
    error_reporter: &mut impl FnMut(&Span, DiagnosticPayload),
) -> LocatedExpression {
    let span = e.span.clone();

    // First apply reduce_local to the expression (mirrors SML's ReduceLocal.reduceExp call)
    let e = crate::core::local_reduction::reduce_exp(e);

    // Check for rpc/tryRpc application patterns
    let (is_rpc, fm, trans) = match &e.node {
        // EApp((ECApp((EFfi("Basis", "rpc"), _), ran), _), trans)
        Expression::App(f, trans) => match &f.node {
            Expression::CApp(inner_f, _ran) => match &inner_f.node {
                Expression::Ffi(m, name) if m == "Basis" && name == "rpc" => {
                    (true, FailureMode::None, Some(*trans.clone()))
                }
                Expression::Ffi(m, name) if m == "Basis" && name == "tryRpc" => {
                    (true, FailureMode::Error, Some(*trans.clone()))
                }
                Expression::Named(n) if rpc_base_ids.contains(n) => {
                    (true, FailureMode::None, Some(*trans.clone()))
                }
                Expression::Named(n) if trpc_base_ids.contains(n) => {
                    (true, FailureMode::Error, Some(*trans.clone()))
                }
                _ => (false, FailureMode::None, None),
            },
            _ => (false, FailureMode::None, None),
        },
        _ => (false, FailureMode::None, None),
    };

    if is_rpc {
        return match trans {
            Some(trans) => new_rpc(trans, fm, tfuncs, state, error_reporter, &span),
            None => {
                error_reporter(
                    &span,
                    DiagnosticPayload::new(DiagnosticId::RpcInternalMissingTranslation, vec![]),
                );
                e
            }
        };
    }

    // Recurse into sub-expressions
    let node = match e.node {
        Expression::App(f, x) => Expression::App(
            Box::new(rewrite_exp(
                *f,
                rpc_base_ids,
                trpc_base_ids,
                tfuncs,
                state,
                error_reporter,
            )),
            Box::new(rewrite_exp(
                *x,
                rpc_base_ids,
                trpc_base_ids,
                tfuncs,
                state,
                error_reporter,
            )),
        ),
        Expression::Abs(x, dom, ran, body) => Expression::Abs(
            x,
            dom,
            ran,
            Box::new(rewrite_exp(
                *body,
                rpc_base_ids,
                trpc_base_ids,
                tfuncs,
                state,
                error_reporter,
            )),
        ),
        Expression::CApp(ef, c) => Expression::CApp(
            Box::new(rewrite_exp(
                *ef,
                rpc_base_ids,
                trpc_base_ids,
                tfuncs,
                state,
                error_reporter,
            )),
            c,
        ),
        Expression::CAbs(x, k, body) => Expression::CAbs(
            x,
            k,
            Box::new(rewrite_exp(
                *body,
                rpc_base_ids,
                trpc_base_ids,
                tfuncs,
                state,
                error_reporter,
            )),
        ),
        Expression::KAbs(x, body) => Expression::KAbs(
            x,
            Box::new(rewrite_exp(
                *body,
                rpc_base_ids,
                trpc_base_ids,
                tfuncs,
                state,
                error_reporter,
            )),
        ),
        Expression::KApp(ef, k) => Expression::KApp(
            Box::new(rewrite_exp(
                *ef,
                rpc_base_ids,
                trpc_base_ids,
                tfuncs,
                state,
                error_reporter,
            )),
            k,
        ),
        Expression::Let(x, t, e1, e2) => Expression::Let(
            x,
            t,
            Box::new(rewrite_exp(
                *e1,
                rpc_base_ids,
                trpc_base_ids,
                tfuncs,
                state,
                error_reporter,
            )),
            Box::new(rewrite_exp(
                *e2,
                rpc_base_ids,
                trpc_base_ids,
                tfuncs,
                state,
                error_reporter,
            )),
        ),
        Expression::Case(disc, arms, meta) => Expression::Case(
            Box::new(rewrite_exp(
                *disc,
                rpc_base_ids,
                trpc_base_ids,
                tfuncs,
                state,
                error_reporter,
            )),
            arms.into_iter()
                .map(|(p, body)| {
                    (
                        p,
                        rewrite_exp(
                            body,
                            rpc_base_ids,
                            trpc_base_ids,
                            tfuncs,
                            state,
                            error_reporter,
                        ),
                    )
                })
                .collect(),
            meta,
        ),
        Expression::Write(inner) => Expression::Write(Box::new(rewrite_exp(
            *inner,
            rpc_base_ids,
            trpc_base_ids,
            tfuncs,
            state,
            error_reporter,
        ))),
        Expression::Record(fields) => Expression::Record(
            fields
                .into_iter()
                .map(|(n, v, t)| {
                    (
                        n,
                        rewrite_exp(
                            v,
                            rpc_base_ids,
                            trpc_base_ids,
                            tfuncs,
                            state,
                            error_reporter,
                        ),
                        t,
                    )
                })
                .collect(),
        ),
        Expression::Concat(e1, c1, e2, c2) => Expression::Concat(
            Box::new(rewrite_exp(
                *e1,
                rpc_base_ids,
                trpc_base_ids,
                tfuncs,
                state,
                error_reporter,
            )),
            c1,
            Box::new(rewrite_exp(
                *e2,
                rpc_base_ids,
                trpc_base_ids,
                tfuncs,
                state,
                error_reporter,
            )),
            c2,
        ),
        Expression::Field(rec, c, meta) => Expression::Field(
            Box::new(rewrite_exp(
                *rec,
                rpc_base_ids,
                trpc_base_ids,
                tfuncs,
                state,
                error_reporter,
            )),
            c,
            meta,
        ),
        Expression::FfiApp(m, f, args) => Expression::FfiApp(
            m,
            f,
            args.into_iter()
                .map(|(ae, at)| {
                    (
                        rewrite_exp(
                            ae,
                            rpc_base_ids,
                            trpc_base_ids,
                            tfuncs,
                            state,
                            error_reporter,
                        ),
                        at,
                    )
                })
                .collect(),
        ),
        Expression::ServerCall(n, args, t, fm) => Expression::ServerCall(
            n,
            args.into_iter()
                .map(|ae| {
                    rewrite_exp(
                        ae,
                        rpc_base_ids,
                        trpc_base_ids,
                        tfuncs,
                        state,
                        error_reporter,
                    )
                })
                .collect(),
            t,
            fm,
        ),
        other => other,
    };

    Located { node, span }
}

/// Convert a transaction expression into an `EServerCall`.
fn new_rpc(
    trans: LocatedExpression,
    fm: FailureMode,
    tfuncs: &HashMap<usize, TFunc>,
    state: &mut State,
    error_reporter: &mut impl FnMut(&Span, DiagnosticPayload),
    span: &Span,
) -> LocatedExpression {
    match get_app(&trans.node, Vec::new()) {
        None => {
            error_reporter(
                span,
                DiagnosticPayload::new(DiagnosticId::RpcCodeNotNamedFunction, vec![]),
            );
            trans
        }
        Some((n, args)) => match tfuncs.get(&n) {
            None => {
                // This can happen if rpcify is called before tfuncs is populated
                // In practice this is a compiler bug
                error_reporter(
                    span,
                    DiagnosticPayload::new(DiagnosticId::RpcUndetectedTransactionFunction, vec![]),
                );
                trans
            }
            Some(tf) => {
                // Export this function as an RPC if not already done
                if !state.exported.contains(&n) {
                    state.exported.insert(n);
                    state.export_decls.push(Located {
                        node: Declaration::Export(ExportKind::Rpc(Effect::ReadWrite), n, false),
                        span: span.clone(),
                    });
                }

                Located {
                    node: Expression::ServerCall(n, args, tf.ran.clone(), fm),
                    span: span.clone(),
                }
            }
        },
    }
}
