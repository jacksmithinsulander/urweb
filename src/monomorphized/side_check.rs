//! Side-check pass: verify server-side code doesn't use client-only FFI.
//!
//! Also collects environment variable names accessed via `Basis.getenv`.
//!
//! Mirrors `SideCheck.check` in `sidecheck.sml`.

use std::collections::HashSet;

use crate::diagnostics::{DiagnosticId, DiagnosticPayload};
use crate::error_types::{CompileError, ErrorReporter};
use crate::monomorphized::{Decl, Exp, File, LocExp, Sidedness};
use crate::primitives::Prim;
use crate::settings::Settings;

// ---------------------------------------------------------------------------
// checkExp — walk an expression, stopping at EJavaScript boundaries
// ---------------------------------------------------------------------------

fn check_exp(
    e: &LocExp,
    settings: &Settings,
    errors: &mut ErrorReporter,
    env_vars: &mut HashSet<String>,
    warned_dynamic: &mut bool,
) {
    match &e.node {
        // Client-side code boundary: do not recurse inside
        Exp::JavaScript(_, _) => {}

        Exp::Ffi(m, x) => {
            let ffi = (m.clone(), x.clone());
            if settings.is_client_only(&ffi) {
                let display = if m == "Basis" {
                    match x.as_str() {
                        "get_client_source" => "get".to_string(),
                        other => other.to_string(),
                    }
                } else {
                    x.clone()
                };
                errors.report_at_with_hint(
                    e.span.clone(),
                    DiagnosticPayload::new(
                        DiagnosticId::SideServerCallsClientOnlyFfi,
                        vec![m.clone(), display],
                    ),
                    DiagnosticId::HintSideServerCallsClientOnlyFfi,
                    vec![],
                );
            }
        }

        Exp::FfiApp(m, x, args) => {
            // Special case: Basis.getenv collects env var names
            if m == "Basis" && x == "getenv" {
                if let [(arg, _)] = args.as_slice() {
                    if let Exp::Prim(Prim::String(_, s)) = &arg.node {
                        env_vars.insert(s.clone());
                    } else if !*warned_dynamic {
                        *warned_dynamic = true;
                        errors.report(CompileError::warning_at_with_hint(
                            e.span.clone(),
                            DiagnosticPayload::new(
                                DiagnosticId::SideGetenvNotCompileTimeString,
                                vec![e.span.to_string()],
                            ),
                            DiagnosticId::HintSideGetenvNotCompileTimeString,
                            vec![],
                        ));
                    }
                }
            } else {
                let ffi = (m.clone(), x.clone());
                if settings.is_client_only(&ffi) {
                    let display = if m == "Basis" {
                        match x.as_str() {
                            "get_client_source" => "get".to_string(),
                            other => other.to_string(),
                        }
                    } else {
                        x.clone()
                    };
                    errors.report_at_with_hint(
                        e.span.clone(),
                        DiagnosticPayload::new(
                            DiagnosticId::SideServerCallsClientOnlyFfi,
                            vec![m.clone(), display],
                        ),
                        DiagnosticId::HintSideServerCallsClientOnlyFfi,
                        vec![],
                    );
                }
            }
            for (a, _) in args {
                check_exp(a, settings, errors, env_vars, warned_dynamic);
            }
        }

        // Leaves that need no checking
        Exp::Prim(_) | Exp::Rel(_) | Exp::Named(_) | Exp::None(_) | Exp::Con(_, _, None) => {}

        // Recursive cases
        Exp::App(f, arg) => {
            check_exp(f, settings, errors, env_vars, warned_dynamic);
            check_exp(arg, settings, errors, env_vars, warned_dynamic);
        }
        Exp::Abs(_, _, _, body) => check_exp(body, settings, errors, env_vars, warned_dynamic),
        Exp::Con(_, _, Some(inner)) | Exp::Some(_, inner) => {
            check_exp(inner, settings, errors, env_vars, warned_dynamic);
        }
        Exp::Unop(_, inner)
        | Exp::Write(inner)
        | Exp::Field(inner, _)
        | Exp::SignalReturn(inner)
        | Exp::SignalSource(inner)
        | Exp::Sleep(inner)
        | Exp::Spawn(inner)
        | Exp::Nextval(inner) => {
            check_exp(inner, settings, errors, env_vars, warned_dynamic);
        }
        Exp::Binop(_, _, e1, e2)
        | Exp::Seq(e1, e2)
        | Exp::Strcat(e1, e2)
        | Exp::Let(_, _, e1, e2)
        | Exp::SignalBind(e1, e2)
        | Exp::Setval(e1, e2) => {
            check_exp(e1, settings, errors, env_vars, warned_dynamic);
            check_exp(e2, settings, errors, env_vars, warned_dynamic);
        }
        Exp::Record(xets) => {
            for (_, a, _) in xets {
                check_exp(a, settings, errors, env_vars, warned_dynamic);
            }
        }
        Exp::Case(disc, arms, _) => {
            check_exp(disc, settings, errors, env_vars, warned_dynamic);
            for (_, ae) in arms {
                check_exp(ae, settings, errors, env_vars, warned_dynamic);
            }
        }
        Exp::Error(inner, _)
        | Exp::Redirect(inner, _)
        | Exp::Uurlify(inner, _, _)
        | Exp::Recv(inner, _)
        | Exp::ServerCall(inner, _, _, _)
        | Exp::Dml(inner, _) => {
            check_exp(inner, settings, errors, env_vars, warned_dynamic);
        }
        Exp::ReturnBlob {
            blob, mime_type, ..
        } => {
            if let Some(b) = blob {
                check_exp(b, settings, errors, env_vars, warned_dynamic);
            }
            check_exp(mime_type, settings, errors, env_vars, warned_dynamic);
        }
        Exp::Query(qm) => {
            check_exp(&qm.query, settings, errors, env_vars, warned_dynamic);
            check_exp(&qm.body, settings, errors, env_vars, warned_dynamic);
            check_exp(&qm.initial, settings, errors, env_vars, warned_dynamic);
        }
        Exp::Closure(_, envs) => {
            for a in envs {
                check_exp(a, settings, errors, env_vars, warned_dynamic);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Check server-side code for client-only FFI usage.
///
/// Returns the file unchanged, plus a list of env var names found via `Basis.getenv`.
///
/// Mirrors `SideCheck.check` and `SideCheck.readEnvVars`.
pub fn check(file: File, settings: &Settings, errors: &mut ErrorReporter) -> (File, Vec<String>) {
    let (decls, ps) = &file;

    // Build set of client-side declaration IDs (from ps sidedness)
    let client_ids: HashSet<usize> = ps
        .iter()
        .filter(|(_, side, _)| !matches!(side, Sidedness::ServerOnly))
        .map(|(n, _, _)| *n)
        .collect();

    let mut env_vars: HashSet<String> = HashSet::new();
    let mut warned_dynamic = false;

    for d in decls {
        match &d.node {
            Decl::Val(_, n, _, e, _) => {
                if !client_ids.contains(n) {
                    check_exp(e, settings, errors, &mut env_vars, &mut warned_dynamic);
                }
            }
            Decl::ValRec(vis) => {
                // Skip entire group if any member is client-side
                let any_client = vis.iter().any(|(_, n, _, _, _)| client_ids.contains(n));
                if !any_client {
                    for (_, _, _, e, _) in vis {
                        check_exp(e, settings, errors, &mut env_vars, &mut warned_dynamic);
                    }
                }
            }
            _ => {}
        }
    }

    let mut env_var_list: Vec<String> = env_vars.into_iter().collect();
    env_var_list.sort();

    (file, env_var_list)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_file_no_errors() {
        let settings = Settings::default();
        let mut errors = ErrorReporter::new();
        let (_, env_vars) = check((vec![], vec![]), &settings, &mut errors);
        assert!(!errors.has_errors());
        assert!(env_vars.is_empty());
    }
}
