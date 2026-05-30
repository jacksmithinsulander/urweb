//! Side-check pass: verify server-side code doesn't use client-only FFI.
//!
//! Also collects environment variable names accessed via `Basis.getenv`.
//!
//! Mirrors `SideCheck.check` in `sidecheck.sml`.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::diagnostics::{DiagnosticId, DiagnosticPayload};
use crate::error_types::{ErrorReporter, Span};
use crate::monomorphized::{Decl, Exp, File, LocExp, Sidedness};
use crate::primitives::Prim;
use crate::settings::Settings;

/// Maximum recursive depth for [`check_exp`] (stack / pathological IR guard; Power-of-Ten style cap).
const MAX_CHECK_EXP_DEPTH: usize = 500_000;

/// Maps an FFI path component to the string inserted into `SideServerCallsClientOnlyFfi` templates.
///
/// # Returns
///
/// Display name for `symbol`, with legacy `Basis` special cases applied.
fn ffi_symbol_for_diagnostic(module: &str, symbol: &str) -> String {
    match module == "Basis" {
        true => match symbol {
            "get_client_source" => "get".to_string(),
            other => other.to_string(),
        },
        false => symbol.to_string(),
    }
}

/// Records a hard error when server-only code calls an FFI tagged client-only in settings.
///
/// Uses catalog id [`DiagnosticId::SideServerCallsClientOnlyFfi`] plus its hint id.
fn report_client_only_ffi_in_server(
    errors: &mut ErrorReporter,
    span: Span,
    module: &str,
    symbol: &str,
) {
    let display = ffi_symbol_for_diagnostic(module, symbol);
    errors.report_at_with_hint(
        span,
        DiagnosticPayload::new(
            DiagnosticId::SideServerCallsClientOnlyFfi,
            vec![module.to_string(), display],
        ),
        DiagnosticId::HintSideServerCallsClientOnlyFfi,
        vec![],
    );
}

/// Emits at most one [`DiagnosticId::SideGetenvNotCompileTimeString`] warning per side-check pass.
///
/// Used when `getenv` is not applied to a single string literal, including wrong arity,
/// so dependency extraction cannot record an environment variable name.
fn warn_getenv_name_not_compile_time_string(
    errors: &mut ErrorReporter,
    span: Span,
    warned_dynamic: &mut bool,
) {
    match *warned_dynamic {
        true => {}
        false => {
            *warned_dynamic = true;
            let span_text = span.to_string();
            errors.report_warning_at_with_hint(
                span,
                DiagnosticPayload::new(
                    DiagnosticId::SideGetenvNotCompileTimeString,
                    vec![span_text],
                ),
                DiagnosticId::HintSideGetenvNotCompileTimeString,
                vec![],
            );
        }
    }
}

fn debug_side_trace_enabled() -> bool {
    std::env::var("URWEB_DEBUG_SIDE_TRACE").ok().as_deref() == Some("1")
}

fn debug_side_trace_span(span: &Span) -> bool {
    span.file.ends_with("/demo/chat.ur") || span.file.ends_with("/demo/listEdit.ur")
}

// ---------------------------------------------------------------------------
// checkExp — walk an expression, stopping at EJavaScript boundaries
// ---------------------------------------------------------------------------

/// Recursively visits `e`, reporting client-only FFI misuse and collecting static `getenv` names.
///
/// `recursion_depth` increases on each recursive descent and is capped at [`MAX_CHECK_EXP_DEPTH`].
fn check_exp(
    e: &LocExp,
    recursion_depth: usize,
    settings: &Settings,
    errors: &mut ErrorReporter,
    env_vars: &mut HashSet<String>,
    warned_dynamic: &mut bool,
) {
    if recursion_depth > MAX_CHECK_EXP_DEPTH {
        panic!("side_check::check_exp exceeded recursion depth cap {MAX_CHECK_EXP_DEPTH}");
    }
    let next_depth = recursion_depth + 1;
    match &e.node {
        // Client-side code boundary: do not recurse inside
        Exp::JavaScript(_, _) => {}

        Exp::Ffi(m, x) => {
            let ffi = (m.clone(), x.clone());
            if settings.is_client_only(&ffi) {
                report_client_only_ffi_in_server(errors, e.span.clone(), m.as_str(), x.as_str());
            }
        }

        Exp::FfiApp(m, x, args) => {
            match m == "Basis" && x == "getenv" {
                true => match args.as_slice() {
                    [(arg, _)] => match &arg.node {
                        Exp::Prim(Prim::String(_, s)) => {
                            env_vars.insert(s.clone());
                        }
                        _ => warn_getenv_name_not_compile_time_string(
                            errors,
                            e.span.clone(),
                            warned_dynamic,
                        ),
                    },
                    _ => warn_getenv_name_not_compile_time_string(
                        errors,
                        e.span.clone(),
                        warned_dynamic,
                    ),
                },
                false => {
                    let ffi = (m.clone(), x.clone());
                    if settings.is_client_only(&ffi) {
                        report_client_only_ffi_in_server(
                            errors,
                            e.span.clone(),
                            m.as_str(),
                            x.as_str(),
                        );
                    }
                }
            }
            for (a, _) in args {
                check_exp(a, next_depth, settings, errors, env_vars, warned_dynamic);
            }
        }

        // Leaves that need no checking
        Exp::Prim(_) | Exp::Rel(_) | Exp::Named(_) | Exp::None(_) | Exp::Con(_, _, None) => {}

        // Recursive cases
        Exp::App(f, arg) => {
            check_exp(f, next_depth, settings, errors, env_vars, warned_dynamic);
            check_exp(arg, next_depth, settings, errors, env_vars, warned_dynamic);
        }
        Exp::Abs(_, _, _, body) => {
            check_exp(body, next_depth, settings, errors, env_vars, warned_dynamic)
        }
        Exp::Con(_, _, Some(inner)) | Exp::Some(_, inner) => {
            check_exp(
                inner,
                next_depth,
                settings,
                errors,
                env_vars,
                warned_dynamic,
            );
        }
        Exp::Unop(_, inner)
        | Exp::Write(inner)
        | Exp::Field(inner, _)
        | Exp::SignalReturn(inner)
        | Exp::SignalSource(inner)
        | Exp::Sleep(inner)
        | Exp::Spawn(inner)
        | Exp::Nextval(inner) => {
            check_exp(
                inner,
                next_depth,
                settings,
                errors,
                env_vars,
                warned_dynamic,
            );
        }
        Exp::Binop(_, _, e1, e2)
        | Exp::Seq(e1, e2)
        | Exp::Strcat(e1, e2)
        | Exp::Let(_, _, e1, e2)
        | Exp::SignalBind(e1, e2)
        | Exp::Setval(e1, e2) => {
            check_exp(e1, next_depth, settings, errors, env_vars, warned_dynamic);
            check_exp(e2, next_depth, settings, errors, env_vars, warned_dynamic);
        }
        Exp::Record(xets) => {
            for (_, a, _) in xets {
                check_exp(a, next_depth, settings, errors, env_vars, warned_dynamic);
            }
        }
        Exp::Case(disc, arms, _) => {
            check_exp(disc, next_depth, settings, errors, env_vars, warned_dynamic);
            for (_, ae) in arms {
                check_exp(ae, next_depth, settings, errors, env_vars, warned_dynamic);
            }
        }
        Exp::Error(inner, _)
        | Exp::Redirect(inner, _)
        | Exp::Uurlify(inner, _, _)
        | Exp::Recv(inner, _)
        | Exp::ServerCall(inner, _, _, _)
        | Exp::Dml(inner, _) => {
            check_exp(
                inner,
                next_depth,
                settings,
                errors,
                env_vars,
                warned_dynamic,
            );
        }
        Exp::ReturnBlob {
            blob, mime_type, ..
        } => {
            if let Some(b) = blob {
                check_exp(b, next_depth, settings, errors, env_vars, warned_dynamic);
            }
            check_exp(
                mime_type,
                next_depth,
                settings,
                errors,
                env_vars,
                warned_dynamic,
            );
        }
        Exp::Query(qm) => {
            check_exp(
                &qm.query,
                next_depth,
                settings,
                errors,
                env_vars,
                warned_dynamic,
            );
            check_exp(
                &qm.body,
                next_depth,
                settings,
                errors,
                env_vars,
                warned_dynamic,
            );
            check_exp(
                &qm.initial,
                next_depth,
                settings,
                errors,
                env_vars,
                warned_dynamic,
            );
        }
        Exp::Closure(_, envs) => {
            for a in envs {
                check_exp(a, next_depth, settings, errors, env_vars, warned_dynamic);
            }
        }
    }
}

fn collect_named_ids_any(e: &LocExp, named_ids: &mut HashSet<usize>) {
    match &e.node {
        Exp::Named(n) => {
            named_ids.insert(*n);
        }
        Exp::App(f, arg)
        | Exp::Seq(f, arg)
        | Exp::Strcat(f, arg)
        | Exp::Binop(_, _, f, arg)
        | Exp::SignalBind(f, arg)
        | Exp::Setval(f, arg) => {
            collect_named_ids_any(f, named_ids);
            collect_named_ids_any(arg, named_ids);
        }
        Exp::Abs(_, _, _, body)
        | Exp::Write(body)
        | Exp::Unop(_, body)
        | Exp::Field(body, _)
        | Exp::SignalReturn(body)
        | Exp::SignalSource(body)
        | Exp::Sleep(body)
        | Exp::Spawn(body)
        | Exp::Nextval(body)
        | Exp::Dml(body, _)
        | Exp::Error(body, _)
        | Exp::Redirect(body, _)
        | Exp::Uurlify(body, _, _)
        | Exp::Recv(body, _)
        | Exp::ServerCall(body, _, _, _)
        | Exp::JavaScript(_, body) => collect_named_ids_any(body, named_ids),
        Exp::Con(_, _, Some(inner)) | Exp::Some(_, inner) => {
            collect_named_ids_any(inner, named_ids)
        }
        Exp::Let(_, _, bound, body) => {
            collect_named_ids_any(bound, named_ids);
            collect_named_ids_any(body, named_ids);
        }
        Exp::FfiApp(_, _, args) => {
            for (arg, _) in args {
                collect_named_ids_any(arg, named_ids);
            }
        }
        Exp::Record(fields) => {
            for (_, arg, _) in fields {
                collect_named_ids_any(arg, named_ids);
            }
        }
        Exp::Case(disc, arms, _) => {
            collect_named_ids_any(disc, named_ids);
            for (_, arm) in arms {
                collect_named_ids_any(arm, named_ids);
            }
        }
        Exp::ReturnBlob {
            blob, mime_type, ..
        } => {
            if let Some(blob) = blob {
                collect_named_ids_any(blob, named_ids);
            }
            collect_named_ids_any(mime_type, named_ids);
        }
        Exp::Query(qm) => {
            collect_named_ids_any(&qm.query, named_ids);
            collect_named_ids_any(&qm.body, named_ids);
            collect_named_ids_any(&qm.initial, named_ids);
        }
        Exp::Closure(n, envs) => {
            named_ids.insert(*n);
            for env in envs {
                collect_named_ids_any(env, named_ids);
            }
        }
        Exp::Prim(_) | Exp::Rel(_) | Exp::Ffi(_, _) | Exp::None(_) | Exp::Con(_, _, None) => {}
    }
}

fn collect_named_ids_in_javascript(e: &LocExp, named_ids: &mut HashSet<usize>) {
    match &e.node {
        Exp::JavaScript(_, body) => collect_named_ids_any(body, named_ids),
        Exp::App(f, arg)
        | Exp::Seq(f, arg)
        | Exp::Strcat(f, arg)
        | Exp::Binop(_, _, f, arg)
        | Exp::SignalBind(f, arg)
        | Exp::Setval(f, arg) => {
            collect_named_ids_in_javascript(f, named_ids);
            collect_named_ids_in_javascript(arg, named_ids);
        }
        Exp::Abs(_, _, _, body)
        | Exp::Write(body)
        | Exp::Unop(_, body)
        | Exp::Field(body, _)
        | Exp::SignalReturn(body)
        | Exp::SignalSource(body)
        | Exp::Sleep(body)
        | Exp::Spawn(body)
        | Exp::Nextval(body)
        | Exp::Dml(body, _)
        | Exp::Error(body, _)
        | Exp::Redirect(body, _)
        | Exp::Uurlify(body, _, _)
        | Exp::Recv(body, _)
        | Exp::ServerCall(body, _, _, _)
        | Exp::Con(_, _, Some(body))
        | Exp::Some(_, body) => collect_named_ids_in_javascript(body, named_ids),
        Exp::Let(_, _, bound, body) => {
            collect_named_ids_in_javascript(bound, named_ids);
            collect_named_ids_in_javascript(body, named_ids);
        }
        Exp::FfiApp(_, _, args) => {
            for (arg, _) in args {
                collect_named_ids_in_javascript(arg, named_ids);
            }
        }
        Exp::Record(fields) => {
            for (_, arg, _) in fields {
                collect_named_ids_in_javascript(arg, named_ids);
            }
        }
        Exp::Case(disc, arms, _) => {
            collect_named_ids_in_javascript(disc, named_ids);
            for (_, arm) in arms {
                collect_named_ids_in_javascript(arm, named_ids);
            }
        }
        Exp::ReturnBlob {
            blob, mime_type, ..
        } => {
            if let Some(blob) = blob {
                collect_named_ids_in_javascript(blob, named_ids);
            }
            collect_named_ids_in_javascript(mime_type, named_ids);
        }
        Exp::Query(qm) => {
            collect_named_ids_in_javascript(&qm.query, named_ids);
            collect_named_ids_in_javascript(&qm.body, named_ids);
            collect_named_ids_in_javascript(&qm.initial, named_ids);
        }
        Exp::Closure(n, envs) => {
            named_ids.insert(*n);
            for env in envs {
                collect_named_ids_in_javascript(env, named_ids);
            }
        }
        Exp::Prim(_)
        | Exp::Rel(_)
        | Exp::Named(_)
        | Exp::Ffi(_, _)
        | Exp::None(_)
        | Exp::Con(_, _, None) => {}
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
    if debug_side_trace_enabled() {
        eprintln!("URWEB_DEBUG_SIDE client_ids={client_ids:?}");
    }

    let mut env_vars: HashSet<String> = HashSet::new();
    let mut warned_dynamic = false;
    let mut decl_bodies: HashMap<usize, &LocExp> = HashMap::new();

    for d in decls {
        match &d.node {
            Decl::Val(_, n, _, e, _) => {
                decl_bodies.insert(*n, e);
            }
            Decl::ValRec(vis) => {
                for (_, n, _, e, _) in vis {
                    decl_bodies.insert(*n, e);
                }
            }
            _ => {}
        }
    }

    let mut client_helper_ids: HashSet<usize> = HashSet::new();
    let mut worklist: VecDeque<usize> = VecDeque::new();
    for d in decls {
        match &d.node {
            Decl::Val(_, n, _, e, _) if client_ids.contains(n) => {
                let mut refs = HashSet::new();
                collect_named_ids_in_javascript(e, &mut refs);
                for id in refs {
                    if client_helper_ids.insert(id) {
                        worklist.push_back(id);
                    }
                }
            }
            Decl::ValRec(vis) => {
                for (_, n, _, e, _) in vis {
                    if client_ids.contains(n) {
                        let mut refs = HashSet::new();
                        collect_named_ids_in_javascript(e, &mut refs);
                        for id in refs {
                            if client_helper_ids.insert(id) {
                                worklist.push_back(id);
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }

    while let Some(id) = worklist.pop_front() {
        if let Some(body) = decl_bodies.get(&id) {
            let mut refs = HashSet::new();
            collect_named_ids_any(body, &mut refs);
            for next in refs {
                if client_helper_ids.insert(next) {
                    worklist.push_back(next);
                }
            }
        }
    }

    for d in decls {
        match &d.node {
            Decl::Val(_, n, _, e, _) => {
                if debug_side_trace_enabled() && debug_side_trace_span(&d.span) {
                    eprintln!(
                        "URWEB_DEBUG_SIDE decl=Val id={} span={}:{} client={} helper={} body={:?}",
                        n,
                        d.span.file,
                        d.span.first.line,
                        client_ids.contains(n),
                        false,
                        e.node
                    );
                }
                if !client_ids.contains(n) && !client_helper_ids.contains(n) {
                    check_exp(e, 0, settings, errors, &mut env_vars, &mut warned_dynamic);
                }
            }
            Decl::ValRec(vis) => {
                // Skip entire group if any member is client-side
                let any_client = vis
                    .iter()
                    .any(|(_, n, _, _, _)| client_ids.contains(n) || client_helper_ids.contains(n));
                if debug_side_trace_enabled() {
                    for (name, n, _, e, _) in vis {
                        if debug_side_trace_span(&e.span) {
                            eprintln!(
                                "URWEB_DEBUG_SIDE decl=ValRecMember name={} id={} span={}:{} client={} helper={} any_client={} body={:?}",
                                name,
                                n,
                                e.span.file,
                                e.span.first.line,
                                client_ids.contains(n),
                                client_helper_ids.contains(n),
                                any_client,
                                e.node
                            );
                        }
                    }
                }
                match any_client {
                    true => {}
                    false => {
                        for (_, _, _, e, _) in vis {
                            check_exp(e, 0, settings, errors, &mut env_vars, &mut warned_dynamic);
                        }
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
    use crate::error_types::{CompileError, Located};
    use crate::monomorphized::{JavaScriptMode, Typ};
    use crate::primitives::StringMode;

    #[test]
    fn empty_file_no_errors() {
        let settings = Settings::default();
        let mut errors = ErrorReporter::new();
        let (_, env_vars) = check((vec![], vec![]), &settings, &mut errors);
        assert!(!errors.has_errors());
        assert!(env_vars.is_empty());
    }

    #[test]
    fn getenv_wrong_arity_warns_once_per_pass() {
        let settings = Settings::default();
        let mut errors = ErrorReporter::new_silent();
        let span = Span::dummy();
        let getenv_no_args = Located::new(
            Exp::FfiApp("Basis".into(), "getenv".into(), vec![]),
            span.clone(),
        );
        let string_type = Located::dummy(Typ::Ffi("Basis".into(), "string".into()));
        let d1 = Located::new(
            Decl::Val(
                "a".into(),
                1,
                string_type.clone(),
                getenv_no_args,
                String::new(),
            ),
            span.clone(),
        );
        let getenv_two_args = Located::new(
            Exp::FfiApp(
                "Basis".into(),
                "getenv".into(),
                vec![
                    (
                        Located::dummy(Exp::Prim(Prim::String(StringMode::Normal, "X".into()))),
                        string_type.clone(),
                    ),
                    (
                        Located::dummy(Exp::Prim(Prim::String(StringMode::Normal, "Y".into()))),
                        string_type.clone(),
                    ),
                ],
            ),
            span.clone(),
        );
        let d2 = Located::new(
            Decl::Val("b".into(), 2, string_type, getenv_two_args, String::new()),
            span,
        );
        let (_, env_vars) = check((vec![d1, d2], vec![]), &settings, &mut errors);
        assert!(
            matches!(errors.errors.as_slice(), [CompileError::WarningAt { .. }]),
            "expected exactly one getenv static-name warning, got {:?}",
            errors.errors
        );
        assert!(env_vars.is_empty());
    }

    #[test]
    fn client_only_ffi_reachable_only_from_javascript_helper_is_allowed() {
        let settings = Settings::default();
        let mut errors = ErrorReporter::new_silent();
        let span = Span::dummy();
        let unit_type = Located::dummy(Typ::Record(vec![]));
        let string_type = Located::dummy(Typ::Ffi("Basis".into(), "string".into()));

        let helper_body = Located::new(
            Exp::FfiApp(
                "Basis".into(),
                "alert".into(),
                vec![(
                    Located::dummy(Exp::Prim(Prim::String(
                        StringMode::Normal,
                        "clicked".into(),
                    ))),
                    string_type,
                )],
            ),
            span.clone(),
        );
        let helper_decl = Located::new(
            Decl::Val(
                "handler".into(),
                1,
                unit_type.clone(),
                helper_body,
                String::new(),
            ),
            span.clone(),
        );

        let js_use = Located::new(
            Exp::JavaScript(
                JavaScriptMode::Attribute,
                Box::new(Located::new(Exp::Named(1), span.clone())),
            ),
            span.clone(),
        );
        let page_decl = Located::new(
            Decl::Val("page".into(), 2, unit_type.clone(), js_use, String::new()),
            span.clone(),
        );

        let file = (
            vec![helper_decl, page_decl],
            vec![(
                2,
                Sidedness::ServerAndPull,
                crate::monomorphized::DbMode::NoDb,
            )],
        );
        let (_, env_vars) = check(file, &settings, &mut errors);

        assert!(
            !errors.has_errors(),
            "helpers used only from JavaScript should not trip the server-only client-FFI check: {:?}",
            errors.errors
        );
        assert!(env_vars.is_empty());
    }

    #[test]
    fn client_only_ffi_reachable_only_from_javascript_closure_helper_is_allowed() {
        let settings = Settings::default();
        let mut errors = ErrorReporter::new_silent();
        let span = Span::dummy();
        let unit_type = Located::dummy(Typ::Record(vec![]));
        let string_type = Located::dummy(Typ::Ffi("Basis".into(), "string".into()));

        let helper_body = Located::new(
            Exp::FfiApp(
                "Basis".into(),
                "alert".into(),
                vec![(
                    Located::dummy(Exp::Prim(Prim::String(
                        StringMode::Normal,
                        "clicked".into(),
                    ))),
                    string_type,
                )],
            ),
            span.clone(),
        );
        let helper_decl = Located::new(
            Decl::Val(
                "handler".into(),
                1,
                unit_type.clone(),
                helper_body,
                String::new(),
            ),
            span.clone(),
        );

        let js_use = Located::new(
            Exp::JavaScript(
                JavaScriptMode::Attribute,
                Box::new(Located::new(Exp::Closure(1, vec![]), span.clone())),
            ),
            span.clone(),
        );
        let page_decl = Located::new(
            Decl::Val("page".into(), 2, unit_type.clone(), js_use, String::new()),
            span.clone(),
        );

        let file = (
            vec![helper_decl, page_decl],
            vec![(
                2,
                Sidedness::ServerAndPull,
                crate::monomorphized::DbMode::NoDb,
            )],
        );
        let (_, env_vars) = check(file, &settings, &mut errors);

        assert!(
            !errors.has_errors(),
            "closure helpers used only from JavaScript should not trip the server-only client-FFI check: {:?}",
            errors.errors
        );
        assert!(env_vars.is_empty());
    }
}
