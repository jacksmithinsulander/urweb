//! ur-compile — Compile Ur/Web projects to native executables and emit **SQL** (Structured Query Language) DDL.
//!
//! Mentions elsewhere: Language Server Protocol helpers, compiler intermediate representation, Structured Query Language schema output,
//! and foreign function interface lines in `.urp` project files.
//!
//! **Style:** [README.md](../../README.md) Rust conventions when this file is edited.

use std::process;

use ur::cli_common::{
    self, cli_diagnostic_text, diagnostic_locale_for_cli, writeln_stderr_display,
    writeln_stderr_line, writeln_stdout_display, writeln_stdout_line,
};
use ur::diagnostics::DiagnosticId;
use ur::error_types::{format_compile_error_for_terminal, CompileError};
use ur::settings::{LanguageCompilationProfile, Settings};

const VERSION_STRING: &str = env!("CARGO_PKG_VERSION");

/// Print usage: orchestrator lines from the catalog plus compiler-specific flags.
///
/// `-dbms` picks the database engine; `-tc` stops after type checking (no code generation).
fn print_usage(settings: &Settings) {
    let locale = settings.diagnostic_locale;
    let usage_heading = cli_diagnostic_text(DiagnosticId::CliUsageHeading, vec![], locale);
    writeln_stdout_line(&usage_heading);
    let orchestrator_block =
        cli_diagnostic_text(DiagnosticId::CliOrchestratorUsageLines, vec![], locale);
    for line in orchestrator_block.lines() {
        writeln_stdout_line(line);
    }
    let extra = cli_diagnostic_text(DiagnosticId::CliUrCompileHelpExtra, vec![], locale);
    for line in extra.lines() {
        writeln_stdout_line(line);
    }
}

/// Parse `ur-compile` arguments and run the full pipeline through C output and Structured Query Language artifacts when requested.
///
/// `args` is argv after the program name. Returns `0` on success (including type-check-only mode), non-zero on diagnostics or input/output failure.
/// Updates [`Settings`] from flags, then calls [`ur::compiler::compile`].
pub fn run_compiler_args(args: &[String]) -> i32 {
    let mut settings = Settings::new();
    let mut project_file: Option<String> = None;
    let mut _dump_source = false;
    let mut _do_iflow = false;
    let mut _partial_build: Option<String> = None;
    let mut demo_prefix: Option<String> = None;
    let mut demo_guided = false;

    let mut args_iter = args.iter();
    // Each pass consumes at least one argv entry; cap passes by argv length so a flag-parse bug cannot spin.
    for _cli_flag_pass in 0..args.len() {
        let Some(arg) = args_iter.next() else {
            break;
        };
        let raw = arg.trim_start_matches('-');
        let (flag, opt_val) = if let Some(eq) = raw.find('=') {
            let (flag_part, value_part) = raw.split_at(eq);
            (flag_part, Some(value_part[1..].to_string()))
        } else {
            (raw, None)
        };
        match flag {
            "help" | "h" => {
                print_usage(&settings);
                return 0;
            }
            "version" | "V" => {
                writeln_stdout_display(VERSION_STRING);
                return 0;
            }
            "numeric-version" => {
                writeln_stdout_display(VERSION_STRING);
                return 0;
            }
            "print-ccompiler" => {
                writeln_stdout_display(&settings.config_c_compiler);
                return 0;
            }
            "print-cinclude" => {
                writeln_stdout_display(&settings.config_include);
                return 0;
            }
            "ccompiler" => {
                if let Some(cc) = opt_val.or_else(|| args_iter.next().cloned()) {
                    settings.config_c_compiler = cc;
                }
            }
            "protocol" => {
                if let Some(protocol_value) = opt_val.or_else(|| args_iter.next().cloned()) {
                    settings.protocol = protocol_value;
                }
            }
            "prefix" => {
                if let Some(prefix_value) = opt_val.or_else(|| args_iter.next().cloned()) {
                    settings.set_url_prefix(&prefix_value);
                }
            }
            "db" => {
                if let Some(db_value) = opt_val.or_else(|| args_iter.next().cloned()) {
                    settings.dbstring = Some(db_value);
                }
            }
            "dbms" => {
                if let Some(db_token) = opt_val.or_else(|| args_iter.next().cloned()) {
                    if let Err(backend_error) =
                        ur::db::set_backend_from_cli_token(&mut settings, &db_token)
                    {
                        let locale = settings.diagnostic_locale;
                        let msg = cli_diagnostic_text(
                            DiagnosticId::CliDatabaseBackendCliRejected,
                            vec![backend_error],
                            locale,
                        );
                        cli_common::writeln_stderr_display(msg);
                        return 1;
                    }
                }
            }
            "debug" => {
                settings.debug = true;
            }
            "verbose" => {
                settings.verbosity = settings
                    .verbosity
                    .clamp(2, ur::compiler_tracing::MAX_COMPILER_VERBOSITY);
            }
            "timing" => {
                settings.emit_phase_timing = true;
            }
            "tc" => {
                settings.typecheck_only = true;
            }
            "languageProfile" => {
                if let Some(raw_profile) = opt_val.or_else(|| args_iter.next().cloned()) {
                    match raw_profile.parse::<LanguageCompilationProfile>() {
                        Ok(profile) => {
                            settings.language_compilation_profile = profile;
                        }
                        Err(()) => {
                            let locale = settings.diagnostic_locale;
                            let msg = cli_diagnostic_text(
                                DiagnosticId::CliLanguageProfileInvalidValue,
                                vec![raw_profile.clone()],
                                locale,
                            );
                            cli_common::writeln_stderr_display(msg);
                            return 1;
                        }
                    }
                }
            }
            "dumpSource" => {
                _dump_source = true;
            }
            "output" | "o" => {
                if let Some(path) = opt_val.or_else(|| args_iter.next().cloned()) {
                    settings.exe = Some(path);
                }
            }
            "sql" => {
                if let Some(path) = opt_val.or_else(|| args_iter.next().cloned()) {
                    settings.sql = Some(path);
                }
            }
            "endpoints" => {
                if let Some(path) = opt_val.or_else(|| args_iter.next().cloned()) {
                    settings.endpoints = Some(path);
                }
            }
            "static" => {
                settings.static_linking = true;
            }
            "boot" => {
                settings.boot_linking = true;
            }
            "sigfile" => {
                if let Some(path) = opt_val.or_else(|| args_iter.next().cloned()) {
                    settings.sig_file = Some(path);
                }
            }
            "iflow" => {
                _do_iflow = true;
            }
            "sqlcache" => {
                settings.sqlcache = true;
            }
            "disablesqlstructurecheck" => {
                settings.disable_sql_structure_check = true;
            }
            "moduleOf" => {
                if let Some(path) = opt_val.or_else(|| args_iter.next().cloned()) {
                    writeln_stdout_display(ur::compiler::module_of(&path));
                }
                return 0;
            }
            "limit" => {
                let class = args_iter.next().cloned().unwrap_or_default();
                let num_str = args_iter.next().cloned().unwrap_or_default();
                match num_str.parse::<i32>() {
                    Ok(limit_n) if cli_common::is_valid_limit(limit_n) => {
                        if let Err(limit_error) = settings.add_limit(&class, limit_n) {
                            let locale = settings.diagnostic_locale;
                            let msg = cli_diagnostic_text(
                                DiagnosticId::CliCompileResourceLimitConfiguration,
                                vec![limit_error],
                                locale,
                            );
                            cli_common::writeln_stderr_display(msg);
                            return 1;
                        }
                    }
                    _ => {
                        let locale = settings.diagnostic_locale;
                        let msg = cli_diagnostic_text(
                            DiagnosticId::CliInvalidLimitNumber,
                            vec![num_str.clone()],
                            locale,
                        );
                        cli_common::writeln_stderr_display(msg);
                        return 1;
                    }
                }
            }
            "demo" => {
                if let Some(prefix) = opt_val.or_else(|| args_iter.next().cloned()) {
                    demo_prefix = Some(prefix);
                    demo_guided = false;
                }
            }
            "guided-demo" => {
                if let Some(prefix) = opt_val.or_else(|| args_iter.next().cloned()) {
                    demo_prefix = Some(prefix);
                    demo_guided = true;
                }
            }
            "noEmacs" => {}
            "partialBuild" => {
                if let Some(module_name) = opt_val.or_else(|| args_iter.next().cloned()) {
                    _partial_build = Some(module_name);
                }
            }
            "startLspServer" => {
                return cli_common::exec_peer_bin("ur-lsp", &[]);
            }
            other if !other.is_empty() && other.len() <= 5 && other.chars().all(|ch| ch == 'v') => {
                cli_common::apply_verbosity_v_flag(&mut settings, other);
            }
            "path" => {
                let _ = args_iter.next();
                let _ = args_iter.next();
            }
            "root" => {
                let _ = args_iter.next();
                let _ = args_iter.next();
            }
            other => {
                if cli_common::is_unknown_compiler_flag(other, arg) {
                    let locale = settings.diagnostic_locale;
                    let msg = cli_diagnostic_text(
                        DiagnosticId::CliUnknownCompilerFlag,
                        vec![arg.clone()],
                        locale,
                    );
                    cli_common::writeln_stderr_display(msg);
                    return 1;
                }
                project_file = Some(arg.clone());
            }
        }
    }

    if let Some(prefix) = demo_prefix {
        let dirname = match project_file {
            Some(dir) => dir,
            None => {
                let locale = settings.diagnostic_locale;
                let msg =
                    cli_diagnostic_text(DiagnosticId::CliDemoRequiresDirectory, vec![], locale);
                cli_common::writeln_stderr_display(msg);
                return 1;
            }
        };
        match ur::demo::make(&prefix, &dirname, &mut settings, demo_guided) {
            Ok(true) => return 0,
            Ok(false) => return 1,
            Err(demo_error) => {
                let locale = settings.diagnostic_locale;
                let msg = cli_diagnostic_text(
                    DiagnosticId::CliDemoModeFailed,
                    vec![format!("{demo_error:#}")],
                    locale,
                );
                cli_common::writeln_stderr_display(msg);
                return 1;
            }
        }
    }

    let project = match project_file {
        Some(path) => path,
        None => {
            let locale = settings.diagnostic_locale;
            let msg = cli_diagnostic_text(DiagnosticId::CliNoProjectSeeHelp, vec![], locale);
            cli_common::writeln_stderr_display(msg);
            return 1;
        }
    };

    let urp_path = std::path::Path::new(&project);
    match ur::compiler::compile(urp_path, &mut settings).into_result() {
        Ok(_exe) => 0,
        Err(compile_error) => {
            let locale = settings.diagnostic_locale;
            let text = match compile_error.downcast::<CompileError>() {
                Ok(ce) => format_compile_error_for_terminal(&ce, locale),
                Err(err) => format!("{err:#}"),
            };
            cli_common::writeln_stderr_display(text);
            1
        }
    }
}

/// Spawn a worker thread with a large stack, run [`run_compiler_args`], then exit with its status.
///
/// Stack size is [`ur::COMPILE_THREAD_STACK_BYTES`] so deep elaboration (type inference) does not overflow the default thread stack.
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let worker = match std::thread::Builder::new()
        .stack_size(ur::COMPILE_THREAD_STACK_BYTES)
        .spawn(move || run_compiler_args(&args[1..]))
    {
        Ok(handle) => handle,
        Err(thread_error) => {
            let locale = diagnostic_locale_for_cli(None);
            let text = cli_diagnostic_text(
                DiagnosticId::CliCompilerWorkerSpawnFailed,
                vec![
                    ur::COMPILE_THREAD_STACK_BYTES.to_string(),
                    thread_error.to_string(),
                ],
                locale,
            );
            writeln_stderr_display(text);
            process::exit(1);
        }
    };
    let code = match worker.join() {
        Ok(exit) => exit,
        Err(_) => {
            let locale = diagnostic_locale_for_cli(None);
            let text = cli_diagnostic_text(DiagnosticId::CliCompilerWorkerPanicked, vec![], locale);
            writeln_stderr_line(&text);
            1
        }
    };
    process::exit(code);
}
