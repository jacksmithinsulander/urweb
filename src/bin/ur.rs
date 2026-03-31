//! Ur/Web command-line orchestrator.
//!
//! Dispatches subcommands (`build`, `new`, `fmt`, …) to small binaries: `ur-compile` (compiler driver), `ur-fmt` (formatter), `ur-new` (scaffold).
//!
//! Style-related paths sometimes use Sassy CSS (“scss”) and output Cascading Style Sheets; builds emit Structured Query Language where configured.
//! Project configuration is strict `ur.toml` (Tom's Obvious, Minimal Language), not legacy `urweb.toml`.

use std::process;

use ur::cli_common::{
    self, cli_diagnostic_text, diagnostic_locale_for_cli, writeln_stderr_line, writeln_stdout_line,
};
use ur::diagnostics::{DiagnosticId, DiagnosticLocale};

/// Implement `ur build`: read the manifest, optionally run Sass, then invoke the compiler.
///
/// Builds argv for [`cli_common::exec_peer_bin`] with `ur-compile`. Flag `-dbms` names the database engine (for example `sqlite`);
/// `-db` supplies the connection string for local `.db` files in the default application layout.
///
/// Returns `0` on success, `1` on manifest, stylesheet, or compiler failure (same exit code as the peer binary).
///
/// `verbosity_forward` — leading `-v` / `-vv` / `-verbose` tokens from `ur build` to pass through to `ur-compile`.
fn build_project(verbosity_forward: &[String]) -> i32 {
    let cfg = match cli_common::load_ur_manifest_cwd() {
        Ok(parsed_manifest) => parsed_manifest,
        Err(manifest_error) => {
            cli_common::writeln_stderr_display(manifest_error);
            return 1;
        }
    };
    let locale = diagnostic_locale_for_cli(Some(&cfg.package.language));
    if let Err(entry_error) = cli_common::require_manifest_entry(&cfg) {
        cli_common::writeln_stderr_display(entry_error);
        return 1;
    }

    let kind = cfg.package.kind.as_str();
    let entry = cfg.build.entry.as_str();
    let db = cfg.build.db.as_str();
    if let Err(db_error) = ur::db::validate_manifest_db_engine(db) {
        let message = cli_diagnostic_text(
            DiagnosticId::CliManifestDatabaseEngineInvalid,
            vec![db_error.to_string()],
            locale,
        );
        cli_common::writeln_stderr_display(message);
        return 1;
    }
    let cc = cfg.build.ccompiler.as_str();
    let is_lib = cli_common::is_lib_project(kind);
    let boot = cfg.build.boot;
    let scss = cfg
        .style
        .as_ref()
        .and_then(|style_section| style_section.scss.as_deref());
    let css = cfg
        .style
        .as_ref()
        .and_then(|style_section| style_section.css.as_deref());

    if let (Some(scss_path), Some(css_path)) = (scss, css) {
        if cli_common::has_sass_or_sassc() {
            let has_sass = std::process::Command::new("which")
                .arg("sass")
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .status()
                .is_ok_and(|status| status.success());
            let scss_line =
                cli_diagnostic_text(DiagnosticId::CliOrchestratorScssCompiling, vec![], locale);
            writeln_stdout_line(&scss_line);
            let sass_arg = format!("{}:{}", scss_path, css_path);
            let status = if has_sass {
                std::process::Command::new("sass")
                    .args([sass_arg.as_str(), "--no-source-map", "--style=expanded"])
                    .status()
            } else {
                std::process::Command::new("sassc")
                    .args([scss_path, css_path])
                    .status()
            };
            if !cli_common::command_succeeded(&status) {
                let err =
                    cli_diagnostic_text(DiagnosticId::CliScssCompilationFailed, vec![], locale);
                cli_common::writeln_stderr_display(err);
                return 1;
            }
        }
    }

    let progress = if is_lib {
        cli_diagnostic_text(
            DiagnosticId::CliOrchestratorTypeCheckingLib,
            vec![entry.to_string()],
            locale,
        )
    } else {
        cli_diagnostic_text(
            DiagnosticId::CliOrchestratorBuildingApp,
            vec![entry.to_string()],
            locale,
        )
    };
    writeln_stdout_line(&progress);

    let mut args: Vec<String> = vec![];
    if cli_common::should_add_ccompiler(cc) {
        args.extend(["-ccompiler".to_string(), cc.to_string()]);
    }
    if boot {
        args.push("-boot".to_string());
    }
    if is_lib {
        args.extend(["-tc".to_string(), entry.to_string()]);
    } else {
        args.extend([
            "-dbms".to_string(),
            db.to_string(),
            "-db".to_string(),
            format!("{}.db", entry),
            "-sql".to_string(),
            format!("{}.sql", entry),
            entry.to_string(),
        ]);
    }

    args.extend(verbosity_forward.iter().cloned());
    cli_common::exec_peer_bin("ur-compile", &args)
}

/// Print localized orchestrator help to standard output (compiler tail follows same catalog).
///
/// `locale` drives which template table [`cli_diagnostic_text`] selects.
fn print_orchestrator_help(locale: DiagnosticLocale) {
    let usage_heading = cli_diagnostic_text(DiagnosticId::CliUsageHeading, vec![], locale);
    writeln_stdout_line(&usage_heading);
    let body = cli_diagnostic_text(DiagnosticId::CliOrchestratorUsageLines, vec![], locale);
    for line in body.lines() {
        writeln_stdout_line(line);
    }
    writeln_stdout_line("");
    let footer = cli_diagnostic_text(DiagnosticId::CliOrchestratorUsageMoreHelp, vec![], locale);
    writeln_stdout_line(&footer);
}

/// Dispatch argv after the program name: run a helper binary or treat the tail as a compiler invocation.
///
/// `args` is the command-line slice without `argv[0]`; the first token picks the subcommand.
/// Returns the child exit status, or `1` for usage errors. Unknown first tokens are forwarded to `ur-compile` (legacy `ur Project` style).
fn dispatch(args: &[String]) -> i32 {
    let default_locale = diagnostic_locale_for_cli(None);
    match args.first().map(|token| token.as_str()) {
        None => {
            let missing = cli_diagnostic_text(
                DiagnosticId::CliDispatchMissingSubcommand,
                vec![],
                default_locale,
            );
            writeln_stderr_line(&missing);
            let hint =
                cli_diagnostic_text(DiagnosticId::CliDispatchRunHelpHint, vec![], default_locale);
            writeln_stderr_line(&hint);
            1
        }
        Some("-h") | Some("--help") => {
            print_orchestrator_help(default_locale);
            0
        }
        Some("new") => {
            let rest: Vec<String> = args[1..].to_vec();
            cli_common::exec_peer_bin("ur-new", &rest)
        }
        Some("build") => {
            let verbosity = cli_common::leading_build_verbosity_flags(&args[1..]);
            build_project(&verbosity)
        }
        Some("install") => {
            let rest: Vec<String> = args[1..].to_vec();
            cli_common::exec_peer_bin("ur-install", &rest)
        }
        Some("fmt") => {
            let rest: Vec<String> = args[1..].to_vec();
            cli_common::exec_peer_bin("ur-fmt", &rest)
        }
        Some("daemon") => {
            let rest: Vec<String> = args[1..].to_vec();
            cli_common::exec_peer_bin("ur-daemon", &rest)
        }
        Some("lsp") => cli_common::exec_peer_bin("ur-lsp", &[]),
        Some("debugger") => {
            let rest: Vec<String> = args[1..].to_vec();
            cli_common::exec_peer_bin("ur-debugger", &rest)
        }
        Some(_) => {
            let forwarded: Vec<String> = args.to_vec();
            cli_common::exec_peer_bin("ur-compile", &forwarded)
        }
    }
}

/// Program entry: forwards `std::env::args()` minus the executable path to [`dispatch`], then exits with that status.
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let code = dispatch(&args[1..]);
    process::exit(code);
}
