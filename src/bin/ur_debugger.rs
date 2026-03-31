//! Debug Adapter Protocol on standard input and output, plus GNU Debugger launch helpers (`ur-debugger`).
//!
//! The adapter speaks JSON remote procedure calls on stdio; `--gdb` uses GDB’s machine-interface text protocol (`mi3`).
//! Build with `ur-compile -debug` (or a `debug` line in the `.urp`) so linking passes `-g` and the binary includes DWARF debugging information.
//! The C backend emits `#line` back to `.ur` where spans exist so breakpoints can name Ur sources when the debug data lists them.
//!
//! ## Editor usage
//! Point the debug adapter at `ur-debugger --dap` (standard output must carry only protocol JSON).
//!
//! Implemented DAP (subset): `initialize`, `launch`, `attach`, `configurationDone`, `setBreakpoints`,
//! `breakpointLocations`, `setExceptionBreakpoints` (signal / C++ catch filters), `setDataBreakpoints`,
//! `setInstructionBreakpoints`, `setFunctionBreakpoints`, `continue` / `next` / `stepIn` / `stepOut`, `pause`,
//! `evaluate`, `setVariable`, `disassemble`, `loadedSources`, `source`, `exceptionInfo`, `modules`, `threads`,
//! `stackTrace`, `scopes`, `variables`, `disconnect`, `terminate`, `shutdown`; `stopped` + `terminated` on exit;
//! `entry` when `stopAtEntry` is set; **`loadedSource`** when new files show up in the inferior after stops.
//!
//! **Style:** this binary follows [README.md](../../README.md) Rust code style where edited.

use anyhow::Result;

use ur::cli_common::{cli_diagnostic_text, diagnostic_locale_for_cli};
use ur::diagnostics::{DiagnosticId, DiagnosticLocale};

/// Drop `argv[0]`, call [`run`], exit with `1` on error.
fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if let Err(run_error) = run(args) {
        let locale = diagnostic_locale_for_cli(None);
        let body = cli_diagnostic_text(
            DiagnosticId::CliDebuggerRunFailed,
            vec![format!("{run_error:#}")],
            locale,
        );
        let bannered =
            ur::error_types::format_tool_diagnostic_banner_and_body("ur-debugger", &body);
        ur::cli_common::writeln_stderr_display(bannered);
        std::process::exit(1);
    }
}

/// Run the Debug Adapter Protocol server, GDB machine-interface passthrough, interactive terminal mode, or print help.
///
/// `args` is argv without the program name. `--dap` calls [`ur::debugger::run_dap_stdio`] on standard input and output.
fn run(args: Vec<String>) -> Result<()> {
    let locale = diagnostic_locale_for_cli(None);
    match args.first().map(|s| s.as_str()) {
        None | Some("-h") | Some("--help") => {
            print_usage();
            Ok(())
        }
        Some("--dap") => ur::debugger::run_dap_stdio().map_err(|dap_error| {
            anyhow::anyhow!(
                "{}",
                cli_diagnostic_text(
                    DiagnosticId::CliDebuggerCliDapStdioFailed,
                    vec![format!("{dap_error:#}")],
                    locale,
                )
            )
        }),
        Some("--gdb") => gdb_mi_passthrough(&args[1..]),
        Some("--tty") => gdb_tty(&args[1..], locale),
        Some(other) if other.starts_with('-') => {
            let body = cli_diagnostic_text(
                DiagnosticId::CliDebuggerUnknownFlag,
                vec![other.to_string()],
                locale,
            );
            let bannered =
                ur::error_types::format_tool_diagnostic_banner_and_body("ur-debugger", &body);
            ur::cli_common::writeln_stderr_display(bannered);
            print_usage();
            Err(anyhow::anyhow!(""))
        }
        _ => {
            let body = cli_diagnostic_text(DiagnosticId::CliDebuggerMissingMode, vec![], locale);
            let bannered =
                ur::error_types::format_tool_diagnostic_banner_and_body("ur-debugger", &body);
            ur::cli_common::writeln_stderr_display(bannered);
            print_usage();
            Err(anyhow::anyhow!(""))
        }
    }
}

/// Print mode summary and examples to standard error.
fn print_usage() {
    let locale = diagnostic_locale_for_cli(None);
    let usage_text = cli_diagnostic_text(DiagnosticId::CliDebuggerUsageBody, vec![], locale);
    ur::cli_common::writeln_stderr_display(usage_text);
}

/// Run `gdb -q --interpreter=mi3` with extra arguments from `rest`.
///
/// Skips a leading `--` in `rest` (tokens after `ur-debugger --gdb`). Returns `Ok` only if GDB exits successfully.
fn gdb_mi_passthrough(rest: &[String]) -> Result<()> {
    let locale = diagnostic_locale_for_cli(None);
    let mut cmd = std::process::Command::new("gdb");
    cmd.args(["-q", "--interpreter=mi3"]);
    let args: Vec<&str> = rest
        .iter()
        .skip_while(|s| *s == "--")
        .map(String::as_str)
        .collect();
    cmd.args(args);
    let status = cmd.status().map_err(|spawn_error| {
        anyhow::anyhow!(
            "{}",
            cli_diagnostic_text(
                DiagnosticId::CliDebuggerGdbSpawnFailed,
                vec![spawn_error.to_string()],
                locale,
            )
        )
    })?;
    if status.success() {
        Ok(())
    } else {
        let code = status
            .code()
            .map(|code| code.to_string())
            .unwrap_or_else(|| "unknown".to_string());
        Err(anyhow::anyhow!(
            "{}",
            cli_diagnostic_text(
                DiagnosticId::CliDebuggerGdbExitedNonZero,
                vec![code],
                locale,
            )
        ))
    }
}

/// Start an interactive GDB session on the user’s terminal for a program and its arguments.
///
/// `rest` may start with `--run`, then the program path, then arguments for the debugged process.
/// On Unix may replace this process with `exec`; elsewhere spawns GDB and waits. Returns `Ok` on clean GDB exit.
fn gdb_tty(rest: &[String], locale: DiagnosticLocale) -> Result<()> {
    let mut run_first = false;
    let mut i = 0usize;
    if rest.first().map(|s| s.as_str()) == Some("--run") {
        run_first = true;
        i = 1;
    }
    let prog = rest.get(i).ok_or_else(|| {
        anyhow::anyhow!(
            "{}",
            cli_diagnostic_text(
                DiagnosticId::CliDebuggerCliTtyRequiresProgramPath,
                vec![],
                locale,
            )
        )
    })?;
    let trailing: Vec<&str> = rest[i + 1..].iter().map(String::as_str).collect();

    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        let mut cmd = std::process::Command::new("gdb");
        cmd.arg("-q");
        if run_first {
            cmd.arg("-ex").arg("run");
        }
        cmd.arg("--args").arg(prog);
        cmd.args(trailing);
        let e = cmd.exec();
        let locale = diagnostic_locale_for_cli(None);
        Err(anyhow::anyhow!(
            "{}",
            cli_diagnostic_text(
                DiagnosticId::CliDebuggerGdbExecFailed,
                vec![e.to_string()],
                locale,
            )
        ))
    }
    #[cfg(not(unix))]
    {
        let locale = diagnostic_locale_for_cli(None);
        let mut cmd = std::process::Command::new("gdb");
        cmd.arg("-q");
        if run_first {
            cmd.arg("-ex").arg("run");
        }
        cmd.arg("--args").arg(prog);
        cmd.args(trailing);
        let status = cmd.status().map_err(|spawn_error| {
            anyhow::anyhow!(
                "{}",
                cli_diagnostic_text(
                    DiagnosticId::CliDebuggerGdbSpawnFailed,
                    vec![spawn_error.to_string()],
                    locale,
                )
            )
        })?;
        if status.success() {
            Ok(())
        } else {
            let code = status
                .code()
                .map(|code| code.to_string())
                .unwrap_or_else(|| "unknown".to_string());
            Err(anyhow::anyhow!(
                "{}",
                cli_diagnostic_text(
                    DiagnosticId::CliDebuggerGdbExitedNonZero,
                    vec![code],
                    locale,
                )
            ))
        }
    }
}
