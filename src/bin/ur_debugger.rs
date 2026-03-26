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

use anyhow::{Context, Result};

/// Drop `argv[0]`, call [`run`], exit with `1` on error.
fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if let Err(e) = run(args) {
        eprintln!("ur-debugger: {e:#}");
        std::process::exit(1);
    }
}

/// Run the Debug Adapter Protocol server, GDB machine-interface passthrough, interactive terminal mode, or print help.
///
/// `args` is argv without the program name. `--dap` calls [`ur::debugger::run_dap_stdio`] on standard input and output.
fn run(args: Vec<String>) -> Result<()> {
    match args.first().map(|s| s.as_str()) {
        None | Some("-h") | Some("--help") => {
            print_usage();
            Ok(())
        }
        Some("--dap") => ur::debugger::run_dap_stdio().context("DAP server"),
        Some("--gdb") => gdb_mi_passthrough(&args[1..]),
        Some("--tty") => gdb_tty(&args[1..]),
        Some(other) if other.starts_with('-') => {
            eprintln!("unknown option: {other}\n");
            print_usage();
            Err(anyhow::anyhow!("bad arguments"))
        }
        _ => {
            print_usage();
            Err(anyhow::anyhow!("missing mode; use --dap, --gdb, or --tty"))
        }
    }
}

/// Print mode summary and examples to standard error.
fn print_usage() {
    eprintln!(
        "\
ur-debugger — native debugger (DAP + GDB/MI or lldb-mi)

Modes:
  --dap              DAP server on stdio (VS Code, Zed, Neovim, Emacs dap-mode, …)
  --gdb -- [args]    Passthrough: gdb -q --interpreter=mi3 [args]
  --tty [--run] PROG [ARG ...]
                     Interactive GDB: gdb -q [--ex run] --args PROG [ARG ...]

Launch JSON (DAP): use gdbPath / miDebuggerPath; set MIMode to \"gdb\" (default) or \"lldb\"
for lldb-mi. Build the app with ur-compile -debug so the binary is compiled with -g.

Examples:
  ur-debugger --dap
  ur-debugger --gdb -- -ex 'file ./myapp' -ex run
  ur-debugger --tty --run ./myapp
"
    );
}

/// Run `gdb -q --interpreter=mi3` with extra arguments from `rest`.
///
/// Skips a leading `--` in `rest` (tokens after `ur-debugger --gdb`). Returns `Ok` only if GDB exits successfully.
fn gdb_mi_passthrough(rest: &[String]) -> Result<()> {
    let mut cmd = std::process::Command::new("gdb");
    cmd.args(["-q", "--interpreter=mi3"]);
    let args: Vec<&str> = rest
        .iter()
        .skip_while(|s| *s == "--")
        .map(String::as_str)
        .collect();
    cmd.args(args);
    let status = cmd
        .status()
        .context("failed to run gdb (install GDB; on macOS see Homebrew gdb + codesigning)")?;
    if status.success() {
        Ok(())
    } else {
        Err(anyhow::anyhow!("gdb exited with {status}"))
    }
}

/// Start an interactive GDB session on the user’s terminal for a program and its arguments.
///
/// `rest` may start with `--run`, then the program path, then arguments for the debugged process.
/// On Unix may replace this process with `exec`; elsewhere spawns GDB and waits. Returns `Ok` on clean GDB exit.
fn gdb_tty(rest: &[String]) -> Result<()> {
    let mut run_first = false;
    let mut i = 0usize;
    if rest.first().map(|s| s.as_str()) == Some("--run") {
        run_first = true;
        i = 1;
    }
    let prog = rest
        .get(i)
        .context("--tty requires a program path (see ur-debugger --help)")?;
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
        Err(anyhow::anyhow!("exec gdb: {e}"))
    }
    #[cfg(not(unix))]
    {
        let mut cmd = std::process::Command::new("gdb");
        cmd.arg("-q");
        if run_first {
            cmd.arg("-ex").arg("run");
        }
        cmd.arg("--args").arg(prog);
        cmd.args(trailing);
        let status = cmd.status().context("gdb")?;
        if status.success() {
            Ok(())
        } else {
            Err(anyhow::anyhow!("gdb exited with {status}"))
        }
    }
}
