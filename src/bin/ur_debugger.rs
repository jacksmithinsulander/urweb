//! ur-debugger — DAP over stdio (GDB/MI) plus `gdb` terminal helpers.
//!
//! Build Ur/Web with `ur-compile -debug` so the executable contains DWARF. Until the C backend
//! emits `#line` for `.ur` files, set breakpoints on generated `.c` paths (or paths in DWARF).
//!
//! ## Editor usage
//! Point the debug adapter at `ur-debugger` with argument `--dap` (stdout must be JSON-RPC only).
//!
//! Implemented DAP (subset): `initialize`, `launch`, `attach`, `configurationDone`, `setBreakpoints`,
//! `continue` / `next` / `stepIn` / `stepOut`, `pause`, `evaluate`, `setVariable`, `disassemble`,
//! `threads`, `stackTrace`, `scopes`, `variables`, `disconnect`, `terminate`, `shutdown`; `stopped`
//! + `terminated` on process exit; `entry` stop reason when `stopAtEntry` is set.
//! With `ur-compile -debug`, C includes `#line` back to `.ur` where spans are present (per decl).

use anyhow::{Context, Result};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if let Err(e) = run(args) {
        eprintln!("ur-debugger: {e:#}");
        std::process::exit(1);
    }
}

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

fn print_usage() {
    eprintln!(
        "\
ur-debugger — native debugger (Debug Adapter Protocol + GDB)

Modes:
  --dap              Run as a DAP server on stdio (for VS Code, Zed, Neovim, Emacs dap-mode)
  --gdb -- [args]    Start GDB in MI3 mode: gdb -q --interpreter=mi3 [args]
  --tty [--run] PROG [ARG ...]
                     Exec interactive GDB: gdb -q [--ex run] --args PROG [ARG ...]

Examples:
  ur-debugger --dap
  ur-debugger --gdb -- -ex 'file ./myapp' -ex run
  ur-debugger --tty --run ./myapp
"
    );
}

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
