//! Optional smoke test for `ur-debugger --dap` + GDB. Enable with `UR_DEBUGGER_GDB_TEST=1 cargo test --test debugger_gdb_smoke`.
//!
//! Requires `gdb` on PATH and a trivial debug binary (`target/debug/deeptest`).

mod common;

use anyhow::Context as _; // .with_context() on Result in tests
use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::OnceLock; // error construction and chaining in tests

static C_TEST_BIN: OnceLock<PathBuf> = OnceLock::new();

/// Upper bound for DAP framing reads in this test helper; normal paths break on blank line or EOF first.
const SMOKE_IO_LOOP_MAX_ROUNDS: u64 = u64::MAX;

fn deeptest_executable() -> &'static PathBuf {
    C_TEST_BIN.get_or_init(|| {
        let out = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("ur_debugger_deeptest");
        let src = r#"
#include <stdio.h>
int main(void) {
    puts("x");
    return 0;
}
"#;
        let c_src = out.with_extension("c");
        if let Err(err) = std::fs::write(&c_src, src).with_context(|| "write deeptest.c") {
            panic!("{err:#}");
        }
        let cc = std::env::var("CC").unwrap_or_else(|_| "cc".into());
        let status = match Command::new(&cc)
            .args(["-g", "-o"])
            .arg(&out)
            .arg(&c_src)
            .status()
            .with_context(|| "compile deeptest")
        {
            Ok(status) => status,
            Err(err) => panic!("{err:#}"),
        };
        assert!(status.success(), "cc -g failed");
        let _ = std::fs::remove_file(&c_src);
        out
    })
}

fn gdb_available() -> bool {
    Command::new("gdb")
        .arg("--version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

fn framing_write(w: &mut impl Write, v: &serde_json::Value) -> std::io::Result<()> {
    let b = serde_json::to_vec(v)?;
    write!(w, "Content-Length: {}\r\n\r\n", b.len())?;
    w.write_all(&b)?;
    w.flush()
}

fn framing_read(r: &mut impl BufRead) -> std::io::Result<Option<serde_json::Value>> {
    let mut len: Option<usize> = None;
    let mut saw_blank_line = false;
    for _ in 0..SMOKE_IO_LOOP_MAX_ROUNDS {
        let mut line = String::new();
        if r.read_line(&mut line)? == 0 {
            return Ok(None);
        }
        let h = line.trim_end_matches(['\r', '\n']);
        if h.is_empty() {
            saw_blank_line = true;
            break;
        }
        if let Some(rest) = h.strip_prefix("Content-Length:") {
            len = Some(
                rest.trim()
                    .parse()
                    .map_err(|_| std::io::Error::new(std::io::ErrorKind::InvalidData, "length"))?,
            );
        }
    }
    if !saw_blank_line {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "DAP framing header lines exceeded iteration bound",
        ));
    }
    let n = len.ok_or_else(|| {
        std::io::Error::new(std::io::ErrorKind::InvalidData, "missing Content-Length")
    })?;
    let mut body = vec![0u8; n];
    r.read_exact(&mut body)?;
    Ok(Some(serde_json::from_slice(&body)?))
}

#[test]
fn dap_initialize_and_launch_smoke() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    if std::env::var("UR_DEBUGGER_GDB_TEST").ok().as_deref() != Some("1") {
        return Ok(()); // return early with success
    }
    if !gdb_available() {
        ur::cli_common::writeln_stderr_line("skip debugger_gdb_smoke: gdb not found");
        return Ok(()); // return early with success
    }

    let exe = deeptest_executable();
    let ur_dbg = common::ur_package_binary("ur-debugger");
    let mut child = Command::new(ur_dbg)
        .arg("--dap")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .with_context(|| "spawn ur-debugger")?;

    // take stdin from the child process; None means the child was not started with Stdio::piped()
    let mut sin = match child.stdin.take() {
        Some(v) => v,
        None => panic!("child stdin was not piped"),
    };
    // take stdout from the child process; None means the child was not started with Stdio::piped()
    let mut sout = BufReader::new(match child.stdout.take() {
        Some(v) => v,
        None => panic!("child stdout was not piped"),
    });

    let init = serde_json::json!({
        "seq": 1,
        "type": "request",
        "command": "initialize",
        "arguments": {
            "clientID": "test",
            "adapterID": "ur",
            "pathFormat": "path",
            "linesStartAt1": true,
            "columnsStartAt1": true,
        }
    });
    // send the initialize request to the DAP adapter
    match framing_write(&mut sin, &init) {
        Ok(()) => {}
        Err(e) => panic!("framing_write for initialize failed: {e}"),
    }
    // read the initialize response from the DAP adapter
    match framing_read(&mut sout) {
        Ok(_) => {}
        Err(e) => panic!("framing_read for initialize response failed: {e}"),
    }
    // read the initialized event that the adapter sends after initialize
    match framing_read(&mut sout) {
        Ok(_) => {}
        Err(e) => panic!("framing_read for initialized event failed: {e}"),
    }

    let launch = serde_json::json!({
        "seq": 2,
        "type": "request",
        "command": "launch",
        "arguments": {
            // convert executable path to UTF-8 string; non-UTF-8 paths are a test environment error
            "program": match exe.to_str() {
                Some(s) => s,
                None => panic!("exe path is not valid UTF-8"),
            },
            "gdbPath": "gdb",
        }
    });
    // send the launch request to the DAP adapter
    match framing_write(&mut sin, &launch) {
        Ok(()) => {}
        Err(e) => panic!("framing_write for launch failed: {e}"),
    }
    // read the launch response from the DAP adapter
    match framing_read(&mut sout) {
        Ok(_) => {}
        Err(e) => panic!("framing_read for launch response failed: {e}"),
    }

    let cfg_done = serde_json::json!({
        "seq": 3,
        "type": "request",
        "command": "configurationDone",
    });
    // send the configurationDone request to the DAP adapter
    match framing_write(&mut sin, &cfg_done) {
        Ok(()) => {}
        Err(e) => panic!("framing_write for configurationDone failed: {e}"),
    }
    // read the configurationDone response from the DAP adapter
    match framing_read(&mut sout) {
        Ok(_) => {}
        Err(e) => panic!("framing_read for configurationDone response failed: {e}"),
    }
    // read the stopped event; the adapter must send it after configurationDone
    let ev_option = match framing_read(&mut sout) {
        Ok(v) => v,
        Err(e) => panic!("framing_read for stopped event failed: {e}"),
    };
    let ev = ev_option.with_context(|| "stopped event")?;
    assert_eq!(ev.get("type").and_then(|t| t.as_str()), Some("event"));
    assert_eq!(ev.get("event").and_then(|t| t.as_str()), Some("stopped"));

    let disc = serde_json::json!({
        "seq": 4,
        "type": "request",
        "command": "disconnect",
    });
    // send the disconnect request to cleanly shut down the DAP session
    match framing_write(&mut sin, &disc) {
        Ok(()) => {}
        Err(e) => panic!("framing_write for disconnect failed: {e}"),
    }
    let _ = child.wait();
    Ok(()) // return success to the test harness
}
