//! Optional smoke test for `ur-debugger --dap` + GDB. Enable with `UR_DEBUGGER_GDB_TEST=1 cargo test --test debugger_gdb_smoke`.
//!
//! Requires `gdb` on PATH and a trivial debug binary (`target/debug/deeptest`).

mod common;

use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::OnceLock;

static C_TEST_BIN: OnceLock<PathBuf> = OnceLock::new();

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
        std::fs::write(&c_src, src).expect("write deeptest.c");
        let cc = std::env::var("CC").unwrap_or_else(|_| "cc".into());
        let status = Command::new(&cc)
            .args(["-g", "-o"])
            .arg(&out)
            .arg(&c_src)
            .status()
            .expect("compile deeptest");
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
    loop {
        let mut line = String::new();
        if r.read_line(&mut line)? == 0 {
            return Ok(None);
        }
        let h = line.trim_end_matches(['\r', '\n']);
        if h.is_empty() {
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
    let n = len.ok_or_else(|| {
        std::io::Error::new(std::io::ErrorKind::InvalidData, "missing Content-Length")
    })?;
    let mut body = vec![0u8; n];
    r.read_exact(&mut body)?;
    Ok(Some(serde_json::from_slice(&body)?))
}

#[test]
fn dap_initialize_and_launch_smoke() {
    if std::env::var("UR_DEBUGGER_GDB_TEST").ok().as_deref() != Some("1") {
        return;
    }
    if !gdb_available() {
        ur::cli_common::writeln_stderr_line("skip debugger_gdb_smoke: gdb not found");
        return;
    }

    let exe = deeptest_executable();
    let ur_dbg = common::ur_package_binary("ur-debugger");
    let mut child = Command::new(ur_dbg)
        .arg("--dap")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ur-debugger");

    let mut sin = child.stdin.take().unwrap();
    let mut sout = BufReader::new(child.stdout.take().unwrap());

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
    framing_write(&mut sin, &init).unwrap();
    let _ = framing_read(&mut sout).unwrap(); // initialize response
    let _ = framing_read(&mut sout).unwrap(); // initialized event

    let launch = serde_json::json!({
        "seq": 2,
        "type": "request",
        "command": "launch",
        "arguments": {
            "program": exe.to_str().unwrap(),
            "gdbPath": "gdb",
        }
    });
    framing_write(&mut sin, &launch).unwrap();
    let _ = framing_read(&mut sout).unwrap();

    let cfg_done = serde_json::json!({
        "seq": 3,
        "type": "request",
        "command": "configurationDone",
    });
    framing_write(&mut sin, &cfg_done).unwrap();
    let _ = framing_read(&mut sout).unwrap();
    let ev = framing_read(&mut sout).unwrap().expect("stopped event");
    assert_eq!(ev.get("type").and_then(|t| t.as_str()), Some("event"));
    assert_eq!(ev.get("event").and_then(|t| t.as_str()), Some("stopped"));

    let disc = serde_json::json!({
        "seq": 4,
        "type": "request",
        "command": "disconnect",
    });
    framing_write(&mut sin, &disc).unwrap();
    let _ = child.wait();
}
