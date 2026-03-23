//! Exercise `ur-lsp` over JSON-RPC so LSP handlers cannot be stubbed out silently.

use std::io::{Read, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use serde_json::{json, Value};

fn cargo_bin(name: &str) -> PathBuf {
    let underscored = name.replace('-', "_");
    let key = format!("CARGO_BIN_EXE_{underscored}");
    if let Some(p) = std::env::var_os(&key) {
        return PathBuf::from(p);
    }
    let profile = std::env::var("PROFILE").unwrap_or_else(|_| "debug".into());
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join(&profile)
        .join(name);
    assert!(
        path.exists(),
        "missing binary {name}: set {key} or build with cargo test — looked for {:?}",
        path
    );
    path
}

fn write_msg(stdin: &mut impl Write, body: &Value) {
    let payload = serde_json::to_vec(body).expect("serialize json");
    let header = format!("Content-Length: {}\r\n\r\n", payload.len());
    stdin.write_all(header.as_bytes()).expect("write header");
    stdin.write_all(&payload).expect("write body");
    stdin.flush().expect("flush");
}

fn read_one_message<R: Read>(reader: &mut R) -> Option<Vec<u8>> {
    let mut header_buf: Vec<u8> = Vec::new();
    let mut byte = [0u8; 1];
    loop {
        reader.read_exact(&mut byte).ok()?;
        header_buf.push(byte[0]);
        if header_buf.len() >= 4 && &header_buf[header_buf.len() - 4..] == b"\r\n\r\n" {
            break;
        }
        if header_buf.len() > 262_144 {
            return None;
        }
    }
    let header = std::str::from_utf8(&header_buf).ok()?;
    let mut content_len: Option<usize> = None;
    for line in header.lines() {
        if let Some(rest) = line.strip_prefix("Content-Length:") {
            content_len = rest.trim().parse().ok();
        }
    }
    let n = content_len?;
    let mut body = vec![0u8; n];
    reader.read_exact(&mut body).ok()?;
    Some(body)
}

#[test]
fn ur_lsp_initialize_reports_text_document_sync() {
    let mut child = Command::new(cargo_bin("ur-lsp"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ur-lsp");

    let mut stdin = child.stdin.take().expect("stdin");
    let mut stdout = child.stdout.take().expect("stdout");

    write_msg(
        &mut stdin,
        &json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": {
                "processId": null,
                "capabilities": {},
                "clientInfo": {"name": "ur-lsp-test", "version": "0"}
            }
        }),
    );

    let body = read_one_message(&mut stdout).expect("initialize response");
    let msg: Value = serde_json::from_slice(&body).expect("parse json");
    let caps = msg
        .get("result")
        .and_then(|r| r.get("capabilities"))
        .expect("initialize result.capabilities");
    assert!(
        caps.get("textDocumentSync").is_some(),
        "capabilities must advertise text sync, got {caps:?}"
    );

    write_msg(
        &mut stdin,
        &json!({
            "jsonrpc": "2.0",
            "method": "initialized",
            "params": {}
        }),
    );

    write_msg(
        &mut stdin,
        &json!({
            "jsonrpc": "2.0",
            "method": "textDocument/didOpen",
            "params": {
                "textDocument": {
                    "uri": "file:///tmp/ur-lsp-smoke.ur",
                    "languageId": "ur",
                    "version": 1,
                    "text": "fun main () = )))\n"
                }
            }
        }),
    );

    let (tx, rx) = mpsc::channel::<Vec<u8>>();
    let reader = thread::spawn(move || {
        let mut stdout = stdout;
        while let Some(body) = read_one_message(&mut stdout) {
            if tx.send(body).is_err() {
                break;
            }
        }
    });

    let deadline = Instant::now() + Duration::from_secs(5);
    let mut saw_diagnostic = false;
    while Instant::now() < deadline && !saw_diagnostic {
        let wait = deadline.saturating_duration_since(Instant::now());
        if wait.is_zero() {
            break;
        }
        match rx.recv_timeout(wait.min(Duration::from_millis(200))) {
            Ok(body) => {
                let v: Value = match serde_json::from_slice(&body) {
                    Ok(x) => x,
                    Err(_) => continue,
                };
                if v.get("method").and_then(|m| m.as_str())
                    == Some("textDocument/publishDiagnostics")
                {
                    let diags = v
                        .get("params")
                        .and_then(|p| p.get("diagnostics"))
                        .and_then(|d| d.as_array())
                        .cloned()
                        .unwrap_or_default();
                    if !diags.is_empty() {
                        let dmsg = diags[0]
                            .get("message")
                            .and_then(|m| m.as_str())
                            .unwrap_or("");
                        assert!(
                            !dmsg.is_empty(),
                            "diagnostic should carry parse error text, got {diags:?}"
                        );
                        saw_diagnostic = true;
                        break;
                    }
                }
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {}
            Err(mpsc::RecvTimeoutError::Disconnected) => break,
        }
    }

    let _ = child.kill();
    let _ = child.wait();
    drop(rx);
    let _ = reader.join();

    assert!(
        saw_diagnostic,
        "expected non-empty publishDiagnostics for invalid Ur source"
    );
}

#[test]
fn ur_lsp_closing_stdin_exits_successfully() {
    let mut child = Command::new(cargo_bin("ur-lsp"))
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ur-lsp");
    drop(child.stdin.take());
    let out = child.wait_with_output().expect("wait");
    assert!(
        out.status.success(),
        "clean disconnect should exit 0, stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );
}
