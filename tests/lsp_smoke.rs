//! Exercise `ur-lsp` over JSON-RPC so LSP handlers cannot be stubbed out silently.

use std::io::{Read, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use serde_json::{json, Value};

/// Wall-clock bound waiting for `textDocument/publishDiagnostics` (CI / loaded hosts).
const LSP_PUBLISH_DIAG_DEADLINE: Duration = Duration::from_secs(6);
const LSP_RECV_POLL: Duration = Duration::from_millis(200);

/// Bound for expecting a JSON-RPC reply when the client is otherwise idle (e.g. initialize).
/// Avoids blocking forever on `read_exact` when mutants stub `handle_request` / `dispatch_message`.
const LSP_RPC_DEADLINE: Duration = Duration::from_secs(5);

const SMOKE_DOC_URI: &str = "file:///tmp/ur-lsp-smoke.ur";

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

fn spawn_stdout_reader<R: Read + Send + 'static>(
    stdout: R,
) -> (thread::JoinHandle<()>, mpsc::Receiver<Vec<u8>>) {
    let (tx, rx) = mpsc::channel::<Vec<u8>>();
    let handle = thread::spawn(move || {
        let mut stdout = stdout;
        while let Some(body) = read_one_message(&mut stdout) {
            if tx.send(body).is_err() {
                break;
            }
        }
    });
    (handle, rx)
}

/// Next JSON-RPC object satisfying `pred`, or panic after `deadline`.
fn recv_jsonrpc_matching(
    rx: &mpsc::Receiver<Vec<u8>>,
    mut pred: impl FnMut(&Value) -> bool,
    deadline: Duration,
    label: &str,
) -> Vec<u8> {
    let end = Instant::now() + deadline;
    while Instant::now() < end {
        let wait = end
            .saturating_duration_since(Instant::now())
            .min(LSP_RECV_POLL);
        if wait.is_zero() {
            break;
        }
        match rx.recv_timeout(wait) {
            Ok(body) => {
                if let Ok(v) = serde_json::from_slice::<Value>(&body) {
                    if pred(&v) {
                        return body;
                    }
                }
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {}
            Err(mpsc::RecvTimeoutError::Disconnected) => break,
        }
    }
    panic!("timeout after {deadline:?} waiting for {label}");
}

/// `Some(diagnostics)` only when this JSON-RPC body is `publishDiagnostics` for `expected_uri`.
fn diagnostics_for_uri(body: &[u8], expected_uri: &str) -> Option<Vec<Value>> {
    let v: Value = serde_json::from_slice(body).ok()?;
    if v.get("method").and_then(|m| m.as_str()) != Some("textDocument/publishDiagnostics") {
        return None;
    }
    let params = v.get("params")?;
    let uri = params.get("uri").and_then(|u| u.as_str())?;
    if uri != expected_uri {
        return None;
    }
    params
        .get("diagnostics")
        .and_then(|d| d.as_array())
        .cloned()
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
    let stdout = child.stdout.take().expect("stdout");
    let (reader, rx) = spawn_stdout_reader(stdout);

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

    let body = recv_jsonrpc_matching(
        &rx,
        |v| v.get("id") == Some(&json!(1)) && v.get("result").is_some(),
        LSP_RPC_DEADLINE,
        "initialize response with id=1",
    );
    let msg: Value = serde_json::from_slice(&body).expect("parse json");
    let caps = msg
        .get("result")
        .and_then(|r| r.get("capabilities"))
        .expect("initialize result.capabilities");
    assert!(
        caps.get("textDocumentSync").is_some(),
        "capabilities must advertise text sync, got {caps:?}"
    );
    assert!(
        caps.get("hoverProvider").is_some(),
        "capabilities should advertise hover, got {caps:?}"
    );
    assert!(
        caps.get("definitionProvider").is_some(),
        "capabilities should advertise definition, got {caps:?}"
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
                    "uri": SMOKE_DOC_URI,
                    "languageId": "ur",
                    "version": 1,
                    "text": "fun main () = )))\n"
                }
            }
        }),
    );

    let deadline = Instant::now() + LSP_PUBLISH_DIAG_DEADLINE;
    let mut saw_diagnostic = false;
    while Instant::now() < deadline && !saw_diagnostic {
        let wait = deadline.saturating_duration_since(Instant::now());
        if wait.is_zero() {
            break;
        }
        match rx.recv_timeout(wait.min(LSP_RECV_POLL)) {
            Ok(body) => {
                let diags = match diagnostics_for_uri(&body, SMOKE_DOC_URI) {
                    Some(d) => d,
                    None => continue,
                };
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
fn ur_lsp_did_change_replaces_text_and_clears_diagnostics() {
    let mut child = Command::new(cargo_bin("ur-lsp"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ur-lsp");

    let mut stdin = child.stdin.take().expect("stdin");
    let stdout = child.stdout.take().expect("stdout");
    let (reader, rx) = spawn_stdout_reader(stdout);

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
    recv_jsonrpc_matching(
        &rx,
        |v| v.get("id") == Some(&json!(1)) && v.get("result").is_some(),
        LSP_RPC_DEADLINE,
        "initialize response with id=1",
    );

    write_msg(
        &mut stdin,
        &json!({
            "jsonrpc": "2.0",
            "method": "initialized",
            "params": {}
        }),
    );

    let uri = "file:///tmp/ur-lsp-change.ur";
    write_msg(
        &mut stdin,
        &json!({
            "jsonrpc": "2.0",
            "method": "textDocument/didOpen",
            "params": {
                "textDocument": {
                    "uri": uri,
                    "languageId": "ur",
                    "version": 1,
                    "text": "fun main () = )))\n"
                }
            }
        }),
    );

    let deadline = Instant::now() + LSP_PUBLISH_DIAG_DEADLINE;
    let mut saw_bad = false;
    while Instant::now() < deadline && !saw_bad {
        let wait = deadline.saturating_duration_since(Instant::now());
        if wait.is_zero() {
            break;
        }
        match rx.recv_timeout(wait.min(LSP_RECV_POLL)) {
            Ok(body) => {
                let diags = match diagnostics_for_uri(&body, uri) {
                    Some(d) => d,
                    None => continue,
                };
                if !diags.is_empty() {
                    saw_bad = true;
                    break;
                }
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {}
            Err(mpsc::RecvTimeoutError::Disconnected) => break,
        }
    }
    assert!(saw_bad, "expected diagnostics for invalid Ur after didOpen");

    write_msg(
        &mut stdin,
        &json!({
            "jsonrpc": "2.0",
            "method": "textDocument/didChange",
            "params": {
                "textDocument": {"uri": uri, "version": 2},
                "contentChanges": [{"text": "val x = 1\n"}]
            }
        }),
    );

    let deadline2 = Instant::now() + LSP_PUBLISH_DIAG_DEADLINE;
    let mut saw_clear = false;
    while Instant::now() < deadline2 && !saw_clear {
        let wait = deadline2.saturating_duration_since(Instant::now());
        if wait.is_zero() {
            break;
        }
        match rx.recv_timeout(wait.min(LSP_RECV_POLL)) {
            Ok(body) => {
                let diags = match diagnostics_for_uri(&body, uri) {
                    Some(d) => d,
                    None => continue,
                };
                if diags.is_empty() {
                    saw_clear = true;
                    break;
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
        saw_clear,
        "didChange should re-parse and publish empty diagnostics for valid source (catches delete DidChange arm)"
    );
}

#[test]
fn ur_lsp_unknown_method_returns_method_not_found() {
    let mut child = Command::new(cargo_bin("ur-lsp"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ur-lsp");

    let mut stdin = child.stdin.take().expect("stdin");
    let stdout = child.stdout.take().expect("stdout");
    let (reader, rx) = spawn_stdout_reader(stdout);

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
    recv_jsonrpc_matching(
        &rx,
        |v| v.get("id") == Some(&json!(1)) && v.get("result").is_some(),
        LSP_RPC_DEADLINE,
        "initialize response with id=1",
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
            "id": 42,
            "method": "textDocument/noSuchMethod",
            "params": {
                "textDocument": {"uri": SMOKE_DOC_URI},
                "position": {"line": 0, "character": 0}
            }
        }),
    );

    let body = recv_jsonrpc_matching(
        &rx,
        |v| v.get("id") == Some(&json!(42)) && v.get("error").is_some(),
        LSP_RPC_DEADLINE,
        "JSON-RPC error for unknown method (id=42)",
    );
    let msg: Value = serde_json::from_slice(&body).expect("parse json");
    assert_eq!(msg.get("id"), Some(&json!(42)));
    let err = msg.get("error").expect("JSON-RPC error object");
    assert_eq!(
        err.get("code").and_then(|c| c.as_i64()),
        Some(-32601),
        "unsupported methods must use Method not found (-32601), got {msg:?}"
    );

    let _ = child.kill();
    let _ = child.wait();
    drop(rx);
    let _ = reader.join();
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

/// Keys that `cargo mutants` used to kill via delete-field mutants on [`ServerCapabilities`] in `ur-lsp`.
fn assert_capabilities_cover_server_surface(capabilities: &Value) {
    for key in [
        "textDocumentSync",
        "hoverProvider",
        "definitionProvider",
        "typeDefinitionProvider",
        "referencesProvider",
        "documentHighlightProvider",
        "workspaceSymbolProvider",
        "documentSymbolProvider",
        "completionProvider",
        "signatureHelpProvider",
        "renameProvider",
        "foldingRangeProvider",
        "selectionRangeProvider",
        "inlayHintProvider",
        "semanticTokensProvider",
        "documentFormattingProvider",
    ] {
        assert!(
            capabilities.get(key).is_some(),
            "initialize must advertise {key}, got {capabilities:?}"
        );
    }
}

#[test]
fn ur_lsp_initialize_advertises_full_capabilities() {
    let mut child = Command::new(cargo_bin("ur-lsp"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ur-lsp");

    let mut stdin = child.stdin.take().expect("stdin");
    let stdout = child.stdout.take().expect("stdout");
    let (reader, rx) = spawn_stdout_reader(stdout);

    write_msg(
        &mut stdin,
        &json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": {
                "processId": null,
                "capabilities": {},
                "clientInfo": {"name": "ur-lsp-cap-test", "version": "0"}
            }
        }),
    );

    let body = recv_jsonrpc_matching(
        &rx,
        |v| v.get("id") == Some(&json!(1)) && v.get("result").is_some(),
        LSP_RPC_DEADLINE,
        "initialize id=1",
    );
    let msg: Value = serde_json::from_slice(&body).expect("json");
    let caps = msg
        .get("result")
        .and_then(|r| r.get("capabilities"))
        .expect("capabilities");
    assert_capabilities_cover_server_surface(caps);

    let _ = child.kill();
    let _ = child.wait();
    drop(rx);
    let _ = reader.join();
}

#[test]
fn ur_lsp_formatting_returns_empty_when_buffer_already_canonical() {
    let fmt_uri = "file:///tmp/ur-lsp-fmt-nodup.ur";
    let buffer = "val x = 1\n";
    let mut child = Command::new(cargo_bin("ur-lsp"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ur-lsp");
    let mut stdin = child.stdin.take().expect("stdin");
    let stdout = child.stdout.take().expect("stdout");
    let (reader, rx) = spawn_stdout_reader(stdout);

    write_msg(
        &mut stdin,
        &json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": {
                "processId": null,
                "capabilities": {},
                "clientInfo": {"name": "ur-lsp-fmt", "version": "0"}
            }
        }),
    );
    recv_jsonrpc_matching(
        &rx,
        |v| v.get("id") == Some(&json!(1)) && v.get("result").is_some(),
        LSP_RPC_DEADLINE,
        "initialize",
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
                    "uri": fmt_uri,
                    "languageId": "ur",
                    "version": 1,
                    "text": buffer
                }
            }
        }),
    );
    write_msg(
        &mut stdin,
        &json!({
            "jsonrpc": "2.0",
            "id": 99,
            "method": "textDocument/formatting",
            "params": {
                "textDocument": {"uri": fmt_uri},
                "options": {"tabSize": 4, "insertSpaces": true}
            }
        }),
    );
    let body = recv_jsonrpc_matching(
        &rx,
        |v| v.get("id") == Some(&json!(99)) && v.get("result").is_some(),
        LSP_RPC_DEADLINE,
        "formatting response",
    );
    let msg: Value = serde_json::from_slice(&body).expect("json");
    let result = msg.get("result").expect("result");
    assert_eq!(
        result,
        &json!([]),
        "canonical buffer must yield empty edits (fmt == doc.text guard), got {result:?}"
    );

    let _ = child.kill();
    let _ = child.wait();
    drop(rx);
    let _ = reader.join();
}
