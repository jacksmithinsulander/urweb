//! ur-lsp — LSP server for Ur/Web.
//!
//! Connects over stdio, handles textDocument sync, and reports parse
//! errors as diagnostics.

use std::collections::HashMap;

use anyhow::Result;
use lsp_server::{Connection, Message, Response};
use lsp_types::{
    notification::{DidChangeTextDocument, DidOpenTextDocument, Notification as _},
    Diagnostic, DiagnosticSeverity, DidChangeTextDocumentParams, DidOpenTextDocumentParams,
    Position, PublishDiagnosticsParams, Range, ServerCapabilities, ServerInfo,
    TextDocumentSyncCapability, TextDocumentSyncKind, Uri,
};

fn main() {
    if let Err(e) = run() {
        // Disconnection from the editor is a normal termination (not an error).
        let msg = e.to_string();
        if msg.contains("disconnected") || msg.contains("channel") || msg.contains("io error") {
            std::process::exit(0);
        }
        eprintln!("ur-lsp error: {e}");
        std::process::exit(1);
    }
}

fn run() -> Result<()> {
    let (connection, io_threads) = Connection::stdio();

    // Build server capabilities
    let capabilities = ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
        ..Default::default()
    };

    let init_result = lsp_types::InitializeResult {
        capabilities,
        server_info: Some(ServerInfo {
            name: "ur-lsp".into(),
            version: Some(env!("CARGO_PKG_VERSION").into()),
        }),
    };

    let (req_id, _init_params) = match connection.initialize_start() {
        Ok(v) => v,
        // Stdin closed before initialize — clean exit.
        Err(_) => return Ok(()),
    };
    connection.initialize_finish(req_id, serde_json::to_value(&init_result)?)?;

    // Document store: URI → content
    let mut docs: HashMap<Uri, String> = HashMap::new();

    // Main message loop
    for msg in &connection.receiver {
        match msg {
            Message::Request(req) => {
                // Handle shutdown
                if connection.handle_shutdown(&req)? {
                    break;
                }
                // Unknown requests: respond with null result
                let resp = Response {
                    id: req.id,
                    result: Some(serde_json::Value::Null),
                    error: None,
                };
                connection.sender.send(Message::Response(resp))?;
            }
            Message::Notification(notif) => {
                match notif.method.as_str() {
                    DidOpenTextDocument::METHOD => {
                        if let Ok(p) = serde_json::from_value::<DidOpenTextDocumentParams>(
                            notif.params.clone(),
                        ) {
                            let uri = p.text_document.uri;
                            let text = p.text_document.text;
                            docs.insert(uri.clone(), text.clone());
                            publish_diagnostics(&connection, &uri, &text)?;
                        }
                    }
                    DidChangeTextDocument::METHOD => {
                        if let Ok(p) = serde_json::from_value::<DidChangeTextDocumentParams>(
                            notif.params.clone(),
                        ) {
                            if let Some(change) = p.content_changes.into_iter().next() {
                                let uri = p.text_document.uri;
                                let text = change.text;
                                docs.insert(uri.clone(), text.clone());
                                publish_diagnostics(&connection, &uri, &text)?;
                            }
                        }
                    }
                    // initialized notification — no-op
                    "initialized" => {}
                    _ => {}
                }
            }
            Message::Response(_) => {}
        }
    }

    let _ = io_threads.join();
    Ok(())
}

/// Parse `text` as an Ur/Web source file and publish any parse errors as
/// LSP diagnostics for `uri`.
fn publish_diagnostics(connection: &Connection, uri: &Uri, text: &str) -> Result<()> {
    let file_name = uri.as_str();
    let mut errors = ur::error_types::ErrorReporter::new();

    // Parse the document — this records parse errors into `errors`.
    let _ = ur::parse::parse_ur(file_name, text, &mut errors);

    let diagnostics: Vec<Diagnostic> = errors
        .errors
        .iter()
        .map(|e| error_to_diagnostic(e))
        .collect();

    let params = PublishDiagnosticsParams {
        uri: uri.clone(),
        diagnostics,
        version: None,
    };

    connection
        .sender
        .send(Message::Notification(lsp_server::Notification::new(
            lsp_types::notification::PublishDiagnostics::METHOD.to_owned(),
            params,
        )))?;

    Ok(())
}

/// Convert a `CompileError` to an LSP `Diagnostic`.
fn error_to_diagnostic(e: &ur::error_types::CompileError) -> Diagnostic {
    let range = match e.span() {
        Some(span) => {
            // LSP lines/cols are 0-based
            let start_line = span.first.line.saturating_sub(1);
            let start_col = span.first.col;
            let end_line = span.last.line.saturating_sub(1);
            let end_col = span.last.col;
            Range::new(
                Position::new(start_line, start_col),
                Position::new(end_line, end_col),
            )
        }
        None => Range::new(Position::new(0, 0), Position::new(0, 0)),
    };

    Diagnostic {
        range,
        severity: Some(DiagnosticSeverity::ERROR),
        code: None,
        code_description: None,
        source: Some("ur-lsp".into()),
        message: e.to_string(),
        related_information: None,
        tags: None,
        data: None,
    }
}
