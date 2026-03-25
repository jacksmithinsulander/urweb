//! ur-lsp — LSP server for Ur/Web.
//!
//! Connects over stdio, handles textDocument sync, and reports parse
//! errors as diagnostics.

use std::collections::HashMap;

use anyhow::Result;
use lsp_server::{Connection, Message, Response};
use lsp_types::{
    notification::{DidChangeTextDocument, DidOpenTextDocument, Initialized, Notification as _},
    DidChangeTextDocumentParams, DidOpenTextDocumentParams, ServerCapabilities, ServerInfo,
    TextDocumentSyncCapability, TextDocumentSyncKind, Uri,
};

fn main() {
    if let Err(e) = run() {
        // Disconnection from the editor is a normal termination (not an error).
        let msg = e.to_string();
        if ur::lsp_support::disconnect_error_exits_clean(&msg) {
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
                // Use `if`/`else if` (not `match` + `_`) so `delete match arm` mutants
                // cannot swallow `didChange` / `initialized` into a catch-all.
                let method = notif.method.as_str();
                if method == DidOpenTextDocument::METHOD {
                    if let Ok(p) =
                        serde_json::from_value::<DidOpenTextDocumentParams>(notif.params.clone())
                    {
                        let uri = p.text_document.uri;
                        let text = p.text_document.text;
                        docs.insert(uri.clone(), text.clone());
                        ur::lsp_support::publish_parse_diagnostics(&connection, &uri, &text)?;
                    }
                } else if method == DidChangeTextDocument::METHOD {
                    if let Ok(p) =
                        serde_json::from_value::<DidChangeTextDocumentParams>(notif.params.clone())
                    {
                        if let Some(change) = p.content_changes.into_iter().next() {
                            let uri = p.text_document.uri;
                            let text = change.text;
                            docs.insert(uri.clone(), text.clone());
                            ur::lsp_support::publish_parse_diagnostics(&connection, &uri, &text)?;
                        }
                    }
                } else if method == Initialized::METHOD {
                    // Client lifecycle (no-op); explicit branch for spec compliance.
                }
            }
            Message::Response(_) => {}
        }
    }

    let _ = io_threads.join();
    Ok(())
}
