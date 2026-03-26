//! Language Server Protocol implementation for Ur/Web over standard input and output (JSON remote procedure calls).
//!
//! The workspace root must contain exactly one `.urp` Ur/Web project file, like the legacy Standard ML server.
//! [`std::env::set_current_dir`] switches to that root so paths in the project file match batch compilation.
//!
//! **Style:** this binary follows [README.md](../../README.md) Rust code style where edited.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::mpsc;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use anyhow::Result;
use crossbeam_channel::RecvTimeoutError;
use lsp_server::{Connection, ErrorCode, Message, Notification, Request as LspRequest, Response};
use lsp_types::notification::{
    DidChangeTextDocument, DidCloseTextDocument, DidOpenTextDocument, Initialized,
    Notification as _,
};
use lsp_types::request::{
    Completion, DocumentHighlightRequest, DocumentSymbolRequest, FoldingRangeRequest, Formatting,
    GotoDefinition, GotoTypeDefinition, InlayHintRequest, PrepareRenameRequest, References, Rename,
    Request, SelectionRangeRequest, SemanticTokensFullRequest, SignatureHelpRequest,
    WorkspaceSymbolRequest,
};
use lsp_types::{
    CompletionOptions, CompletionParams, CompletionResponse, DidChangeTextDocumentParams,
    DidCloseTextDocumentParams, DidOpenTextDocumentParams, DocumentFormattingParams,
    DocumentHighlight, DocumentHighlightKind, DocumentHighlightParams, DocumentSymbol,
    DocumentSymbolParams, DocumentSymbolResponse, FoldingRangeParams,
    FoldingRangeProviderCapability, GotoDefinitionParams, GotoDefinitionResponse, Hover,
    HoverContents, HoverParams, InitializeParams, InlayHintParams, Location, OneOf,
    PrepareRenameResponse, ReferenceParams, RenameOptions, RenameParams, SelectionRangeParams,
    SelectionRangeProviderCapability, SemanticTokens, SemanticTokensFullOptions,
    SemanticTokensLegend, SemanticTokensOptions, SemanticTokensParams,
    SemanticTokensServerCapabilities, ServerCapabilities, ServerInfo, SignatureHelp,
    SignatureHelpOptions, SignatureHelpParams, SignatureInformation, SymbolInformation, SymbolKind,
    TextDocumentPositionParams, TextDocumentSyncCapability, TextDocumentSyncKind, TextEdit,
    TypeDefinitionProviderCapability, Uri, WorkDoneProgressOptions, WorkspaceSymbolParams,
};

use ur::lsp_analysis::{AnalysisSnapshot, ProjectState};
use ur::lsp_semantics;
use ur::lsp_workspace::{
    relative_file_key_for_uri, uri_local_path_for_tooling, uri_to_file_path,
    workspace_root_from_initialize,
};

/// Run the server loop; exit with status zero when the editor disconnects cleanly.
///
/// Delegates to [`run`] and treats transport teardown as success when [`ur::lsp_support::disconnect_error_exits_clean`] matches.
///
/// # Returns
///
/// Does not return: calls [`std::process::exit`] with `0` or `1`.
fn main() {
    if let Err(e) = run() {
        let msg = e.to_string();
        if ur::lsp_support::disconnect_error_exits_clean(&msg) {
            std::process::exit(0);
        }
        eprintln!("ur-lsp error: {e}");
        std::process::exit(1);
    }
}

/// Open buffer text and a generation stamp so stale background work is discarded.
struct DocState {
    text: String,
    /// Bumped on each change; must match a finished job for its diagnostics to apply.
    analysis_gen: u64,
}

/// Result from a background analysis thread: document, generation stamp, and snapshot.
struct AnalysisReady {
    uri: Uri,
    gen: u64,
    snap: AnalysisSnapshot,
}

/// Shared session state for one server run (behind a mutex inside an [`Arc`]).
struct Global {
    workspace_root: Option<PathBuf>,
    project: Option<ProjectState>,
    docs: HashMap<Uri, DocState>,
    /// Last elaboration snapshot per uniform resource identifier (for hover and similar) when the latest run still had errors.
    last_snap: HashMap<Uri, AnalysisSnapshot>,
}

type GlobalRef = Arc<Mutex<Global>>;

/// Main server loop: initialize, advertise capabilities, then poll JSON messages from the client.
///
/// Uses a bounded receive timeout so [`AnalysisReady`] work is merged without blocking forever on idle standard input.
///
/// # Returns
///
/// `Ok(())` after the inbound channel disconnects or initialize fails early; `Err` on I/O/serialization failures in the loop body.
///
/// # Errors
///
/// Initialization finish, JSON serialization, message handling, or diagnostic publish failures propagate as [`anyhow::Error`].
fn run() -> Result<()> {
    let (connection, io_threads) = Connection::stdio();

    let (req_id, init_value) = match connection.initialize_start() {
        Ok(v) => v,
        Err(_) => return Ok(()),
    };
    let init_params: InitializeParams =
        serde_json::from_value(init_value).unwrap_or_else(|_| InitializeParams::default());

    let workspace_root = workspace_root_from_initialize(&init_params);
    let project = workspace_root
        .as_ref()
        .and_then(|r| match ProjectState::open(r) {
            Ok(p) => Some(p),
            Err(e) => {
                eprintln!("ur-lsp: project load: {e}");
                None
            }
        });

    if let Some(ref root) = workspace_root {
        if let Err(e) = std::env::set_current_dir(root) {
            eprintln!("ur-lsp: set_current_dir({}): {e}", root.display());
        }
    }

    let capabilities = ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
        hover_provider: Some(true.into()),
        definition_provider: Some(OneOf::Left(true)),
        type_definition_provider: Some(TypeDefinitionProviderCapability::Simple(true)),
        references_provider: Some(OneOf::Left(true)),
        document_highlight_provider: Some(OneOf::Left(true)),
        workspace_symbol_provider: Some(OneOf::Left(true)),
        document_symbol_provider: Some(OneOf::Left(true)),
        completion_provider: Some(CompletionOptions {
            resolve_provider: Some(false),
            trigger_characters: Some(vec![".".into()]),
            all_commit_characters: None,
            completion_item: None,
            work_done_progress_options: WorkDoneProgressOptions::default(),
        }),
        signature_help_provider: Some(SignatureHelpOptions {
            work_done_progress_options: WorkDoneProgressOptions::default(),
            trigger_characters: Some(vec!["(".into(), ",".into()]),
            retrigger_characters: None,
        }),
        rename_provider: Some(OneOf::Right(RenameOptions {
            prepare_provider: Some(true),
            work_done_progress_options: WorkDoneProgressOptions::default(),
        })),
        folding_range_provider: Some(FoldingRangeProviderCapability::Simple(true)),
        selection_range_provider: Some(SelectionRangeProviderCapability::Simple(true)),
        inlay_hint_provider: Some(OneOf::Left(true)),
        semantic_tokens_provider: Some(SemanticTokensServerCapabilities::SemanticTokensOptions(
            SemanticTokensOptions {
                work_done_progress_options: WorkDoneProgressOptions::default(),
                legend: SemanticTokensLegend {
                    token_types: ur::lsp_semantics::SEMANTIC_TOKEN_TYPES.to_vec(),
                    token_modifiers: vec![],
                },
                range: Some(false),
                full: Some(SemanticTokensFullOptions::Bool(true)),
            },
        )),
        document_formatting_provider: Some(OneOf::Left(true)),
        ..Default::default()
    };

    let init_result = lsp_types::InitializeResult {
        capabilities,
        server_info: Some(ServerInfo {
            name: "ur-lsp".into(),
            version: Some(env!("CARGO_PKG_VERSION").into()),
        }),
    };
    connection.initialize_finish(req_id, serde_json::to_value(&init_result)?)?;

    let global = Arc::new(Mutex::new(Global {
        workspace_root,
        project,
        docs: HashMap::new(),
        last_snap: HashMap::new(),
    }));

    let (analysis_tx, analysis_rx) = mpsc::channel::<AnalysisReady>();

    const POLL: Duration = Duration::from_millis(50);

    loop {
        match connection.receiver.recv_timeout(POLL) {
            Ok(msg) => {
                dispatch_message(&connection, msg, &global, &analysis_tx)?;
            }
            Err(RecvTimeoutError::Timeout) => {
                drain_analysis(&connection, &global, &analysis_rx)?;
            }
            Err(RecvTimeoutError::Disconnected) => break,
        }
        // Also drain after each message
        drain_analysis(&connection, &global, &analysis_rx)?;
    }

    let _ = io_threads.join();
    Ok(())
}

/// Take finished analyses from the channel and publish diagnostics when the buffer generation still matches.
///
/// Drops stale [`AnalysisReady`] values if the user edited the buffer (analysis generation advanced).
///
/// # Arguments
///
/// * `connection` — Active server connection for outbound notifications.
/// * `global` — Mutex-protected session state.
/// * `rx` — Bounded channel of completed analysis jobs.
///
/// # Returns
///
/// `Ok(())` when all pending items are processed for this call.
///
/// # Errors
///
/// If [`ur::lsp_support::publish_diagnostics`] cannot send on the connection.
fn drain_analysis(
    connection: &Connection,
    global: &GlobalRef,
    rx: &mpsc::Receiver<AnalysisReady>,
) -> Result<()> {
    while let Ok(ready) = rx.try_recv() {
        let mut g = global.lock().unwrap();
        let skip = g
            .docs
            .get(&ready.uri)
            .map(|d| d.analysis_gen != ready.gen)
            .unwrap_or(true);
        if skip {
            continue;
        }
        g.last_snap.insert(ready.uri.clone(), ready.snap);
        let uri = &ready.uri;
        if let Some(snap) = g.last_snap.get(uri) {
            ur::lsp_support::publish_diagnostics(connection, uri, &snap.errors)?;
        }
    }
    Ok(())
}

/// Schedule parsing or full-project analysis for `text` at `uri`, stamped with `gen` for staleness checks.
///
/// Without a [`ProjectState`], only [`ur::parse::parse_ur`] runs. With a project, a background thread sleeps briefly to coalesce edits,
/// then calls [`ProjectState::analyze_buffer`].
///
/// # Arguments
///
/// * `global` — Read-locks to clone project state or choose parse-only mode.
/// * `analysis_tx` — Sender for [`AnalysisReady`] results.
/// * `uri` — Document identifier.
/// * `text` — Current buffer text.
/// * `gen` — Monotonic generation; must match the open document’s `analysis_gen` for results to apply.
///
/// # Returns
///
/// Nothing; sends zero or one message on `analysis_tx` (or spawns a thread that sends).
fn schedule_analysis(
    global: &GlobalRef,
    analysis_tx: &mpsc::Sender<AnalysisReady>,
    uri: Uri,
    text: String,
    gen: u64,
) {
    let g = global.lock().unwrap();
    let Some(proj) = g.project.as_ref() else {
        let mut err = ur::error_types::ErrorReporter::new_silent();
        let file_label =
            uri_local_path_for_tooling(&uri).unwrap_or_else(|| uri.as_str().to_string());
        let _ = ur::parse::parse_ur(&file_label, &text, &mut err, ur::db::ProjectDb::default());
        let snap = AnalysisSnapshot {
            errors: err,
            elaborated: None,
        };
        let u = uri.clone();
        drop(g);
        let _ = analysis_tx.send(AnalysisReady { uri: u, gen, snap });
        return;
    };
    let Some(disk) = uri_to_file_path(&uri) else {
        return;
    };
    let proj = ProjectState {
        root: proj.root.clone(),
        urp_path: proj.urp_path.clone(),
        job: proj.job.clone(),
        settings: proj.settings.clone(),
    };
    drop(g);

    let tx = analysis_tx.clone();
    let u = uri.clone();
    std::thread::spawn(move || {
        std::thread::sleep(Duration::from_millis(220));
        let snap = proj.analyze_buffer(&disk, &text);
        let _ = tx.send(AnalysisReady { uri: u, gen, snap });
    });
}

/// Demultiplex one wire message into requests, notifications, or ignored responses.
///
/// Shutdown is handled inside `lsp_server`; every other request goes to [`handle_request`].
///
/// # Arguments
///
/// * `connection` — Active connection.
/// * `msg` — One decoded [`Message`].
/// * `global` — Shared session state.
/// * `analysis_tx` — Channel passed to handlers that schedule work.
///
/// # Returns
///
/// `Ok(())` after the message is handled.
///
/// # Errors
///
/// Shutdown handling, [`handle_request`], or [`handle_notification`] failures.
fn dispatch_message(
    connection: &Connection,
    msg: Message,
    global: &GlobalRef,
    analysis_tx: &mpsc::Sender<AnalysisReady>,
) -> Result<()> {
    match msg {
        Message::Request(req) => {
            if connection.handle_shutdown(&req)? {
                return Ok(());
            }
            handle_request(connection, req, global, analysis_tx)?;
        }
        Message::Notification(notif) => {
            handle_notification(connection, notif, global, analysis_tx)?;
        }
        Message::Response(_) => {}
    }
    Ok(())
}

/// Handle editor notifications: open, change, close, initialized, and related methods.
///
/// Updates open documents, calls [`schedule_analysis`], and may invoke [`ur::lsp_support::publish_parse_diagnostics`] for quick parse-only feedback.
///
/// # Arguments
///
/// * `connection` — For outbound diagnostics when needed.
/// * `notif` — One notification with JSON `params`.
/// * `global` — Session state to mutate.
/// * `analysis_tx` — Analysis scheduling channel.
///
/// # Returns
///
/// `Ok(())` when the notification is recognized or ignored safely.
///
/// # Errors
///
/// JSON parse failures, diagnostic publish failures, or inner request helpers.
fn handle_notification(
    connection: &Connection,
    notif: Notification,
    global: &GlobalRef,
    analysis_tx: &mpsc::Sender<AnalysisReady>,
) -> Result<()> {
    let method = notif.method.as_str();
    if method == DidOpenTextDocument::METHOD {
        if let Ok(p) = serde_json::from_value::<DidOpenTextDocumentParams>(notif.params.clone()) {
            let uri = p.text_document.uri;
            let text = p.text_document.text;
            let mut g = global.lock().unwrap();
            let gen = ur::lsp_support::next_buffer_analysis_generation(None);
            g.docs.insert(
                uri.clone(),
                DocState {
                    text: text.clone(),
                    analysis_gen: gen,
                },
            );
            drop(g);
            schedule_analysis(global, analysis_tx, uri.clone(), text.clone(), gen);
        }
    } else if method == DidChangeTextDocument::METHOD {
        if let Ok(p) = serde_json::from_value::<DidChangeTextDocumentParams>(notif.params.clone()) {
            if let Some(ch) = p.content_changes.into_iter().next() {
                let uri = p.text_document.uri;
                let text = ch.text;
                let mut g = global.lock().unwrap();
                let gen = ur::lsp_support::next_buffer_analysis_generation(
                    g.docs.get(&uri).map(|document| document.analysis_gen),
                );
                g.docs.insert(
                    uri.clone(),
                    DocState {
                        text: text.clone(),
                        analysis_gen: gen,
                    },
                );
                drop(g);
                schedule_analysis(global, analysis_tx, uri.clone(), text, gen);
            }
        }
    } else if method == DidCloseTextDocument::METHOD {
        if let Ok(p) = serde_json::from_value::<DidCloseTextDocumentParams>(notif.params.clone()) {
            let uri = p.text_document.uri;
            let mut g = global.lock().unwrap();
            g.docs.remove(&uri);
            g.last_snap.remove(&uri);
            ur::lsp_support::publish_diagnostics(
                connection,
                &uri,
                &ur::error_types::ErrorReporter::new_silent(),
            )?;
        }
    } else if method == Initialized::METHOD {
    }
    Ok(())
}

/// Workspace-relative `/` path for `uri`, or `None` if there is no root or not a `file:` location.
///
/// # Arguments
///
/// * `g` — Session state (needs `workspace_root`).
/// * `uri` — Document uniform resource identifier.
///
/// # Returns
///
/// String key suitable for [`ur::lsp_workspace::file_key_relative_to_root`], or `None`.
fn file_key(g: &Global, uri: &Uri) -> Option<String> {
    relative_file_key_for_uri(g.workspace_root.as_deref(), uri)
}

/// Answer a single Language Server Protocol request (hover, goto, formatting, …) and send the JSON response.
///
/// # Arguments
///
/// * `connection` — For sending [`Response`] values.
/// * `req` — Incoming request with method name and JSON params.
/// * `global` — Read-locks for documents and last analysis snapshot.
/// * `_analysis_tx` — Reserved for handlers that might schedule work (currently unused in some code paths).
///
/// # Returns
///
/// `Ok(())` after a response is sent or the method is ignored.
///
/// # Errors
///
/// JSON deserialization failures or outbound send errors.
fn handle_request(
    connection: &Connection,
    req: LspRequest,
    global: &GlobalRef,
    _analysis_tx: &mpsc::Sender<AnalysisReady>,
) -> Result<()> {
    let id = req.id.clone();
    let method = req.method.as_str();

    if method == "textDocument/hover" {
        let params: HoverParams = serde_json::from_value(req.params.clone())?;
        let g = global.lock().unwrap();
        let uri = &params.text_document_position_params.text_document.uri;
        let doc = g.docs.get(uri);
        let fk = file_key(&g, uri);
        let elab = g.last_snap.get(uri).and_then(|s| s.elaborated.as_ref());
        let text = doc.map(|d| d.text.as_str()).unwrap_or("");
        let pos = &params.text_document_position_params.position;
        let hover = fk.as_ref().and_then(|fk| {
            lsp_semantics::hover_markdown(elab, fk, text, pos.line, pos.character).map(|c| Hover {
                contents: HoverContents::Markup(c.into_lsp_markup()),
                range: None,
            })
        });
        connection
            .sender
            .send(Response::new_ok(id, serde_json::to_value(hover)?).into())?;
        return Ok(());
    }

    if method == GotoDefinition::METHOD {
        let params: GotoDefinitionParams = serde_json::from_value(req.params.clone())?;
        let g = global.lock().unwrap();
        let uri = &params.text_document_position_params.text_document.uri;
        let doc = g.docs.get(uri);
        let fk = file_key(&g, uri);
        let elab = g.last_snap.get(uri).and_then(|s| s.elaborated.as_ref());
        let text = doc.map(|d| d.text.as_str()).unwrap_or("");
        let pos = &params.text_document_position_params.position;
        let loc = fk.and_then(|fk| {
            lsp_semantics::goto_definition(elab, &fk, uri.as_str(), text, pos.line, pos.character)
        });
        let out: Option<GotoDefinitionResponse> =
            loc.and_then(|s| s.try_lsp_location().map(GotoDefinitionResponse::Scalar));
        connection
            .sender
            .send(Response::new_ok(id, serde_json::to_value(out)?).into())?;
        return Ok(());
    }

    if method == GotoTypeDefinition::METHOD {
        let _params: GotoDefinitionParams = serde_json::from_value(req.params.clone())?;
        connection
            .sender
            .send(Response::new_ok(id, serde_json::Value::Null).into())?;
        return Ok(());
    }

    if method == Completion::METHOD {
        let params: CompletionParams = serde_json::from_value(req.params.clone())?;
        let g = global.lock().unwrap();
        let uri = &params.text_document_position.text_document.uri;
        let doc = g.docs.get(uri);
        let fk = file_key(&g, uri);
        let elab = g.last_snap.get(uri).and_then(|s| s.elaborated.as_ref());
        let text = doc.map(|d| d.text.as_str()).unwrap_or("");
        let pos = &params.text_document_position.position;
        let comp = fk
            .map(|fk| {
                CompletionResponse::Array(lsp_semantics::completion_at_point(
                    elab,
                    &fk,
                    text,
                    pos.line,
                    pos.character,
                ))
            })
            .unwrap_or_else(|| CompletionResponse::Array(vec![]));
        connection
            .sender
            .send(Response::new_ok(id, serde_json::to_value(comp)?).into())?;
        return Ok(());
    }

    if method == SignatureHelpRequest::METHOD {
        let params: SignatureHelpParams = serde_json::from_value(req.params.clone())?;
        let g = global.lock().unwrap();
        let uri = &params.text_document_position_params.text_document.uri;
        let doc = g.docs.get(uri);
        let fk = file_key(&g, uri);
        let elab = g.last_snap.get(uri).and_then(|s| s.elaborated.as_ref());
        let text = doc.map(|d| d.text.as_str()).unwrap_or("");
        let pos = &params.text_document_position_params.position;
        let sh = fk.and_then(|fk| {
            lsp_semantics::signature_help(elab, &fk, text, pos.line, pos.character).map(|labels| {
                SignatureHelp {
                    signatures: labels
                        .into_iter()
                        .map(|label| SignatureInformation {
                            label,
                            documentation: None,
                            parameters: None,
                            active_parameter: Some(0),
                        })
                        .collect(),
                    active_signature: Some(0),
                    active_parameter: Some(0),
                }
            })
        });
        connection
            .sender
            .send(Response::new_ok(id, serde_json::to_value(sh)?).into())?;
        return Ok(());
    }

    if method == DocumentHighlightRequest::METHOD {
        let params: DocumentHighlightParams = serde_json::from_value(req.params.clone())?;
        let g = global.lock().unwrap();
        let uri = &params.text_document_position_params.text_document.uri;
        let doc = g.docs.get(uri);
        let text = doc.map(|d| d.text.as_str()).unwrap_or("");
        let pos = &params.text_document_position_params.position;
        let hi: Vec<DocumentHighlight> =
            lsp_semantics::document_highlights(text, pos.line, pos.character)
                .into_iter()
                .map(|range| DocumentHighlight {
                    range,
                    kind: Some(DocumentHighlightKind::TEXT),
                })
                .collect();
        connection
            .sender
            .send(Response::new_ok(id, serde_json::to_value(hi)?).into())?;
        return Ok(());
    }

    if method == DocumentSymbolRequest::METHOD {
        let params: DocumentSymbolParams = serde_json::from_value(req.params.clone())?;
        let g = global.lock().unwrap();
        let uri = &params.text_document.uri;
        let fk = file_key(&g, uri);
        let elab = g.last_snap.get(uri).and_then(|s| s.elaborated.as_ref());
        let syms = fk
            .map(|fk| {
                DocumentSymbolResponse::Nested(
                    lsp_semantics::document_symbols(elab, &fk)
                        .into_iter()
                        .map(|row| {
                            #[allow(deprecated)]
                            DocumentSymbol {
                                name: row.name,
                                detail: Some(row.detail).filter(|d| !d.is_empty()),
                                kind: SymbolKind::FUNCTION,
                                tags: None,
                                deprecated: None,
                                range: row.range,
                                selection_range: row.selection_range,
                                children: None,
                            }
                        })
                        .collect(),
                )
            })
            .unwrap_or_else(|| DocumentSymbolResponse::Nested(vec![]));
        connection
            .sender
            .send(Response::new_ok(id, serde_json::to_value(syms)?).into())?;
        return Ok(());
    }

    if method == WorkspaceSymbolRequest::METHOD {
        let _params: WorkspaceSymbolParams = serde_json::from_value(req.params.clone())?;
        let g = global.lock().unwrap();
        let Some(ref root) = g.workspace_root else {
            connection
                .sender
                .send(Response::new_ok(id, serde_json::json!([])).into())?;
            return Ok(());
        };
        let elab = g
            .last_snap
            .values()
            .max_by_key(|s| s.elaborated.as_ref().map_or(0, |e| e.len()))
            .and_then(|s| s.elaborated.as_ref());
        let syms: Vec<SymbolInformation> = lsp_semantics::workspace_symbol(elab, root)
            .into_iter()
            .filter_map(|row| {
                let uri: Uri = row.uri_str.parse().ok()?;
                #[allow(deprecated)]
                Some(SymbolInformation {
                    name: row.name,
                    kind: SymbolKind::FUNCTION,
                    tags: None,
                    deprecated: None,
                    location: Location {
                        uri,
                        range: row.range,
                    },
                    container_name: Some(row.type_str),
                })
            })
            .collect();
        connection
            .sender
            .send(Response::new_ok(id, serde_json::to_value(syms)?).into())?;
        return Ok(());
    }

    if method == References::METHOD {
        let params: ReferenceParams = serde_json::from_value(req.params.clone())?;
        let g = global.lock().unwrap();
        let uri = &params.text_document_position.text_document.uri;
        let doc = g.docs.get(uri);
        let text = doc.map(|d| d.text.as_str()).unwrap_or("");
        let pos = &params.text_document_position.position;
        let locs: Vec<Location> =
            lsp_semantics::references_in_file(text, pos.line, pos.character, uri.as_str())
                .into_iter()
                .filter_map(|s| s.try_lsp_location())
                .collect();
        connection
            .sender
            .send(Response::new_ok(id, serde_json::to_value(locs)?).into())?;
        return Ok(());
    }

    if method == PrepareRenameRequest::METHOD {
        let params: TextDocumentPositionParams = serde_json::from_value(req.params.clone())?;
        let g = global.lock().unwrap();
        let uri = &params.text_document.uri;
        let doc = g.docs.get(uri);
        let text = doc.map(|d| d.text.as_str()).unwrap_or("");
        let pos = &params.position;
        let resp = lsp_semantics::prepare_rename(text, pos.line, pos.character)
            .map(PrepareRenameResponse::Range);
        connection
            .sender
            .send(Response::new_ok(id, serde_json::to_value(resp)?).into())?;
        return Ok(());
    }

    if method == Rename::METHOD {
        let params: RenameParams = serde_json::from_value(req.params.clone())?;
        let g = global.lock().unwrap();
        let uri = &params.text_document_position.text_document.uri;
        let doc = g.docs.get(uri);
        let text = doc.map(|d| d.text.as_str()).unwrap_or("");
        let pos = &params.text_document_position.position;
        let Some(range) = lsp_semantics::prepare_rename(text, pos.line, pos.character) else {
            connection
                .sender
                .send(Response::new_ok(id, serde_json::Value::Null).into())?;
            return Ok(());
        };
        let Some(edit) =
            lsp_semantics::workspace_edit_rename(uri.as_str(), range, &params.new_name)
        else {
            connection
                .sender
                .send(Response::new_ok(id, serde_json::Value::Null).into())?;
            return Ok(());
        };
        connection
            .sender
            .send(Response::new_ok(id, serde_json::to_value(edit)?).into())?;
        return Ok(());
    }

    if method == FoldingRangeRequest::METHOD {
        let params: FoldingRangeParams = serde_json::from_value(req.params.clone())?;
        let g = global.lock().unwrap();
        let uri = &params.text_document.uri;
        let doc = g.docs.get(uri);
        let text = doc.map(|d| d.text.as_str()).unwrap_or("");
        let fk = file_key(&g, uri);
        let elab = g.last_snap.get(uri).and_then(|s| s.elaborated.as_ref());
        let folds = lsp_semantics::folding_ranges_with_analysis(elab, fk.as_deref(), text);
        connection
            .sender
            .send(Response::new_ok(id, serde_json::to_value(folds)?).into())?;
        return Ok(());
    }

    if method == SelectionRangeRequest::METHOD {
        let params: SelectionRangeParams = serde_json::from_value(req.params.clone())?;
        let g = global.lock().unwrap();
        let uri = &params.text_document.uri;
        let doc = g.docs.get(uri);
        let text = doc.map(|d| d.text.as_str()).unwrap_or("");
        let mut out = Vec::new();
        for pos in &params.positions {
            if let Some(sr) = lsp_semantics::selection_range_at(text, pos.line, pos.character) {
                out.push(sr);
            }
        }
        connection
            .sender
            .send(Response::new_ok(id, serde_json::to_value(out)?).into())?;
        return Ok(());
    }

    if method == InlayHintRequest::METHOD {
        let params: InlayHintParams = serde_json::from_value(req.params.clone())?;
        let g = global.lock().unwrap();
        let uri = &params.text_document.uri;
        let fk = file_key(&g, uri);
        let elab = g.last_snap.get(uri).and_then(|s| s.elaborated.as_ref());
        let doc = g.docs.get(uri);
        let text = doc.map(|d| d.text.as_str()).unwrap_or("");
        let hints = fk
            .map(|fk| lsp_semantics::inlay_hints(elab, &fk, text))
            .unwrap_or_default();
        connection
            .sender
            .send(Response::new_ok(id, serde_json::to_value(hints)?).into())?;
        return Ok(());
    }

    if method == SemanticTokensFullRequest::METHOD {
        let params: SemanticTokensParams = serde_json::from_value(req.params.clone())?;
        let g = global.lock().unwrap();
        let uri = &params.text_document.uri;
        let doc = g.docs.get(uri);
        let text = doc.map(|d| d.text.as_str()).unwrap_or("");
        let tok = lsp_semantics::semantic_tokens(text).unwrap_or_else(|| SemanticTokens {
            result_id: None,
            data: vec![],
        });
        connection
            .sender
            .send(Response::new_ok(id, serde_json::to_value(tok)?).into())?;
        return Ok(());
    }

    if method == Formatting::METHOD {
        let params: DocumentFormattingParams = serde_json::from_value(req.params.clone())?;
        let g = global.lock().unwrap();
        let uri = &params.text_document.uri;
        let tab = params.options.tab_size.try_into().unwrap_or(4usize).max(1);
        let Some(virtual_path) = uri_local_path_for_tooling(uri) else {
            connection
                .sender
                .send(Response::new_ok(id, serde_json::Value::Null).into())?;
            return Ok(());
        };
        let Some(doc) = g.docs.get(uri) else {
            connection
                .sender
                .send(Response::new_ok(id, serde_json::Value::Null).into())?;
            return Ok(());
        };
        match ur::ur_format::format_source_path(&virtual_path, &doc.text, tab) {
            Ok(fmt) if fmt == doc.text => {
                connection
                    .sender
                    .send(Response::new_ok(id, serde_json::json!([])).into())?;
            }
            Ok(fmt) => {
                let edits = vec![TextEdit {
                    range: ur::lsp_support::lsp_full_document_range(&doc.text),
                    new_text: fmt,
                }];
                connection
                    .sender
                    .send(Response::new_ok(id, serde_json::to_value(edits)?).into())?;
            }
            Err(_) => {
                connection
                    .sender
                    .send(Response::new_ok(id, serde_json::Value::Null).into())?;
            }
        }
        return Ok(());
    }

    if req.method.starts_with("$/") {
        connection
            .sender
            .send(Response::new_ok(id, serde_json::Value::Null).into())?;
        return Ok(());
    }

    connection.sender.send(
        Response::new_err(
            id,
            ErrorCode::MethodNotFound as i32,
            format!("unknown method: {method}"),
        )
        .into(),
    )?;
    Ok(())
}
