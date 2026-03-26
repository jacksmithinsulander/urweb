//! Helpers for the `ur-lsp` binary (Language Server Protocol integration).
//!
//! Lives in the library so boolean-branch mutants in `||` / `&&` inside the binary still fail tests here.
//!
//! The editor uses standard input and standard output with JSON remote procedure call framing from `lsp_server`.
//! Parameters deserialize through `serde_json` into `lsp-types` structs; treat that as the schema boundary for untrusted input
//! (language-based security expectations, Zencode-style inventories).
//!
//! ## Untrusted input surfaces
//!
//! - JSON remote procedure calls on standard input/output: handshake and notifications become typed `lsp-types` values.
//! - Document text: [`crate::parse::parse_ur`] or [`crate::compiler::parse_sources_with_overlay`] (rewrites, XML-aware lexer,
//!   then tables from the LALRPOP parser generator). Errors use [`crate::error_types::ErrorReporter`], not panics.
//! - Language Server Protocol requests (for example `textDocument/hover`): same deserialization boundary in the binary; extend when adding handlers.
//!
//! There is no extra full-buffer rescan beyond this pipeline.
//!
//! **Style:** new/edited Rust here follows [README.md](../README.md) Rust code style (exceptions documented there).

use anyhow::Result;
use lsp_server::{Connection, Message, Notification};
use lsp_types::{
    notification::{Notification as NotificationTrait, PublishDiagnostics},
    Diagnostic, DiagnosticSeverity, Position, PublishDiagnosticsParams, Range, Uri,
};

use crate::db::ProjectDb;
use crate::error_types::{CompileError, ErrorReporter};
use crate::parse::parse_ur;

/// Returns true when `msg` looks like a benign editor disconnect (substring heuristic).
///
/// Matches substrings such as `"disconnected"`, `"channel"`, and `"io error"` so tearing down standard input/output
/// does not force a non-zero exit after the Language Server Protocol client closes the connection.
///
/// # Arguments
///
/// * `msg` — Typically `Display` output from an [`std::io::Error`] or channel error after the client disconnects.
///
/// # Returns
///
/// `true` if the message should be treated as a clean shutdown, `false` otherwise.
pub fn disconnect_error_exits_clean(msg: &str) -> bool {
    msg.contains("disconnected") || msg.contains("channel") || msg.contains("io error")
}

/// Convert one [`CompileError`] into a Language Server Protocol [`Diagnostic`] (range, severity, message).
///
/// Protocol positions use zero-based lines; compiler [`crate::error_types::Span`] lines are one-based, hence `saturating_sub(1)` on lines.
/// Columns are Unicode UTF-8 byte offsets in the line (see [`crate::error_types::Span::from_offsets`]); ASCII-only sources usually match clients,
/// while other text can disagree with the specification’s sixteen-bit Unicode code unit counts.
///
/// # Arguments
///
/// * `e` — Compiler or parse diagnostic to map.
///
/// # Returns
///
/// A filled [`Diagnostic`] with source `"ur-lsp"`.
pub fn compile_error_to_diagnostic(e: &CompileError) -> Diagnostic {
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

    let severity = match e {
        CompileError::WarningAt { .. } => Some(DiagnosticSeverity::WARNING),
        _ => Some(DiagnosticSeverity::ERROR),
    };
    let message = match e {
        CompileError::WarningAt { message, .. } => message.clone(),
        _ => e.to_string(),
    };
    Diagnostic {
        range,
        severity,
        code: None,
        code_description: None,
        source: Some("ur-lsp".into()),
        message,
        related_information: None,
        tags: None,
        data: None,
    }
}

fn publish_diagnostics_params(uri: &Uri, errors: &ErrorReporter) -> PublishDiagnosticsParams {
    let diagnostics: Vec<Diagnostic> = errors
        .errors
        .iter()
        .map(compile_error_to_diagnostic)
        .collect();
    PublishDiagnosticsParams {
        uri: uri.clone(),
        diagnostics,
        version: None,
    }
}

/// Send the `textDocument/publishDiagnostics` notification for `uri` carrying every diagnostic in `errors`.
///
/// `connection` is the active `lsp_server` link; `uri` is the uniform resource identifier the client bound to the document.
///
/// # Arguments
///
/// * `connection` — Active Language Server Protocol connection (stdio sender).
/// * `uri` — Document uniform resource identifier for this publish batch.
/// * `errors` — Collected diagnostics to serialize as protocol items.
///
/// # Returns
///
/// `Ok(())` when the notification is queued on the connection’s outbound channel.
///
/// # Errors
///
/// If sending on `connection.sender` fails (broken pipe, disconnected client, …).
pub fn publish_diagnostics(
    connection: &Connection,
    uri: &Uri,
    errors: &ErrorReporter,
) -> Result<()> {
    let params = publish_diagnostics_params(uri, errors);
    connection
        .sender
        .send(Message::Notification(Notification::new(
            <PublishDiagnostics as NotificationTrait>::METHOD.to_owned(),
            params,
        )))?;
    Ok(())
}

/// Lex and parse `text` without loading the full project, then publish diagnostics.
///
/// Uses [`parse_ur`] with an empty [`ProjectDb`]; handy for unsaved buffers when no `.urp` graph is open.
///
/// # Arguments
///
/// * `connection` — Active Language Server Protocol connection.
/// * `uri` — Document identifier (also used as the synthetic filename label for parsing).
/// * `text` — Full buffer text to parse.
///
/// # Returns
///
/// `Ok(())` after diagnostics are sent, or the same error as [`publish_diagnostics`].
///
/// # Errors
///
/// Propagates channel send failures from [`publish_diagnostics`].
pub fn publish_parse_diagnostics(connection: &Connection, uri: &Uri, text: &str) -> Result<()> {
    let file_name = uri.as_str();
    let mut errors = ErrorReporter::new_silent();
    let _ = parse_ur(file_name, text, &mut errors, ProjectDb::default());
    publish_diagnostics(connection, uri, &errors)
}

/// Build a [`Range`] over all of `text` for one full-document [`TextEdit`].
///
/// The end column counts sixteen-bit Unicode code units on the last line, per the protocol and `lsp-types`
/// (see [`str::encode_utf16`]).
///
/// # Arguments
///
/// * `text` — Full document buffer.
///
/// # Returns
///
/// Range from `(0,0)` through the last line’s end column in UTF-16 code units.
pub fn lsp_full_document_range(text: &str) -> Range {
    let lines: Vec<&str> = text.split('\n').collect();
    let last_line_idx = lines.len().saturating_sub(1);
    let last_line = lines.get(last_line_idx).copied().unwrap_or("");
    let end_char = last_line.encode_utf16().count() as u32;
    Range::new(
        Position::new(0, 0),
        Position::new(last_line_idx as u32, end_char),
    )
}

/// Next monotonic analysis generation: first open uses `1`, each `didChange` bumps the previous value.
///
/// # Arguments
///
/// * `previous_document_generation` — `None` for `didOpen`, `Some(prior)` after each `didChange`.
///
/// # Returns
///
/// Generation stamp paired with scheduled analysis so stale results can be dropped.
pub fn next_buffer_analysis_generation(previous_document_generation: Option<u64>) -> u64 {
    previous_document_generation
        .map(|generation| generation.saturating_add(1))
        .unwrap_or(1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error_types::{Pos, Span};

    #[test]
    fn disconnect_clean_is_any_substring_not_all() {
        assert!(disconnect_error_exits_clean("disconnected"));
        assert!(disconnect_error_exits_clean("channel closed"));
        assert!(disconnect_error_exits_clean("io error"));
        assert!(!disconnect_error_exits_clean("fatal compiler bug"));
    }

    #[test]
    fn compile_error_to_diagnostic_maps_span_to_lsp_range() {
        let span = Span {
            file: "file:///x.ur".into(),
            first: Pos { line: 2, col: 3 },
            last: Pos { line: 2, col: 10 },
        };
        let e = CompileError::at(span.clone(), "bad");
        let d = compile_error_to_diagnostic(&e);
        assert_eq!(d.range.start.line, 1);
        assert_eq!(d.range.start.character, 3);
        assert_eq!(d.range.end.line, 1);
        assert_eq!(d.range.end.character, 10);
        assert_eq!(d.source.as_deref(), Some("ur-lsp"));
        assert_eq!(d.severity, Some(DiagnosticSeverity::ERROR));
        let w = CompileError::warning_at(span, "unused");
        assert_eq!(
            compile_error_to_diagnostic(&w).severity,
            Some(DiagnosticSeverity::WARNING)
        );
    }

    #[test]
    fn compile_error_to_diagnostic_plain_uses_origin_range() {
        let e = CompileError::Plain("x".into());
        let d = compile_error_to_diagnostic(&e);
        assert_eq!(d.range.start.line, 0);
        assert_eq!(d.range.start.character, 0);
    }

    #[test]
    fn lsp_full_document_range_covers_utf16_last_line() {
        let text = "a\nbc";
        let range = lsp_full_document_range(text);
        assert_eq!(range.start, Position::new(0, 0));
        assert_eq!(range.end, Position::new(1, 2));
        assert_ne!(
            range,
            Range::default(),
            "non-empty buffer must not use Default range (ur-lsp full_document_range mutant)"
        );
    }

    #[test]
    fn lsp_full_document_range_empty_is_zero_zero() {
        let range = lsp_full_document_range("");
        assert_eq!(range.end.line, 0);
        assert_eq!(range.end.character, 0);
    }

    #[test]
    fn next_buffer_analysis_generation_increments_from_open() {
        assert_eq!(next_buffer_analysis_generation(None), 1);
        assert_eq!(next_buffer_analysis_generation(Some(1)), 2);
        assert_eq!(next_buffer_analysis_generation(Some(2)), 3);
        assert_eq!(next_buffer_analysis_generation(Some(u64::MAX)), u64::MAX);
    }
}
