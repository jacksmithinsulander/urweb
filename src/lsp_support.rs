//! Helpers shared by the `ur-lsp` binary, unit-tested here so `||`/`&&` mutants
//! in the binary cannot survive without failing library tests.
//!
//! ## Untrusted input surfaces (LangSec / Zencode-style inventory)
//!
//! The LSP server accepts:
//!
//! - **stdio JSON-RPC**: LSP handshake and notifications. Params are deserialized with
//!   `serde_json` into `lsp-types` structs (`DidOpenTextDocumentParams`, etc.); treat those
//!   as the schema boundary for RPC payloads.
//! - **Document text**: Passed to [`crate::parse::parse_ur`], which runs the composed pipeline
//!   (rewrites → [`crate::parse::lexical_analyzer::XmlAwareLexer`] → LALRPOP). Errors are reported
//!   through [`crate::error_types::ErrorReporter`], not panics.
//!
//! There is no secondary “shotgun” rescan of the same buffer for structure beyond this path.

use anyhow::Result;
use lsp_server::{Connection, Message, Notification};
use lsp_types::{
    notification::{Notification as NotificationTrait, PublishDiagnostics},
    Diagnostic, DiagnosticSeverity, Position, PublishDiagnosticsParams, Range, Uri,
};

use crate::error_types::{CompileError, ErrorReporter};
use crate::parse::parse_ur;

/// True when `run()` failed with a disconnect-style error that should exit 0.
pub fn disconnect_error_exits_clean(msg: &str) -> bool {
    msg.contains("disconnected") || msg.contains("channel") || msg.contains("io error")
}

/// Convert a [`CompileError`] to an LSP [`Diagnostic`].
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

/// Parse `text` as Ur/Web under `uri` and publish diagnostics to the LSP client.
pub fn publish_parse_diagnostics(connection: &Connection, uri: &Uri, text: &str) -> Result<()> {
    let file_name = uri.as_str();
    let mut errors = ErrorReporter::new();
    let _ = parse_ur(file_name, text, &mut errors);

    let diagnostics: Vec<Diagnostic> = errors
        .errors
        .iter()
        .map(compile_error_to_diagnostic)
        .collect();

    let params = PublishDiagnosticsParams {
        uri: uri.clone(),
        diagnostics,
        version: None,
    };

    connection
        .sender
        .send(Message::Notification(Notification::new(
            <PublishDiagnostics as NotificationTrait>::METHOD.to_owned(),
            params,
        )))?;

    Ok(())
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
        let e = CompileError::at(span, "bad");
        let d = compile_error_to_diagnostic(&e);
        assert_eq!(d.range.start.line, 1);
        assert_eq!(d.range.start.character, 3);
        assert_eq!(d.range.end.line, 1);
        assert_eq!(d.range.end.character, 10);
        assert_eq!(d.source.as_deref(), Some("ur-lsp"));
        assert_eq!(d.severity, Some(DiagnosticSeverity::ERROR));
    }

    #[test]
    fn compile_error_to_diagnostic_plain_uses_origin_range() {
        let e = CompileError::Plain("x".into());
        let d = compile_error_to_diagnostic(&e);
        assert_eq!(d.range.start.line, 0);
        assert_eq!(d.range.start.character, 0);
    }
}
