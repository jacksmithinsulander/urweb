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

/// True when `run()` failed with a disconnect-style error that should exit 0.
pub fn disconnect_error_exits_clean(msg: &str) -> bool {
    msg.contains("disconnected") || msg.contains("channel") || msg.contains("io error")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn disconnect_clean_is_any_substring_not_all() {
        assert!(disconnect_error_exits_clean("disconnected"));
        assert!(disconnect_error_exits_clean("channel closed"));
        assert!(disconnect_error_exits_clean("io error"));
        assert!(!disconnect_error_exits_clean("fatal compiler bug"));
    }
}
