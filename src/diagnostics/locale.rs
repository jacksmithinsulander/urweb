//! Project language for diagnostic templates (`ur.toml` `[package].language`).
//!
//! Tools honor [`crate::cli_common::URWEB_LANG_ENV`] when the manifest is missing or silent on `language`.

/// Supported languages for compiler diagnostics (batch, LSP, tests).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum DiagnosticLocale {
    /// English messages (default).
    #[default]
    En,
    /// Swedish messages.
    Sv,
    /// Spanish messages.
    Es,
}

impl DiagnosticLocale {
    /// Parse a manifest or config token (`en`, `sv`, `es`); case-insensitive.
    ///
    /// # Arguments
    ///
    /// * `raw` — User-supplied language code from `ur.toml`.
    ///
    /// # Returns
    ///
    /// [`Some(DiagnosticLocale)`] when `raw` is a known code, else [`None`].
    pub fn parse_manifest_token(raw: &str) -> Option<Self> {
        match raw.trim().to_ascii_lowercase().as_str() {
            "en" | "english" => Some(Self::En),
            "sv" | "swedish" | "svenska" => Some(Self::Sv),
            "es" | "spanish" | "español" | "espanol" => Some(Self::Es),
            _ => None,
        }
    }
}
