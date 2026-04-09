//! Structured diagnostic text: stable [`super::ids::DiagnosticId`] plus interpolated arguments.

use super::ids::DiagnosticId;

/// Optional hint paragraph following the main diagnostic body (shown after `hint:` in the layout).
#[derive(Debug, Clone)]
pub struct DiagnosticHint {
    /// Catalog id for the hint template.
    pub id: DiagnosticId,
    /// Positional placeholders `{0}`, `{1}`, … in the hint template.
    pub args: Vec<String>,
}

/// User-facing diagnostic text built from a catalog template, optional suffix payloads, and hint.
#[derive(Debug, Clone)]
pub struct DiagnosticPayload {
    /// Primary message template id.
    pub id: DiagnosticId,
    /// Arguments for `{0}`, `{1}`, … in the primary template before suffix expansion.
    pub args: Vec<String>,
    /// Each entry is fully rendered (with locale) and appended as the next `{n}` placeholder.
    pub suffix_payloads: Vec<DiagnosticPayload>,
    /// Optional hint line (separate template).
    pub hint: Option<DiagnosticHint>,
}

impl DiagnosticPayload {
    /// Primary text only, no hint or suffix payloads.
    ///
    /// # Arguments
    ///
    /// * `id` — Template selector.
    /// * `args` — Values for positional placeholders.
    ///
    /// # Returns
    ///
    /// A [`DiagnosticPayload`] with empty suffix list and no hint.
    pub fn new(id: DiagnosticId, args: Vec<String>) -> Self {
        Self {
            id,
            args,
            suffix_payloads: Vec::new(),
            hint: None,
        }
    }

    /// Attaches a hint built from another template id and args.
    ///
    /// # Arguments
    ///
    /// * `self` — Main diagnostic.
    /// * `hint_id` — Hint template id.
    /// * `hint_args` — Hint placeholder values.
    ///
    /// # Returns
    ///
    /// `self` with [`DiagnosticPayload::hint`] set.
    pub fn with_hint(mut self, hint_id: DiagnosticId, hint_args: Vec<String>) -> Self {
        self.hint = Some(DiagnosticHint {
            id: hint_id,
            args: hint_args,
        });
        self
    }

    /// Appends a nested payload whose rendered text becomes the next `{n}` argument.
    ///
    /// # Arguments
    ///
    /// * `self` — Outer diagnostic.
    /// * `suffix` — Inner diagnostic rendered after outer `args` fill their slots.
    ///
    /// # Returns
    ///
    /// `self` with `suffix` pushed onto [`DiagnosticPayload::suffix_payloads`].
    pub fn with_suffix(mut self, suffix: DiagnosticPayload) -> Self {
        self.suffix_payloads.push(suffix);
        self
    }
}
