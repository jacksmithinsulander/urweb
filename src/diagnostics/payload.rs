//! Structured diagnostic text: stable [`super::ids::DiagnosticId`] plus interpolated arguments.

use super::ids::DiagnosticId;

/// Severity level for a [`DiagnosticPayload`], used for color rendering and tracing-level mapping.
///
/// Drives the ANSI banner color in terminal output and selects which [`tracing`] level the
/// diagnostic is emitted at when [`crate::error_types::ErrorReporter::report`] is called.
/// Defaults to [`DiagnosticSeverity::Error`] so existing [`DiagnosticPayload::new`] call sites
/// are unaffected.
///
/// | Variant | Banner color | Tracing level | Minimum `-v` to see |
/// |---------|-------------|---------------|----------------------|
/// | `Error`   | bold red    | `error`       | always               |
/// | `Warning` | bold yellow | `warn`        | always               |
/// | `Info`    | bold cyan   | `info`        | `-vv` (verbosity ≥ 2) |
/// | `Hint`    | bold green  | `info`        | `-v` (verbosity ≥ 1)  |
/// | `Debug`   | dim         | `debug`       | `-vvv` (verbosity ≥ 3)|
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum DiagnosticSeverity {
    /// Hard compiler error; always displayed; bold red banner.
    #[default]
    Error,
    /// Potentially incorrect but non-fatal; bold yellow banner.
    Warning,
    /// Informational note; bold cyan banner; emitted at `tracing::info!` level.
    Info,
    /// Supplemental suggestion (shown near a hint paragraph); bold green banner; `tracing::info!` level.
    Hint,
    /// Internal debug detail; dimmed banner; emitted at `tracing::debug!` level.
    Debug,
}

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
    /// Severity level for terminal color selection and tracing-event level mapping.
    ///
    /// Defaults to [`DiagnosticSeverity::Error`]; use [`DiagnosticPayload::with_severity`] to
    /// override for warnings, informational notes, or debug details.
    pub severity: DiagnosticSeverity,
    /// Pairs of `(inferred_arg_index, expected_arg_index)` that a color-aware renderer should
    /// diff-highlight against each other using word-level LCS comparison.
    ///
    /// An empty list (the default) means no diff highlighting is applied. When non-empty each
    /// pair tells [`crate::diagnostics::render::render_diagnostic_body_colored`] to replace
    /// `args[inferred_arg_index]` and `args[expected_arg_index]` with ANSI-highlighted versions
    /// before template substitution. Plain-mode rendering ignores this field entirely, so the
    /// payload is fully backwards-compatible.
    pub diff_hints: Vec<(usize, usize)>,
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
            severity: DiagnosticSeverity::default(), // Default to Error so existing callers are unaffected.
            diff_hints: Vec::new(), // No diff hints by default; callers opt in via with_diff_hint.
        }
    }

    /// Override the default [`DiagnosticSeverity::Error`] severity for this payload.
    ///
    /// Use this when constructing warnings, informational notes, or debug-only details that
    /// should render with a different banner color and tracing event level.
    ///
    /// # Arguments
    ///
    /// * `severity` — Desired severity level.
    ///
    /// # Returns
    ///
    /// `self` with [`DiagnosticPayload::severity`] set to `severity`.
    pub fn with_severity(mut self, severity: DiagnosticSeverity) -> Self {
        self.severity = severity; // Override the Error default with the caller-specified level.
        self
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

    /// Mark two arg indices as a type diff pair for color-aware rendering.
    ///
    /// When [`crate::diagnostics::render::render_diagnostic_body_colored`] processes this payload it
    /// will compute a word-level diff between `args[inferred_idx]` and `args[expected_idx]` and
    /// replace both with ANSI-highlighted versions before template substitution. Plain-mode
    /// rendering (LSP, pipes, `NO_COLOR`) ignores these hints entirely.
    ///
    /// # Arguments
    ///
    /// * `inferred_idx` — Index into [`DiagnosticPayload::args`] for the inferred (found) type string.
    /// * `expected_idx` — Index into [`DiagnosticPayload::args`] for the expected (needed) type string.
    ///
    /// # Returns
    ///
    /// `self` with the pair appended to [`DiagnosticPayload::diff_hints`].
    pub fn with_diff_hint(mut self, inferred_idx: usize, expected_idx: usize) -> Self {
        self.diff_hints.push((inferred_idx, expected_idx)); // record the index pair for the colored renderer
        self
    }
}
