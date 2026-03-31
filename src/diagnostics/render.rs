//! Replace `{0}`, `{1}`, … in templates and render nested [`DiagnosticPayload`] trees.

use super::ids::DiagnosticId;
use super::locale::DiagnosticLocale;
use super::payload::{DiagnosticHint, DiagnosticPayload};
use super::template_tables::diagnostic_template;

/// Same trailer as legacy [`crate::error_types::HINT_TRAILER_PREFIX`] for hint paragraphs.
pub const HINT_TRAILER_PREFIX: &str = "\n  hint: ";

/// Substitute positional `{i}` placeholders in `template_str` with `args` (all occurrences per index).
///
/// # Arguments
///
/// * `template_str` — Catalog string containing `{0}`, `{1}`, … placeholders.
/// * `args` — Replacement strings; missing indices leave placeholders unchanged (should not happen for valid catalogs).
///
/// # Returns
///
/// Filled string for display.
pub(crate) fn apply_template(template_str: &str, args: &[String]) -> String {
    let mut out = template_str.to_string();
    for (index, replacement) in args.iter().enumerate() {
        let needle = format!("{{{index}}}");
        out = out.replace(&needle, replacement);
    }
    out
}

/// Render a hint block to a single string (no `hint:` prefix; layout adds it).
///
/// # Arguments
///
/// * `hint` — Hint id and args.
/// * `locale` — Active project language.
///
/// # Returns
///
/// Localized hint paragraph.
pub(crate) fn render_hint(hint: &DiagnosticHint, locale: DiagnosticLocale) -> String {
    let template_str = diagnostic_template(hint.id, locale);
    apply_template(template_str, &hint.args)
}

/// Recursively render a [`DiagnosticPayload`] including suffix payloads and arity expansion.
///
/// # Arguments
///
/// * `payload` — Structured diagnostic tree.
/// * `locale` — Active project language.
///
/// # Returns
///
/// Localized primary body (hints handled separately by caller).
pub fn render_diagnostic_body(payload: &DiagnosticPayload, locale: DiagnosticLocale) -> String {
    let mut collected: Vec<String> = payload.args.clone();
    for suffix in &payload.suffix_payloads {
        collected.push(render_diagnostic_body(suffix, locale));
    }
    let template_str = diagnostic_template(payload.id, locale);
    apply_template(template_str, &collected)
}

/// Full multi-paragraph user text: primary body plus optional hint trailer (no banner or `-->` line).
///
/// # Arguments
///
/// * `payload` — Catalog id, args, suffix payloads, and optional hint.
/// * `locale` — Active project language.
///
/// # Returns
///
/// String suitable for embedding in located compiler diagnostics.
pub fn format_diagnostic_payload_for_user(
    payload: &DiagnosticPayload,
    locale: DiagnosticLocale,
) -> String {
    let body = render_diagnostic_body(payload, locale);
    if let Some(hint) = &payload.hint {
        let hint_text = render_hint(hint, locale);
        if hint_text.is_empty() {
            return body;
        }
        return format!("{body}{}{hint_text}", HINT_TRAILER_PREFIX);
    }
    body
}

/// Stable numeric code for Language Server Protocol `Diagnostic.code` (explicit enum discriminant).
///
/// # Arguments
///
/// * `id` — Diagnostic identifier carried on this error.
///
/// # Returns
///
/// The same value as `id as u32`.
pub fn diagnostic_id_as_u32(id: DiagnosticId) -> u32 {
    id as u32
}
