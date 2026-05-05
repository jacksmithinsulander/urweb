//! Replace `{0}`, `{1}`, … in templates and render nested [`DiagnosticPayload`] trees.

use super::ids::DiagnosticId;
use super::locale::DiagnosticLocale;
use super::payload::{DiagnosticHint, DiagnosticPayload};
use super::template_tables::diagnostic_template;
use super::type_diff;

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

/// Recursively render a [`DiagnosticPayload`] with word-level diff ANSI highlighting on type pairs.
///
/// Identical to [`render_diagnostic_body`] except that for each pair `(i, j)` in
/// [`DiagnosticPayload::diff_hints`] the args at those indices are replaced with their
/// ANSI-highlighted diff versions before template substitution. Suffix payloads are also rendered
/// via this function so nested constructor-mismatch messages benefit from the same highlighting.
///
/// This function is only called on the terminal-color path; LSP and plain-text output continue
/// using [`render_diagnostic_body`], which ignores `diff_hints` entirely.
///
/// # Arguments
///
/// * `payload` — Structured diagnostic tree, possibly carrying diff hints.
/// * `locale` — Active project language.
///
/// # Returns
///
/// Localized primary body with ANSI color codes embedded at the diverging tokens.
pub fn render_diagnostic_body_colored(
    payload: &DiagnosticPayload,
    locale: DiagnosticLocale,
) -> String {
    let mut effective_args = payload.args.clone(); // start from the plain args; we may replace some

    // Apply diff highlighting to every (inferred, expected) pair registered on this payload.
    for &(inferred_idx, expected_idx) in &payload.diff_hints {
        if inferred_idx < effective_args.len() && expected_idx < effective_args.len() {
            // Compute the word-level diff between the two formatted type strings.
            let (colored_inferred, colored_expected) = type_diff::diff_type_strings(
                &effective_args[inferred_idx],
                &effective_args[expected_idx],
            );
            effective_args[inferred_idx] = colored_inferred; // replace inferred arg with red-highlighted version
            effective_args[expected_idx] = colored_expected; // replace expected arg with green-highlighted version
        }
    }

    // Render suffix payloads recursively so nested constructor/kind errors also highlight diffs.
    for suffix in &payload.suffix_payloads {
        effective_args.push(render_diagnostic_body_colored(suffix, locale));
    }

    let template_str = diagnostic_template(payload.id, locale); // fetch the localized catalog template
    apply_template(template_str, &effective_args) // substitute colored args into the template
}

/// Full multi-paragraph user text with ANSI diff highlighting: primary body plus optional hint trailer.
///
/// Mirrors [`format_diagnostic_payload_for_user`] but delegates body rendering to
/// [`render_diagnostic_body_colored`] so any registered diff hints are applied.  Hint text is
/// rendered without diff highlighting because hints do not contain type-pair arguments.
///
/// # Arguments
///
/// * `payload` — Catalog id, args, suffix payloads, diff hints, and optional hint.
/// * `locale` — Active project language.
///
/// # Returns
///
/// String with embedded ANSI escape sequences, suitable for the terminal-color path only.
pub fn format_diagnostic_payload_for_user_colored(
    payload: &DiagnosticPayload,
    locale: DiagnosticLocale,
) -> String {
    let body = render_diagnostic_body_colored(payload, locale); // build the colored body
    if let Some(hint) = &payload.hint {
        let hint_text = render_hint(hint, locale); // hints are plain; no diff highlighting needed
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
