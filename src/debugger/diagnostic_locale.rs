//! Localized copy for debugger (DAP + GDB/MI) user-visible strings via the diagnostic catalog.

use crate::cli_common::{cli_diagnostic_text, diagnostic_locale_for_cli};
use crate::diagnostics::{DiagnosticId, DiagnosticLocale};

/// Fill a catalog template for the active debugger locale.
#[inline]
pub(crate) fn debugger_diagnostic_text(
    diagnostic_id: DiagnosticId,
    arguments: Vec<String>,
) -> String {
    let locale: DiagnosticLocale = diagnostic_locale_for_cli(None);
    cli_diagnostic_text(diagnostic_id, arguments, locale)
}
