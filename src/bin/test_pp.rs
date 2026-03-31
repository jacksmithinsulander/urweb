//! Internal dev binary: inspect a fixed window of preprocessed `basis.urs` text.

use ur::cli_common::{cli_diagnostic_text, diagnostic_locale_for_cli, writeln_stdout_display};
use ur::diagnostics::DiagnosticId;

/// Call [`ur::parse::basis_urs_preprocessed_window`] with hard-coded offsets; print debug text or stderr on failure.
fn main() {
    let locale = diagnostic_locale_for_cli(None);
    match ur::parse::basis_urs_preprocessed_window(38564, 200, 100) {
        Ok(context) => {
            let line = cli_diagnostic_text(
                DiagnosticId::CliTestPpContextOk,
                vec![format!("{context:?}")],
                locale,
            );
            writeln_stdout_display(line);
        }
        Err(window_error) => {
            let msg = cli_diagnostic_text(
                DiagnosticId::CliDevPreprocessWindowFailed,
                vec![window_error.to_string()],
                locale,
            );
            ur::cli_common::writeln_stderr_display(msg);
            std::process::exit(1);
        }
    }
}
