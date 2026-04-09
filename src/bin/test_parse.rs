//! Dev helper: smoke-test [`ur::parse::parse_top_level_decl_count`] on tiny snippets.

use ur::cli_common::{cli_diagnostic_text, diagnostic_locale_for_cli, writeln_stdout_display};
use ur::diagnostics::DiagnosticId;

/// Run two fixed samples through the parse helper and print summary lines to stdout.
fn main() {
    let locale = diagnostic_locale_for_cli(None);
    let mut errors = ur::error_types::ErrorReporter::new();
    let decl_count = ur::parse::parse_top_level_decl_count("test.ur", "val x = 1", &mut errors);
    let flag_line = cli_diagnostic_text(
        DiagnosticId::CliTestParseHasErrors,
        vec![format!("{:?}", errors.has_errors())],
        locale,
    );
    writeln_stdout_display(flag_line);
    match decl_count {
        Some(count) => {
            let line = cli_diagnostic_text(
                DiagnosticId::CliTestParseDeclCount,
                vec![count.to_string()],
                locale,
            );
            writeln_stdout_display(line);
        }
        None => {
            let line = cli_diagnostic_text(DiagnosticId::CliTestParseFailed, vec![], locale);
            writeln_stdout_display(line);
        }
    }
    let mut errors_second = ur::error_types::ErrorReporter::new();
    let two =
        ur::parse::parse_top_level_decl_count("t.ur", "val a = 1\nval b = 2", &mut errors_second);
    match two {
        Some(count) => {
            let line = cli_diagnostic_text(
                DiagnosticId::CliTestParseTwoDecls,
                vec![count.to_string()],
                locale,
            );
            writeln_stdout_display(line);
        }
        None => {
            let line =
                cli_diagnostic_text(DiagnosticId::CliTestParseTwoDeclsFailed, vec![], locale);
            writeln_stdout_display(line);
        }
    }
}
