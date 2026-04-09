//! Dump C and SQL output from the compiler without linking.
//! Used by scripts/compare-compilers.sh to compare Rust vs ML compiler output.
//!
//! Usage: cargo run --example dump_output -- <path-to.urp> <output.c> <output.sql>

use std::env;
use std::fs;
use std::path::Path;

use ur::cli_common::{
    cli_diagnostic_text, diagnostic_locale_for_cli, writeln_stderr_display, writeln_stderr_line,
};
use ur::diagnostics::DiagnosticId;

/// Parse three path arguments, run [`ur::compiler::compile_to_outputs`], write C and SQL files, or exit with an error line on stderr.
fn main() {
    let args: Vec<String> = env::args().collect();
    let locale = diagnostic_locale_for_cli(None);
    if args.len() != 4 {
        let msg = cli_diagnostic_text(DiagnosticId::CliDumpOutputUsage, vec![], locale);
        writeln_stderr_line(&msg);
        std::process::exit(1);
    }
    let urp_path = Path::new(&args[1]);
    let c_out = &args[2];
    let sql_out = &args[3];

    let project_dir = urp_path.parent().unwrap_or_else(|| Path::new("."));
    if let Err(chdir_error) = env::set_current_dir(project_dir) {
        let msg = cli_diagnostic_text(
            DiagnosticId::CliDumpOutputChdirFailed,
            vec![project_dir.display().to_string(), chdir_error.to_string()],
            locale,
        );
        writeln_stderr_display(msg);
        std::process::exit(1);
    }

    let mut settings = ur::settings::Settings {
        db_backend: Some(ur::db::ProjectDb::sqlite()),
        boot_linking: true,
        ..Default::default()
    };

    match ur::compiler::compile_to_outputs(urp_path, &mut settings) {
        Ok((c_code, sql_ddl)) => {
            // Write generated C code to the requested output path; exit on I/O failure
            if let Err(write_error) = fs::write(c_out, &c_code) {
                writeln_stderr_line(&format!(
                    "error: could not write C output to {c_out}: {write_error}"
                ));
                std::process::exit(1);
            }
            // Write generated SQL DDL to the requested output path; exit on I/O failure
            if let Err(write_error) = fs::write(sql_out, &sql_ddl) {
                writeln_stderr_line(&format!(
                    "error: could not write SQL output to {sql_out}: {write_error}"
                ));
                std::process::exit(1);
            }
        }
        Err(pipeline_error) => {
            let msg = cli_diagnostic_text(
                DiagnosticId::CliDumpOutputCompileFailed,
                vec![pipeline_error.to_string()],
                locale,
            );
            writeln_stderr_display(msg);
            std::process::exit(1);
        }
    }
}
