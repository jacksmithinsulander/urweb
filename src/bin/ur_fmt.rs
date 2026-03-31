//! Format `.ur` and `.urs` sources after parsing (invalid programs are not rewritten silently).
//!
//! The formatter builds an abstract syntax tree, then pretty-prints. **Style:** [README.md](../../README.md) when edited.

use std::fs;
use std::path::Path;
use std::process;

use ur::cli_common::{self, cli_diagnostic_text, diagnostic_locale_for_cli, writeln_stdout_line};
use ur::diagnostics::DiagnosticId;
use ur::error_types::{format_compile_error_for_terminal, CompileError};

/// Print each [`CompileError`] to standard error using the project locale when known.
fn print_errors(errors: &[CompileError], locale: ur::diagnostics::DiagnosticLocale) {
    for compile_error in errors {
        let rendered = format_compile_error_for_terminal(compile_error, locale);
        ur::cli_common::writeln_stderr_display(rendered);
    }
}

/// Parse `ur-fmt` flags and format listed files or discover the project through `ur.toml`.
///
/// `args` is argv after the program name (`--check`, `--tab`, paths, …). Returns `0` when no file needed changes
/// (or `--check` found no diff), `1` when formatting would change a file or errors occurred.
fn fmt_command(args: &[String]) -> i32 {
    let mut check_mode = false;
    let mut tab_width: usize = 4;
    let mut files: Vec<String> = vec![];
    let mut args_iter = args.iter();
    let default_locale = diagnostic_locale_for_cli(None);
    while let Some(arg) = args_iter.next() {
        let (flag, opt_val) = if let Some(eq) = arg.find('=') {
            let (head, tail) = arg.split_at(eq);
            (head, Some(tail[1..].to_string()))
        } else {
            (arg.as_str(), None)
        };
        match flag {
            "-help" | "--help" | "-h" => {
                let help = cli_diagnostic_text(DiagnosticId::CliUrFmtHelp, vec![], default_locale);
                for line in help.lines() {
                    writeln_stdout_line(line);
                }
                return 0;
            }
            "-check" | "--check" => {
                check_mode = true;
            }
            "-t" | "--tab" => {
                if let Some(width) = opt_val
                    .or_else(|| args_iter.next().cloned())
                    .and_then(|token| token.parse::<usize>().ok())
                {
                    tab_width = width;
                }
            }
            "-w" | "--width" => {
                let _ = opt_val
                    .or_else(|| args_iter.next().cloned())
                    .and_then(|token| token.parse::<u32>().ok());
            }
            candidate if cli_common::is_file_arg(candidate) => {
                files.push(candidate.to_string());
            }
            other => {
                let warn = cli_diagnostic_text(
                    DiagnosticId::CliUrFmtUnknownFlag,
                    vec![other.to_string()],
                    default_locale,
                );
                cli_common::writeln_stderr_display(warn);
            }
        }
    }

    if files.is_empty() {
        let cfg = match cli_common::load_ur_manifest_cwd_for_fmt_discovery() {
            Ok(parsed) => parsed,
            Err(load_error) => {
                cli_common::writeln_stderr_display(load_error);
                return 1;
            }
        };
        let locale = diagnostic_locale_for_cli(Some(&cfg.package.language));
        if let Err(entry_error) = cli_common::require_manifest_entry(&cfg) {
            cli_common::writeln_stderr_display(entry_error);
            return 1;
        }
        let entry = cfg.build.entry.as_str();
        let urp_path = format!("{}.urp", entry);
        if !cli_common::file_exists(&urp_path) {
            let msg = cli_diagnostic_text(
                DiagnosticId::CliUrFmtProjectUrpNotFound,
                vec![urp_path],
                locale,
            );
            cli_common::writeln_stderr_display(msg);
            return 1;
        }
        if let Ok(urp_body) = fs::read_to_string(&urp_path) {
            for raw_line in urp_body.lines() {
                let line = raw_line.trim();
                if cli_common::should_skip_urp_line(line) {
                    continue;
                }
                if cli_common::URP_DIRECTIVE_KEYWORDS
                    .iter()
                    .any(|keyword| line.starts_with(keyword))
                {
                    continue;
                }
                let ur_path = format!("{}.ur", line);
                let urs_path = format!("{}.urs", line);
                if Path::new(&ur_path).exists() {
                    files.push(ur_path);
                }
                if Path::new(&urs_path).exists() {
                    files.push(urs_path);
                }
            }
        }
        if files.is_empty() {
            let msg = cli_diagnostic_text(DiagnosticId::CliUrFmtNoSourceFilesFound, vec![], locale);
            writeln_stdout_line(&msg);
            return 0;
        }
    }

    let locale_for_paths = if files.is_empty() {
        default_locale
    } else {
        match cli_common::load_ur_manifest_cwd() {
            Ok(cfg) => diagnostic_locale_for_cli(Some(&cfg.package.language)),
            Err(_) => default_locale,
        }
    };

    let mut all_ok = true;
    for path in &files {
        if !path.ends_with(".ur") && !path.ends_with(".urs") {
            let msg = cli_diagnostic_text(
                DiagnosticId::CliUrFmtNotUrFile,
                vec![path.clone()],
                locale_for_paths,
            );
            cli_common::writeln_stderr_display(msg);
            all_ok = false;
            continue;
        }
        if !cli_common::file_exists(path) {
            let msg = cli_diagnostic_text(
                DiagnosticId::CliUrFmtFileMissing,
                vec![path.clone()],
                locale_for_paths,
            );
            cli_common::writeln_stderr_display(msg);
            all_ok = false;
            continue;
        }
        let Ok(original) = fs::read_to_string(path) else {
            let msg = cli_diagnostic_text(
                DiagnosticId::CliUrFmtReadFailed,
                vec![path.clone()],
                locale_for_paths,
            );
            cli_common::writeln_stderr_display(msg);
            all_ok = false;
            continue;
        };
        match ur::ur_format::format_source_path(path, &original, tab_width) {
            Ok(formatted) => {
                if formatted == original {
                    if check_mode {}
                } else if check_mode {
                    let msg = cli_diagnostic_text(
                        DiagnosticId::CliUrFmtCheckWouldChange,
                        vec![path.clone()],
                        locale_for_paths,
                    );
                    cli_common::writeln_stderr_display(msg);
                    all_ok = false;
                } else if let Err(write_error) = fs::write(path, &formatted) {
                    let msg = cli_diagnostic_text(
                        DiagnosticId::CliUrFmtWriteFailed,
                        vec![path.clone(), write_error.to_string()],
                        locale_for_paths,
                    );
                    cli_common::writeln_stderr_display(msg);
                    all_ok = false;
                }
            }
            Err(parse_errors) => {
                let header = cli_diagnostic_text(
                    DiagnosticId::CliUrFmtParseFailedHeader,
                    vec![path.clone()],
                    locale_for_paths,
                );
                cli_common::writeln_stderr_display(header);
                print_errors(&parse_errors, locale_for_paths);
                all_ok = false;
            }
        }
    }
    if all_ok {
        0
    } else {
        1
    }
}

/// Run [`fmt_command`] on argv after the executable, then exit with its status.
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let code = fmt_command(&args[1..]);
    process::exit(code);
}
