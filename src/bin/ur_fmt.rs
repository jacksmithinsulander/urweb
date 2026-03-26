//! Format `.ur` and `.urs` sources after parsing (invalid programs are not rewritten silently).
//!
//! The formatter builds an abstract syntax tree, then pretty-prints. **Style:** [README.md](../../README.md) when edited.

use std::fs;
use std::path::Path;
use std::process;
use ur::cli_common;
use ur::error_types::CompileError;
use ur::ur_format::format_source_path;

/// Print each [`CompileError`] to standard error.
fn print_errors(errors: &[CompileError]) {
    for e in errors {
        eprintln!("{e}");
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
    while let Some(arg) = args_iter.next() {
        let (flag, opt_val) = if let Some(eq) = arg.find('=') {
            let (f, v) = arg.split_at(eq);
            (f, Some(v[1..].to_string()))
        } else {
            (arg.as_str(), None)
        };
        match flag {
            "-help" | "--help" | "-h" => {
                println!("ur-fmt [options] [files...]");
                println!(
                    "  If no files: format all .ur/.urs in project (from .urp via ur.toml entry)."
                );
                println!("  Otherwise: format the given files.");
                println!("  -check, --check: exit 1 if any file would change");
                println!("  -t N, --tab N, --tab=N: tab width for expansion (default 4)");
                println!(
                    "  -w N, --width N: accepted for compatibility (layout is not wrapped yet)"
                );
                return 0;
            }
            "-check" | "--check" => {
                check_mode = true;
            }
            "-t" | "--tab" => {
                if let Some(n) = opt_val
                    .or_else(|| args_iter.next().cloned())
                    .and_then(|s| s.parse::<usize>().ok())
                {
                    tab_width = n;
                }
            }
            "-w" | "--width" => {
                let _ = opt_val
                    .or_else(|| args_iter.next().cloned())
                    .and_then(|s| s.parse::<u32>().ok());
            }
            f if cli_common::is_file_arg(f) => {
                files.push(f.to_string());
            }
            other => {
                eprintln!("warning: unknown fmt flag: {}", other);
            }
        }
    }

    if files.is_empty() {
        let cfg = match cli_common::load_ur_manifest_cwd_for_fmt_discovery() {
            Ok(c) => c,
            Err(e) => {
                eprintln!("{}", e);
                return 1;
            }
        };
        if let Err(e) = cli_common::require_manifest_entry(&cfg) {
            eprintln!("{}", e);
            return 1;
        }
        let entry = cfg.build.entry.as_str();
        let urp_path = format!("{}.urp", entry);
        if !cli_common::file_exists(&urp_path) {
            eprintln!("error: project .urp not found: {}", urp_path);
            return 1;
        }
        if let Ok(content) = fs::read_to_string(&urp_path) {
            for line in content.lines() {
                let line = line.trim();
                if cli_common::should_skip_urp_line(line) {
                    continue;
                }
                if cli_common::URP_DIRECTIVE_KEYWORDS
                    .iter()
                    .any(|kw| line.starts_with(kw))
                {
                    continue;
                }
                let ur = format!("{}.ur", line);
                let urs = format!("{}.urs", line);
                if Path::new(&ur).exists() {
                    files.push(ur);
                }
                if Path::new(&urs).exists() {
                    files.push(urs);
                }
            }
        }
        if files.is_empty() {
            println!("no .ur or .urs files found");
            return 0;
        }
    }

    let mut all_ok = true;
    for f in &files {
        if !f.ends_with(".ur") && !f.ends_with(".urs") {
            eprintln!("error: {} is not a .ur or .urs file", f);
            all_ok = false;
            continue;
        }
        if !cli_common::file_exists(f) {
            eprintln!("error: {} not found", f);
            all_ok = false;
            continue;
        }
        let Ok(orig) = fs::read_to_string(f) else {
            eprintln!("error: cannot read {}", f);
            all_ok = false;
            continue;
        };
        match format_source_path(f, &orig, tab_width) {
            Ok(formatted) => {
                if formatted == orig {
                    if check_mode {
                        // unchanged
                    }
                } else if check_mode {
                    eprintln!("check failed (would reformat): {}", f);
                    all_ok = false;
                } else if let Err(e) = fs::write(f, &formatted) {
                    eprintln!("error: write {}: {e}", f);
                    all_ok = false;
                }
            }
            Err(errs) => {
                eprintln!("error: cannot format {} (parse failed)", f);
                print_errors(&errs);
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
