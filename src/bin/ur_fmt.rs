//! ur-fmt — Format Ur/Web source files.

use std::process;
use ur::cli_common;

fn fmt_command(args: &[String]) -> i32 {
    let mut _check_mode = false;
    let mut _width: u32 = 80;
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
                println!("  If no files: format all .ur/.urs in project (from ur.toml)");
                println!("  Otherwise: format the given files.");
                println!("  -check, --check: check only; exit 1 if would reformat (CI mode)");
                println!("  -w N, --width N, --width=N: line width (default 80)");
                return 0;
            }
            "-check" | "--check" => {
                _check_mode = true;
            }
            "-w" | "--width" => {
                if let Some(n) = opt_val
                    .or_else(|| args_iter.next().cloned())
                    .and_then(|s| s.parse::<u32>().ok())
                {
                    _width = n;
                }
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
        if let Ok(content) = std::fs::read_to_string(&urp_path) {
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
                if std::path::Path::new(&ur).exists() {
                    files.push(ur);
                }
                if std::path::Path::new(&urs).exists() {
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
        eprintln!("note: formatter not yet implemented; {} skipped", f);
    }
    if all_ok {
        0
    } else {
        1
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let code = fmt_command(&args[1..]);
    process::exit(code);
}
