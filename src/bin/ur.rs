//! ur — Ur/Web orchestrator; dispatches to ur-compile, ur-fmt, ur-new, etc.

use std::process;
use ur::cli_common;

fn build_project() -> i32 {
    let cfg = match cli_common::load_ur_manifest_cwd() {
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

    let kind = cfg.package.kind.as_str();
    let entry = cfg.build.entry.as_str();
    let db = cfg.build.db.as_str();
    if let Err(e) = ur::db::validate_manifest_db_engine(db) {
        eprintln!("error: ur.toml [build].db: {}", e);
        return 1;
    }
    let cc = cfg.build.ccompiler.as_str();
    let is_lib = cli_common::is_lib_project(kind);
    let boot = cfg.build.boot;
    let scss = cfg.style.as_ref().and_then(|s| s.scss.as_deref());
    let css = cfg.style.as_ref().and_then(|s| s.css.as_deref());

    // Compile SCSS → CSS if configured
    if let (Some(scss_path), Some(css_path)) = (scss, css) {
        if cli_common::has_sass_or_sassc() {
            let has_sass = std::process::Command::new("which")
                .arg("sass")
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .status()
                .is_ok_and(|s| s.success());
            println!("  Compiling SCSS...");
            let sass_arg = format!("{}:{}", scss_path, css_path);
            let status = if has_sass {
                std::process::Command::new("sass")
                    .args([sass_arg.as_str(), "--no-source-map", "--style=expanded"])
                    .status()
            } else {
                std::process::Command::new("sassc")
                    .args([scss_path, css_path])
                    .status()
            };
            if !cli_common::command_succeeded(&status) {
                eprintln!("error: SCSS compilation failed");
                return 1;
            }
        }
    }

    println!(
        "  {} {}...",
        if is_lib { "Type-checking" } else { "Building" },
        entry
    );

    let mut args: Vec<String> = vec![];
    if cli_common::should_add_ccompiler(cc) {
        args.extend(["-ccompiler".to_string(), cc.to_string()]);
    }
    if boot {
        args.push("-boot".to_string());
    }
    if is_lib {
        args.extend(["-tc".to_string(), entry.to_string()]);
    } else {
        args.extend([
            "-dbms".to_string(),
            db.to_string(),
            "-db".to_string(),
            format!("{}.db", entry),
            "-sql".to_string(),
            format!("{}.sql", entry),
            entry.to_string(),
        ]);
    }

    cli_common::exec_peer_bin("ur-compile", &args)
}

fn print_usage() {
    println!("usage:");
    for line in cli_common::UR_ORCHESTRATOR_USAGE_LINES {
        println!("{}", line);
    }
    println!();
    println!("Run 'ur -help' for compiler flag help (via ur-compile).");
}

fn dispatch(args: &[String]) -> i32 {
    match args.first().map(|s| s.as_str()) {
        None => {
            eprintln!("usage: ur <command> [args...]");
            eprintln!("Run 'ur -help' for more information.");
            1
        }
        Some("-h") | Some("--help") => {
            print_usage();
            0
        }
        Some("new") => {
            let rest: Vec<String> = args[1..].to_vec();
            cli_common::exec_peer_bin("ur-new", &rest)
        }
        Some("build") => build_project(),
        Some("install") => {
            let rest: Vec<String> = args[1..].to_vec();
            cli_common::exec_peer_bin("ur-install", &rest)
        }
        Some("fmt") => {
            let rest: Vec<String> = args[1..].to_vec();
            cli_common::exec_peer_bin("ur-fmt", &rest)
        }
        Some("daemon") => {
            let rest: Vec<String> = args[1..].to_vec();
            cli_common::exec_peer_bin("ur-daemon", &rest)
        }
        Some("lsp") => cli_common::exec_peer_bin("ur-lsp", &[]),
        Some("debugger") => {
            let rest: Vec<String> = args[1..].to_vec();
            cli_common::exec_peer_bin("ur-debugger", &rest)
        }
        Some(_) => {
            let forwarded: Vec<String> = args.to_vec();
            cli_common::exec_peer_bin("ur-compile", &forwarded)
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let code = dispatch(&args[1..]);
    process::exit(code);
}
