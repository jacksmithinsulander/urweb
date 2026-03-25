//! ur — Ur/Web orchestrator; dispatches to ur-compile, ur-fmt, ur-new, etc.

use std::process;
use ur::cli_common;

fn build_project() -> i32 {
    let toml_path = "ur.toml";
    if !cli_common::file_exists(toml_path) {
        eprintln!(
            "error: ur.toml not found in current directory\n\
Run 'ur new <name>' to create a project, then 'cd <name> && ur build'"
        );
        return 1;
    }

    let toml_content = match std::fs::read_to_string(toml_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error reading ur.toml: {}", e);
            return 1;
        }
    };
    let cfg = match cli_common::parse_ur_toml_strict(&toml_content) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("error: ur.toml: {}", e);
            return 1;
        }
    };

    let kind = cfg.package.kind.as_str();
    let entry = cfg.build.entry.as_str();
    let db = cfg.build.db.as_str();
    let cc = cfg.build.ccompiler.as_str();
    let is_lib = cli_common::is_lib_project(kind);
    let boot = cfg.build.boot;
    let scss = cfg.style.as_ref().and_then(|s| s.scss.as_deref());
    let css = cfg.style.as_ref().and_then(|s| s.css.as_deref());

    if entry.is_empty() {
        eprintln!("error: ur.toml: [build] entry is required");
        return 1;
    }

    // Compile SCSS → CSS if configured
    if let (Some(scss_path), Some(css_path)) = (scss, css) {
        if cli_common::has_sass_or_sassc() {
            let has_sass = std::process::Command::new("which")
                .arg("sass")
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .status()
                .map_or(false, |s| s.success());
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

    let status = std::process::Command::new("ur-compile")
        .args(&args)
        .status();
    match status {
        Ok(s) => {
            if s.success() {
                0
            } else {
                s.code().unwrap_or(1)
            }
        }
        Err(_) => {
            eprintln!("error: ur-compile not found in PATH");
            1
        }
    }
}

fn print_usage() {
    println!("usage:");
    println!("  ur new <project-name>");
    println!("  ur new --lib <project-name>");
    println!("  ur build");
    println!("  ur fmt [options] [files...]");
    println!("  ur install author/repo");
    println!("  ur daemon [stop|start]");
    println!("  ur lsp");
    println!("  ur [flag ...] project-name");
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
            let status = std::process::Command::new("ur-new").args(&rest).status();
            match status {
                Ok(s) => s.code().unwrap_or(1),
                Err(_) => {
                    eprintln!("error: ur-new not found in PATH");
                    1
                }
            }
        }
        Some("build") => build_project(),
        Some("install") => {
            let rest: Vec<String> = args[1..].to_vec();
            let status = std::process::Command::new("ur-install")
                .args(&rest)
                .status();
            match status {
                Ok(s) => {
                    if s.success() {
                        0
                    } else {
                        s.code().unwrap_or(1)
                    }
                }
                Err(_) => {
                    eprintln!("error: ur-install not found in PATH");
                    1
                }
            }
        }
        Some("fmt") => {
            let rest: Vec<String> = args[1..].to_vec();
            let status = std::process::Command::new("ur-fmt").args(&rest).status();
            match status {
                Ok(s) => s.code().unwrap_or(1),
                Err(_) => {
                    eprintln!("error: ur-fmt not found in PATH");
                    1
                }
            }
        }
        Some("daemon") => {
            let rest: Vec<String> = args[1..].to_vec();
            let status = std::process::Command::new("ur-daemon").args(&rest).status();
            match status {
                Ok(s) => s.code().unwrap_or(1),
                Err(_) => {
                    eprintln!("error: ur-daemon not found in PATH");
                    1
                }
            }
        }
        Some("lsp") => {
            let status = std::process::Command::new("ur-lsp").status();
            match status {
                Ok(s) => s.code().unwrap_or(1),
                Err(_) => {
                    eprintln!("error: ur-lsp not found in PATH");
                    1
                }
            }
        }
        Some(_) => {
            // Compiler invocation: pass all args to ur-compile
            let status = std::process::Command::new("ur-compile").args(args).status();
            match status {
                Ok(s) => s.code().unwrap_or(1),
                Err(_) => {
                    eprintln!("error: ur-compile not found in PATH");
                    1
                }
            }
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let code = dispatch(&args[1..]);
    process::exit(code);
}
