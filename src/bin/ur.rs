//! Ur/Web command-line orchestrator.
//!
//! Dispatches subcommands (`build`, `new`, `fmt`, …) to small binaries: `ur-compile` (compiler driver), `ur-fmt` (formatter), `ur-new` (scaffold).
//!
//! Style-related paths sometimes use Sassy CSS (“scss”) and output Cascading Style Sheets; builds emit Structured Query Language where configured.
//! Project configuration is strict `ur.toml` (Tom's Obvious, Minimal Language), not legacy `urweb.toml`.

use std::process;
use ur::cli_common;

/// Implement `ur build`: read the manifest, optionally run Sass, then invoke the compiler.
///
/// Builds argv for [`cli_common::exec_peer_bin`] with `ur-compile`. Flag `-dbms` names the database engine (for example `sqlite`);
/// `-db` supplies the connection string for local `.db` files in the default application layout.
///
/// Returns `0` on success, `1` on manifest, stylesheet, or compiler failure (same exit code as the peer binary).
///
/// `verbosity_forward` — leading `-v` / `-vv` / `-verbose` tokens from `ur build` to pass through to `ur-compile`.
fn build_project(verbosity_forward: &[String]) -> i32 {
    // Load strict project manifest from the current working directory.
    let cfg = match cli_common::load_ur_manifest_cwd() {
        Ok(c) => c, // Parsed `ur.toml` is valid.
        Err(e) => {
            // Surface manifest errors to the user and abort without compiling.
            eprintln!("{}", e);
            return 1;
        }
    };
    // Applications and libraries must declare a non-empty entry module in `[build]`.
    if let Err(e) = cli_common::require_manifest_entry(&cfg) {
        eprintln!("{}", e);
        return 1;
    }

    // Fields used to build the `ur-compile` argument list.
    let kind = cfg.package.kind.as_str(); // `"app"` or `"lib"`.
    let entry = cfg.build.entry.as_str(); // Module stem (matches `entry.ur`).
    let db = cfg.build.db.as_str(); // Database engine name for `-dbms`.
                                    // Reject unknown engines early so the user sees a clear manifest error.
    if let Err(e) = ur::db::validate_manifest_db_engine(db) {
        eprintln!("error: ur.toml [build].db: {}", e);
        return 1;
    }
    let cc = cfg.build.ccompiler.as_str(); // Optional C compiler override.
    let is_lib = cli_common::is_lib_project(kind); // Libraries type-check only (`-tc`).
    let boot = cfg.build.boot; // Static/bootstrapped link mode when true.
    let scss = cfg.style.as_ref().and_then(|s| s.scss.as_deref()); // Optional SCSS source path.
    let css = cfg.style.as_ref().and_then(|s| s.css.as_deref()); // Matching CSS output path.

    // When both style paths exist and a Sass implementation is available, regenerate CSS before compile.
    if let (Some(scss_path), Some(css_path)) = (scss, css) {
        if cli_common::has_sass_or_sassc() {
            // Prefer `sass` (Dart Sass) when `which sass` succeeds.
            let has_sass = std::process::Command::new("which")
                .arg("sass")
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .status()
                .is_ok_and(|s| s.success());
            println!("  Compiling SCSS...");
            // Sass CLI expects `input:output` for a single build command.
            let sass_arg = format!("{}:{}", scss_path, css_path);
            let status = if has_sass {
                std::process::Command::new("sass")
                    .args([sass_arg.as_str(), "--no-source-map", "--style=expanded"])
                    .status()
            } else {
                // Fall back to `sassc` (libsass wrapper) with separate input and output paths.
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

    // Inform the user whether we emit a full app binary or stop after type-check.
    println!(
        "  {} {}...",
        if is_lib { "Type-checking" } else { "Building" },
        entry
    );

    // Assemble `ur-compile` argv: optional `-ccompiler`, optional `-boot`, then project-specific tail.
    let mut args: Vec<String> = vec![];
    if cli_common::should_add_ccompiler(cc) {
        args.extend(["-ccompiler".to_string(), cc.to_string()]);
    }
    if boot {
        args.push("-boot".to_string());
    }
    if is_lib {
        // Library projects only run the compiler through type-checking.
        args.extend(["-tc".to_string(), entry.to_string()]);
    } else {
        // Application projects pass database and SQL output paths inferred from the entry name.
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

    args.extend(verbosity_forward.iter().cloned());
    // Delegate to the real compiler binary on `PATH`.
    cli_common::exec_peer_bin("ur-compile", &args)
}

/// Print the built-in subcommand summary to standard output.
///
/// Lines come from [`cli_common::UR_ORCHESTRATOR_USAGE_LINES`]. Compiler flags are documented via `ur-compile -help`.
fn print_usage() {
    println!("usage:");
    for line in cli_common::UR_ORCHESTRATOR_USAGE_LINES {
        println!("{}", line);
    }
    println!();
    println!("Run 'ur -help' for compiler flag help (via ur-compile).");
}

/// Dispatch argv after the program name: run a helper binary or treat the tail as a compiler invocation.
///
/// `args` is the command-line slice without `argv[0]`; the first token picks the subcommand.
/// Returns the child exit status, or `1` for usage errors. Unknown first tokens are forwarded to `ur-compile` (legacy `ur Project` style).
fn dispatch(args: &[String]) -> i32 {
    match args.first().map(|s| s.as_str()) {
        None => {
            // No subcommand: print minimal usage on stderr.
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
        Some("build") => {
            let verbosity = cli_common::leading_build_verbosity_flags(&args[1..]);
            build_project(&verbosity)
        }
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
            // Treat as compiler invocation: forward full argv tail unchanged.
            let forwarded: Vec<String> = args.to_vec();
            cli_common::exec_peer_bin("ur-compile", &forwarded)
        }
    }
}

/// Program entry: forwards `std::env::args()` minus the executable path to [`dispatch`], then exits with that status.
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let code = dispatch(&args[1..]);
    process::exit(code);
}
