//! ur-compile — Compile Ur/Web projects to native executables and emit **SQL** (Structured Query Language) DDL.
//!
//! Mentions elsewhere: Language Server Protocol helpers, compiler intermediate representation, Structured Query Language schema output,
//! and foreign function interface lines in `.urp` project files.
//!
//! **Style:** [README.md](../../README.md) Rust conventions when this file is edited.

use std::process;
use ur::cli_common;
use ur::settings::Settings;

const VERSION_STRING: &str = env!("CARGO_PKG_VERSION");

/// Print usage: shared orchestrator lines plus compiler-specific flags.
///
/// `-dbms` picks the database engine; `-tc` stops after type checking (no code generation).
fn print_usage(_settings: &Settings) {
    let _name = std::env::args()
        .next()
        .unwrap_or_else(|| "ur-compile".into());
    println!("usage:");
    for line in cli_common::UR_ORCHESTRATOR_USAGE_LINES {
        println!("{}", line);
    }
    println!("Standard options: -h, --help; -V, --version; -o, --output=FILE");
    println!("Supported flags include:");
    println!("  -h, -help, --help    print this overview");
    println!("  -V, -version         print version and exit");
    println!("  -ccompiler <prog>    set C compiler");
    println!(
        "  -dbms <engine>       select database engine [sqlite|mysql|postgres|persy|rocksdb|ndb|tigerbeetle]"
    );
    println!("  -db <connstr>        database connection string");
    println!("  -prefix <prefix>     URL prefix");
    println!("  -sql <file>          output SQL DDL to <file>");
    println!("  -o, -output <file>    output executable to <file> (or --output=FILE)");
    println!("  -tc                  stop after type checking");
    println!("  -debug               save intermediate C files");
    println!(
        "  -v, -vv, … -vvvvv   verbosity (Foundry-style; stderr tracing via `tracing`, max 5)"
    );
    println!("  -verbose             legacy alias for a higher default verbosity (-vv)");
    println!("  -timing              print coarse phase wall times on stderr");
    println!(
        "  RUST_LOG             optional `tracing-subscriber` filter (overrides default `ur=…`)"
    );
    println!("  -iflow               run information-flow analysis");
    println!("  -limit <class> <n>   set resource limit");
    println!("  -startLspServer      run ur-lsp (Language Server Protocol on stdio)");
    println!("  -moduleOf <file>     print module name of <file>");
}

/// Parse `ur-compile` arguments and run the full pipeline through C output and Structured Query Language artifacts when requested.
///
/// `args` is argv after the program name. Returns `0` on success (including type-check-only mode), non-zero on diagnostics or input/output failure.
/// Updates [`Settings`] from flags, then calls [`ur::compiler::compile`].
pub fn run_compiler_args(args: &[String]) -> i32 {
    let mut settings = Settings::new();
    let mut project_file: Option<String> = None;
    let mut _tc_only = false;
    let mut _dump_source = false;
    let mut _do_iflow = false;
    let mut _partial_build: Option<String> = None;
    let mut demo_prefix: Option<String> = None;
    let mut demo_guided = false;

    let mut args_iter = args.iter();
    while let Some(arg) = args_iter.next() {
        let raw = arg.trim_start_matches('-');
        let (flag, opt_val) = if let Some(eq) = raw.find('=') {
            let (f, v) = raw.split_at(eq);
            (f, Some(v[1..].to_string()))
        } else {
            (raw, None)
        };
        match flag {
            "help" | "h" => {
                print_usage(&settings);
                return 0;
            }
            "version" | "V" => {
                println!("{}", VERSION_STRING);
                return 0;
            }
            "numeric-version" => {
                println!("{}", VERSION_STRING);
                return 0;
            }
            "print-ccompiler" => {
                println!("{}", settings.config_c_compiler);
                return 0;
            }
            "print-cinclude" => {
                println!("{}", settings.config_include);
                return 0;
            }
            "ccompiler" => {
                if let Some(cc) = opt_val.or_else(|| args_iter.next().cloned()) {
                    settings.config_c_compiler = cc;
                }
            }
            "protocol" => {
                if let Some(p) = opt_val.or_else(|| args_iter.next().cloned()) {
                    settings.protocol = p;
                }
            }
            "prefix" => {
                if let Some(p) = opt_val.or_else(|| args_iter.next().cloned()) {
                    settings.set_url_prefix(&p);
                }
            }
            "db" => {
                if let Some(db) = opt_val.or_else(|| args_iter.next().cloned()) {
                    settings.dbstring = Some(db);
                }
            }
            "dbms" => {
                if let Some(db) = opt_val.or_else(|| args_iter.next().cloned()) {
                    if let Err(e) = ur::db::set_backend_from_cli_token(&mut settings, &db) {
                        eprintln!("error: {}", e);
                        return 1;
                    }
                }
            }
            "debug" => {
                settings.debug = true;
            }
            "verbose" => {
                settings.verbosity = settings
                    .verbosity
                    .clamp(2, ur::compiler_tracing::MAX_COMPILER_VERBOSITY);
            }
            "timing" => {
                settings.emit_phase_timing = true;
            }
            "tc" => {
                _tc_only = true;
            }
            "dumpSource" => {
                _dump_source = true;
            }
            "output" | "o" => {
                if let Some(f) = opt_val.or_else(|| args_iter.next().cloned()) {
                    settings.exe = Some(f);
                }
            }
            "sql" => {
                if let Some(f) = opt_val.or_else(|| args_iter.next().cloned()) {
                    settings.sql = Some(f);
                }
            }
            "endpoints" => {
                if let Some(f) = opt_val.or_else(|| args_iter.next().cloned()) {
                    settings.endpoints = Some(f);
                }
            }
            "static" => {
                settings.static_linking = true;
            }
            "boot" => {
                settings.boot_linking = true;
            }
            "sigfile" => {
                if let Some(f) = opt_val.or_else(|| args_iter.next().cloned()) {
                    settings.sig_file = Some(f);
                }
            }
            "iflow" => {
                _do_iflow = true;
            }
            "sqlcache" => {
                settings.sqlcache = true;
            }
            "disablesqlstructurecheck" => {
                settings.disable_sql_structure_check = true;
            }
            "moduleOf" => {
                if let Some(f) = opt_val.or_else(|| args_iter.next().cloned()) {
                    println!("{}", ur::compiler::module_of(&f));
                }
                return 0;
            }
            "limit" => {
                let class = args_iter.next().cloned().unwrap_or_default();
                let num_str = args_iter.next().cloned().unwrap_or_default();
                match num_str.parse::<i32>() {
                    Ok(n) if cli_common::is_valid_limit(n) => {
                        if let Err(e) = settings.add_limit(&class, n) {
                            eprintln!("error: {}", e);
                            return 1;
                        }
                    }
                    _ => {
                        eprintln!("error: invalid limit number '{}'", num_str);
                        return 1;
                    }
                }
            }
            "demo" => {
                if let Some(p) = opt_val.or_else(|| args_iter.next().cloned()) {
                    demo_prefix = Some(p);
                    demo_guided = false;
                }
            }
            "guided-demo" => {
                if let Some(p) = opt_val.or_else(|| args_iter.next().cloned()) {
                    demo_prefix = Some(p);
                    demo_guided = true;
                }
            }
            // Ignored flags (SML compiler compat)
            "noEmacs" => {}
            "partialBuild" => {
                if let Some(m) = opt_val.or_else(|| args_iter.next().cloned()) {
                    _partial_build = Some(m);
                }
            }
            "startLspServer" => {
                return cli_common::exec_peer_bin("ur-lsp", &[]);
            }
            _ if !flag.is_empty() && flag.len() <= 5 && flag.chars().all(|c| c == 'v') => {
                cli_common::apply_verbosity_v_flag(&mut settings, flag);
            }
            "path" => {
                let _ = args_iter.next();
                let _ = args_iter.next();
            }
            "root" => {
                let _ = args_iter.next();
                let _ = args_iter.next();
            }
            other => {
                if cli_common::is_unknown_compiler_flag(other, arg) {
                    eprintln!("error: unknown flag -{}", other);
                    return 1;
                }
                project_file = Some(arg.clone());
            }
        }
    }

    // Demo mode: -demo <prefix> <dirname>
    if let Some(prefix) = demo_prefix {
        let dirname = match project_file {
            Some(p) => p,
            None => {
                eprintln!("error: -demo requires a directory argument");
                return 1;
            }
        };
        match ur::demo::make(&prefix, &dirname, &mut settings, demo_guided) {
            Ok(true) => return 0,
            Ok(false) => return 1,
            Err(e) => {
                eprintln!("{}", e);
                return 1;
            }
        }
    }

    let project = match project_file {
        Some(p) => p,
        None => {
            eprintln!("error: no project specified, see -help");
            return 1;
        }
    };

    let urp_path = std::path::Path::new(&project);
    match ur::compiler::compile(urp_path, &mut settings).into_result() {
        Ok(_exe) => 0,
        Err(e) => {
            eprintln!("{}", e);
            1
        }
    }
}

/// Spawn a worker thread with a large stack, run [`run_compiler_args`], then exit with its status.
///
/// Stack size is [`ur::COMPILE_THREAD_STACK_BYTES`] so deep elaboration (type inference) does not overflow the default thread stack.
fn main() {
    let args: Vec<String> = std::env::args().collect();
    // Run in a thread with 64MB stack to handle deep elaboration recursion.
    let worker = match std::thread::Builder::new()
        .stack_size(ur::COMPILE_THREAD_STACK_BYTES)
        .spawn(move || run_compiler_args(&args[1..]))
    {
        Ok(h) => h,
        Err(e) => {
            eprintln!(
                "Could not start the compiler worker thread (stack size {} bytes): {e}\n\
                 Try closing other heavy processes or raising the stack limit.",
                ur::COMPILE_THREAD_STACK_BYTES
            );
            process::exit(1);
        }
    };
    let code = match worker.join() {
        Ok(exit) => exit,
        Err(_) => {
            eprintln!(
                "The compiler worker thread panicked. This is usually a compiler bug.\n\
                 If you can reproduce it with a small project, please report it."
            );
            1
        }
    };
    process::exit(code);
}
