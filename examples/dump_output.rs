//! Dump C and SQL output from the compiler without linking.
//! Used by scripts/compare-compilers.sh to compare Rust vs ML compiler output.
//!
//! Usage: cargo run --example dump_output -- <path-to.urp> <output.c> <output.sql>

use std::env;
use std::fs;
use std::path::Path;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 4 {
        eprintln!("usage: dump_output <path-to.urp> <output.c> <output.sql>");
        std::process::exit(1);
    }
    let urp_path = Path::new(&args[1]);
    let c_out = &args[2];
    let sql_out = &args[3];

    let project_dir = urp_path.parent().unwrap_or_else(|| Path::new("."));
    if let Err(e) = env::set_current_dir(project_dir) {
        eprintln!("error: could not chdir to {}: {}", project_dir.display(), e);
        std::process::exit(1);
    }

    let mut settings = ur::settings::Settings {
        db_backend: Some(ur::db::ProjectDb::sqlite()),
        boot_linking: true,
        ..Default::default()
    };

    match ur::compiler::compile_to_outputs(urp_path, &mut settings) {
        Ok((c_code, sql_ddl)) => {
            fs::write(c_out, c_code).expect("write C output");
            fs::write(sql_out, sql_ddl).expect("write SQL output");
        }
        Err(e) => {
            eprintln!("error: compile_to_outputs failed: {}", e);
            std::process::exit(1);
        }
    }
}
