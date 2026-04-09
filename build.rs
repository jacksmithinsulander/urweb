//! Build script: compile `grammar.lalrpop` and normalize the emitted Rust so the included parser
//! stays buildable under strict `clippy` for issues we can fix mechanically.
//!
//! LALRPOP’s generated `grammar.rs` still carries the compiler attributes it emits (`#[allow(...)]`
//! on parser submodules). Those are generator output, not project `src/**/*.rs` suppressions.

/// Collapse stray blank lines after outer attributes and apply small mechanical fixes LALRPOP does not emit.
fn postprocess_grammar_rs(path: &std::path::Path) {
    let Ok(mut s) = std::fs::read_to_string(path) else {
        return;
    };

    // `clippy::empty_line_after_outer_attr`: lalrpop can insert an extra newline after `#[rustfmt::skip]`.
    for (pat, rep) in [
        (
            "#![allow(clippy::type_complexity, dead_code)]\r\n\r\n",
            "#![allow(clippy::type_complexity, dead_code)]\r\n",
        ),
        (
            "#![allow(clippy::type_complexity, dead_code)]\n\n",
            "#![allow(clippy::type_complexity, dead_code)]\n",
        ),
        (
            "#[allow(clippy::type_complexity, dead_code)]\r\n\r\n",
            "#[allow(clippy::type_complexity, dead_code)]\r\n",
        ),
        (
            "#[allow(clippy::type_complexity, dead_code)]\n\n",
            "#[allow(clippy::type_complexity, dead_code)]\n",
        ),
    ] {
        s = s.replace(pat, rep);
    }

    // `clippy::type_complexity`: repeated reduce stack tuples → alias in `parse` module.
    s = s.replace(
        "(usize, Vec<(String, Option<LocCon>, LocExp)>, usize)",
        "crate::parse::GrammarConLamTriple",
    );
    s = s.replace(
        "super::GrammarConLamTriple",
        "crate::parse::GrammarConLamTriple",
    );
    s = s.replace("(*rest).node", "rest.node");

    let _ = std::fs::write(path, s);
}

/// Run LALRPOP on `src/parse/grammar.lalrpop`, normalize emitted Rust, and print `cargo:` lines for cfg/output.
fn main() {
    use std::io::Write as _; // `writeln!` to stderr without `eprintln!`.

    println!("cargo::rustc-check-cfg=cfg(generated_parser)"); // Declare `generated_parser` for `cfg` checking.
    if let Err(lalrpop_error) = lalrpop::Configuration::new() // Parser generation from the LALRPOP grammar file.
        .use_cargo_dir_conventions()
        .process_file("src/parse/grammar.lalrpop")
    {
        let mut lock = std::io::stderr().lock(); // Single-writer lock for the failure message.
        let _ =
            writeln!( // Surface LALRPOP errors on stderr before exiting.
            lock,
            "lalrpop failed to build the parser from src/parse/grammar.lalrpop:\n{lalrpop_error}\n\
             Fix grammar conflicts or errors, then run cargo build again."
        );
        std::process::exit(1); // Signal failure to Cargo.
    }

    // `var_os` returns `None` only when Cargo does not set `OUT_DIR`, which cannot happen during a
    // normal build; using `let Some(...)` with an `else` branch avoids a panic and keeps clippy happy.
    let Some(out_dir) = std::env::var_os("OUT_DIR") else {
        let mut lock = std::io::stderr().lock(); // Single-writer lock for the warning message.
        let _ = writeln!(
            lock,
            "build.rs: OUT_DIR not set; skipping grammar postprocessing."
        );
        return;
    };
    postprocess_grammar_rs(&std::path::PathBuf::from(out_dir).join("parse/grammar.rs")); // apply LALRPOP output cleanup

    println!("cargo:rustc-cfg=generated_parser");
}
