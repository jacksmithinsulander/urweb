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

fn main() {
    println!("cargo::rustc-check-cfg=cfg(generated_parser)");
    if let Err(e) = lalrpop::Configuration::new()
        .use_cargo_dir_conventions()
        .process_file("src/parse/grammar.lalrpop")
    {
        eprintln!(
            "lalrpop failed to build the parser from src/parse/grammar.lalrpop:\n{e}\n\
             Fix grammar conflicts or errors, then run cargo build again."
        );
        std::process::exit(1);
    }

    postprocess_grammar_rs(
        &std::path::PathBuf::from(std::env::var_os("OUT_DIR").unwrap()).join("parse/grammar.rs"),
    );

    println!("cargo:rustc-cfg=generated_parser");
}
