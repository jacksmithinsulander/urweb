/// Normalize LALRPOP output so `clippy` stays clean without crate-level lint suppressions.
fn postprocess_grammar_rs(path: &std::path::Path) {
    let Ok(mut s) = std::fs::read_to_string(path) else {
        return;
    };

    // `clippy::empty_line_after_outer_attr`: lalrpop can insert an extra newline after allow attrs.
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
    // Nested modules in the generated file use `super::` incorrectly for this path.
    s = s.replace(
        "super::GrammarConLamTriple",
        "crate::parse::GrammarConLamTriple",
    );
    // `clippy::explicit_auto_deref`
    s = s.replace("(*rest).node", "rest.node");

    let _ = std::fs::write(path, s);
}

fn main() {
    // Always generate the parser from the LALRPOP grammar. Conflicts are hard
    // errors (no yacc-style default resolution) — keep the CFG LangSec-strict.
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
