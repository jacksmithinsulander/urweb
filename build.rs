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

    // LALRPOP emits a blank line after `#![allow(...)]` on the fallback `ToTriple`
    // trait; clippy::empty_line_after_outer_attr flags that. Collapse to one newline.
    let grammar_rs =
        std::path::PathBuf::from(std::env::var_os("OUT_DIR").unwrap()).join("parse/grammar.rs");
    if let Ok(raw) = std::fs::read_to_string(&grammar_rs) {
        let fixed = raw.replace(
            "#![allow(clippy::type_complexity, dead_code)]\n\npub ",
            "#![allow(clippy::type_complexity, dead_code)]\npub ",
        );
        if fixed != raw {
            let _ = std::fs::write(&grammar_rs, fixed);
        }
    }

    println!("cargo:rustc-cfg=generated_parser");
}
