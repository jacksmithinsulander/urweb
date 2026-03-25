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
    println!("cargo:rustc-cfg=generated_parser");
}
