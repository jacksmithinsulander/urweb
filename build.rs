fn main() {
    // Always generate the parser from the LALRPOP grammar.
    println!("cargo::rustc-check-cfg=cfg(generated_parser)");
    lalrpop::Configuration::new()
        .use_cargo_dir_conventions()
        .process_file("src/parse/grammar.lalrpop")
        .unwrap();
    println!("cargo:rustc-cfg=generated_parser");
}
