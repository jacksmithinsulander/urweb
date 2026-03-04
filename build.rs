fn main() {
    // Only run lalrpop if explicitly requested (set URWEB_GEN_PARSER=1).
    // During Session 1 the grammar skeleton is not yet complete; later sessions
    // will enable this unconditionally.
    if std::env::var("URWEB_GEN_PARSER").is_ok() {
        lalrpop::Configuration::new()
            .use_cargo_dir_conventions()
            .process_file("src/parse/grammar.lalrpop")
            .unwrap();
    }
}
