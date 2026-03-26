fn main() {
    let mut errors = ur::error_types::ErrorReporter::new();
    let n = ur::parse::parse_top_level_decl_count("test.ur", "val x = 1", &mut errors);
    println!("Errors: {:?}", errors.has_errors());
    match n {
        Some(c) => println!("Parsed {} decls", c),
        None => println!("Parse failed"),
    }
    let mut e2 = ur::error_types::ErrorReporter::new();
    let n2 = ur::parse::parse_top_level_decl_count("t.ur", "val a = 1\nval b = 2", &mut e2);
    match n2 {
        Some(c) => println!("two_decls: {}", c),
        None => println!("two_decls: parse failed"),
    }
}
