fn main() {
    let mut errors = ur::error_types::ErrorReporter::new();
    let n = ur::parse::smoke_parse_val_decl_count(&mut errors);
    println!("Errors: {:?}", errors.has_errors());
    match n {
        Some(c) => println!("Parsed {} decls", c),
        None => println!("Parse failed"),
    }
}
