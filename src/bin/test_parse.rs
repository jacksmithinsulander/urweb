fn main() {
    let mut errors = ur::error_types::ErrorReporter::new();
    let result = ur::parse::parse_ur("test.ur", "val x = 1", &mut errors);
    println!("Errors: {:?}", errors.has_errors());
    match result {
        Some(file) => {
            println!("Parsed {} decls", file.len());
            for decl in &file {
                println!("  {:?}", decl.node);
            }
        }
        None => println!("Parse failed"),
    }
}
