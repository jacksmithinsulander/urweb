fn main() {
    match ur::parse::basis_urs_preprocessed_window(38564, 200, 100) {
        Ok(ctx) => println!("Context: {:?}", ctx),
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(1);
        }
    }
}
