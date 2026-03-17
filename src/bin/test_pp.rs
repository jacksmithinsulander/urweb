fn main() {
    let src = std::fs::read_to_string("lib/ur/basis.urs").unwrap();
    let preprocessed = ur::parse::preprocess_urs(&src);
    let pos = 38564usize;
    let start = pos.saturating_sub(200);
    let end = (pos + 100).min(preprocessed.len());
    println!("Context: {:?}", &preprocessed[start..end]);
}
