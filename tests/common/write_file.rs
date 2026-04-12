//! Write test fixture files with contextual panics on failure.

/// Write one test fixture file with contextual panic text on failure.
pub fn write_file(path: &std::path::Path, contents: impl AsRef<[u8]>, context: &str) {
    match std::fs::write(path, contents) {
        Ok(()) => {}
        Err(error) => panic!("{context} ({}): {error}", path.display()),
    }
}
