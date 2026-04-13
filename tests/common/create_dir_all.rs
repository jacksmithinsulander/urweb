//! Create directory trees for test fixtures with contextual panics on failure.

/// Create a directory tree for test fixtures with contextual panic text on failure.
pub fn create_dir_all(path: &std::path::Path, context: &str) {
    match std::fs::create_dir_all(path) {
        Ok(()) => {}
        Err(error) => panic!("{context} ({}): {error}", path.display()),
    }
}
