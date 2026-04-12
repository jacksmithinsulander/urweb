//! Temporary directories for integration tests.

/// Create an isolated temp directory for a test, panicking with context on failure.
pub fn tempdir(context: &str) -> tempfile::TempDir {
    tempfile::tempdir().unwrap_or_else(|error| panic!("{context}: {error}"))
}
