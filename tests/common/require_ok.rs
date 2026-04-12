//! Unwrap a `Result` in tests with a contextual panic that keeps the original error visible.

/// Unwrap a `Result` in tests with a contextual panic that keeps the original error visible.
pub fn require_ok<T, E: std::fmt::Display>(result: Result<T, E>, context: &str) -> T {
    match result {
        Ok(value) => value,
        Err(error) => panic!("{context}: {error}"),
    }
}
