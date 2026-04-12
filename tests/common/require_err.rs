//! Unwrap the error side of a `Result` in tests with a contextual panic on unexpected success.

/// Unwrap the error side of a `Result` in tests with a contextual panic on unexpected success.
pub fn require_err<T, E>(result: Result<T, E>, context: &str) -> E {
    match result {
        Ok(_) => panic!("{context}: expected Err(..), got Ok(..)"),
        Err(error) => error,
    }
}
