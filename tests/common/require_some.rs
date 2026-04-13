//! Unwrap an `Option` in tests with a contextual panic when the value is missing.

/// Unwrap an `Option` in tests with a contextual panic when the value is missing.
pub fn require_some<T>(value: Option<T>, context: &str) -> T {
    match value {
        Some(inner) => inner,
        None => panic!("{context}: expected Some(..), got None"),
    }
}
