//! Compiler intrinsics and canonical FFI spellings shared across passes.
//!
//! Web-specific behavior should register here (or in future generated tables) instead of
//! duplicating `"Basis"` string literals across the codebase.

pub mod web_ffi;
