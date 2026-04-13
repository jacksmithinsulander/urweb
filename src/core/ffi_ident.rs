//! Foreign function interface identity: module name plus symbol name.
//!
//! Core IR uses [`FfiIdent`] for simple `(module, name)` references in [`crate::core::Constructor::Ffi`],
//! [`crate::core::Expression::Ffi`], and [`crate::core::Expression::FfiApp`] so construction and comparison
//! stay explicit. Richer FFI pattern shapes remain on [`crate::core::PatternConstructor::Ffi`].

/// Module and symbol name for a Core-level FFI reference (types, values, or calls).
///
/// Strings are owned so passes may move, hash, or emit C without borrowing the whole AST.
/// Values originate from the compiler pipeline (corify / lowering), not from unchecked editor text at this IR.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FfiIdent {
    /// FFI module path segment (for example `Basis`).
    pub module: String,
    /// Symbol within the module (for example `int` or `getCookie`).
    pub name: String,
}

impl FfiIdent {
    /// Build an FFI identity from owned module and name strings.
    ///
    /// # Arguments
    ///
    /// * `module` — Module path segment.
    /// * `name` — Symbol name within that module.
    ///
    /// # Returns
    ///
    /// A new [`FfiIdent`].
    pub fn new(module: String, name: String) -> Self {
        FfiIdent { module, name }
    }

    /// Borrow module and name as `str` slices for comparisons and formatting.
    ///
    /// # Returns
    ///
    /// `(&module, &name)` for pattern-style checks without allocating.
    pub fn as_str_pair(&self) -> (&str, &str) {
        (self.module.as_str(), self.name.as_str())
    }
}

impl From<FfiIdent> for (String, String) {
    /// Convert back to the legacy pair form for settings or glue that expects `(String, String)`.
    fn from(value: FfiIdent) -> Self {
        (value.module, value.name)
    }
}

impl From<(String, String)> for FfiIdent {
    /// Wrap a `(module, name)` pair from explicit lowering.
    fn from(pair: (String, String)) -> Self {
        FfiIdent::new(pair.0, pair.1)
    }
}
