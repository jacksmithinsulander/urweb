//! Datatype representation classification.
//!
//! Determines runtime representation from constructor shape:
//! - Enum: all nullary → integer tag
//! - Option: None + Some → nullable pointer
//! - Default: general → tagged struct

/// Classifies how a datatype is represented at runtime (mirrors `DatatypeKind`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DatatypeKind {
    /// All constructors are nullary — represented as an integer enum.
    Enum,
    /// Exactly one nullary constructor (`None`) and one unary (`Some`) — uses nullable pointer.
    Option,
    /// General case — uses a tagged struct.
    Default,
}
