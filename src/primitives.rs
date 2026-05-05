//! Primitive literals shared across compiler intermediate representations.
//!
//! [`Prim`] covers integers, floats, text, and characters; [`StringMode`] selects normal versus HTML-oriented escaping for code generation.
//! See [`Prim::to_c_literal`] and [`Prim::float_to_string`]; [`std::fmt::Display`] is used where run-time text is needed.
//!
//! Shapes follow Standard ML’s `Prim.t` from the reference compiler.

use std::fmt;

/// The minimum integer width required to hold a given literal value.
///
/// Used by code-generation passes (SQL DDL, FFI layers) to select the smallest concrete
/// integer type that can faithfully represent a compile-time–known integer constant.
/// Ur/Web's `int` type compiles to C `long long` (`i64`) uniformly, so `IntWidth` is not
/// used for the core C output — it is provided for SQL column-type selection and future
/// FFI interop where the target environment supports multiple widths.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum IntWidth {
    /// Fits in a signed 8-bit integer (`-128` to `127`).
    I8,
    /// Fits in a signed 16-bit integer (`-32 768` to `32 767`).
    I16,
    /// Fits in a signed 32-bit integer.
    I32,
    /// Requires a full signed 64-bit integer.
    I64,
}

impl IntWidth {
    /// Returns the C standard integer type name for this width.
    ///
    /// Suitable for use in generated C headers or SQL DDL (`INT8`, `SMALLINT`, …).
    pub fn c_type_name(self) -> &'static str {
        match self {
            IntWidth::I8 => "int8_t",   // narrowest — fits in a single byte
            IntWidth::I16 => "int16_t", // two-byte short
            IntWidth::I32 => "int32_t", // standard C int on most 32/64-bit platforms
            IntWidth::I64 => "int64_t", // Ur/Web's native `int` width
        }
    }

    /// Returns the SQL standard type name for this width.
    ///
    /// Useful when generating SQL `CREATE TABLE` DDL for columns whose values are
    /// known at compile time to fit within a smaller range.
    pub fn sql_type_name(self) -> &'static str {
        match self {
            IntWidth::I8 => "SMALLINT", // SQL has no standard INT8; SMALLINT is 2 bytes
            IntWidth::I16 => "SMALLINT", // 2-byte SQL integer
            IntWidth::I32 => "INTEGER", // 4-byte SQL integer
            IntWidth::I64 => "BIGINT",  // 8-byte SQL integer
        }
    }
}

/// The minimum unsigned integer width required to hold a given non-negative literal value.
///
/// Parallel to [`IntWidth`] for signed integers, but for the unsigned family (u8..u64).
/// Used when a numeric literal is known to be non-negative — it can be stored in the smallest
/// unsigned type, halving the required bit-width relative to the signed equivalent.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum UintWidth {
    /// Fits in an unsigned 8-bit integer (`0` to `255`).
    U8,
    /// Fits in an unsigned 16-bit integer (`0` to `65 535`).
    U16,
    /// Fits in an unsigned 32-bit integer (`0` to `4 294 967 295`).
    U32,
    /// Requires a full unsigned 64-bit integer.
    U64,
}

impl UintWidth {
    /// Returns the C standard unsigned integer type name for this width.
    ///
    /// Suitable for use in generated C headers or SQL DDL.
    pub fn c_type_name(self) -> &'static str {
        match self {
            UintWidth::U8 => "uint8_t",   // narrowest unsigned — one byte
            UintWidth::U16 => "uint16_t", // two-byte unsigned short
            UintWidth::U32 => "uint32_t", // four-byte unsigned int
            UintWidth::U64 => "uint64_t", // eight-byte unsigned long
        }
    }

    /// Returns the SQL standard type name for this unsigned width.
    ///
    /// SQL has no native unsigned types; the smallest signed type that can hold
    /// all values of this unsigned range is used.
    pub fn sql_type_name(self) -> &'static str {
        match self {
            UintWidth::U8 => "SMALLINT", // SQL SMALLINT (2 bytes signed) covers 0-255
            UintWidth::U16 => "INTEGER", // SQL INTEGER (4 bytes) covers 0-65535
            UintWidth::U32 => "BIGINT",  // SQL BIGINT (8 bytes) covers 0-4294967295
            UintWidth::U64 => "NUMERIC", // SQL NUMERIC (arbitrary precision) for full u64
        }
    }
}

/// Returns the minimum [`UintWidth`] that can hold the given unsigned 64-bit value.
///
/// # Examples
///
/// ```
/// use ur::primitives::{UintWidth, narrow_uint_width};
/// assert_eq!(narrow_uint_width(0),         UintWidth::U8);
/// assert_eq!(narrow_uint_width(255),       UintWidth::U8);
/// assert_eq!(narrow_uint_width(256),       UintWidth::U16);
/// assert_eq!(narrow_uint_width(65535),     UintWidth::U16);
/// assert_eq!(narrow_uint_width(65536),     UintWidth::U32);
/// assert_eq!(narrow_uint_width(u64::MAX),  UintWidth::U64);
/// ```
pub fn narrow_uint_width(n: u64) -> UintWidth {
    if n <= u8::MAX as u64 {
        UintWidth::U8 // value fits in [0, 255]
    } else if n <= u16::MAX as u64 {
        UintWidth::U16 // value fits in [0, 65535]
    } else if n <= u32::MAX as u64 {
        UintWidth::U32 // value fits in [0, 4294967295]
    } else {
        UintWidth::U64 // full 64-bit unsigned range required
    }
}

/// The minimum floating-point precision required to represent a given value without loss.
///
/// `F32` is selected only when the value round-trips through `f32` exactly; otherwise `F64`.
/// Note that `f32` has 23 mantissa bits (~7 decimal digits) and `f64` has 52 (~15 digits).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum FloatWidth {
    /// 32-bit IEEE-754 single precision (value is exactly representable as `f32`).
    F32,
    /// 64-bit IEEE-754 double precision (full `f64` range needed).
    F64,
}

impl FloatWidth {
    /// Returns the C type name for this floating-point width.
    pub fn c_type_name(self) -> &'static str {
        match self {
            FloatWidth::F32 => "float",  // C `float` is IEEE-754 single precision
            FloatWidth::F64 => "double", // C `double` is IEEE-754 double precision
        }
    }

    /// Returns the SQL type name for this floating-point width.
    pub fn sql_type_name(self) -> &'static str {
        match self {
            FloatWidth::F32 => "REAL",             // SQL REAL is single precision
            FloatWidth::F64 => "DOUBLE PRECISION", // SQL DOUBLE PRECISION is 64-bit
        }
    }
}

/// Returns the minimum [`FloatWidth`] that can represent the given `f64` value without loss.
///
/// A value is representable in `F32` if and only if casting to `f32` and back to `f64`
/// produces the identical bit pattern (NaN and infinities are also preserved).
///
/// # Examples
///
/// ```
/// use ur::primitives::{FloatWidth, narrow_float_width};
/// assert_eq!(narrow_float_width(0.0),    FloatWidth::F32); // zero is exact in f32
/// assert_eq!(narrow_float_width(1.0),    FloatWidth::F32); // powers of two are exact
/// assert_eq!(narrow_float_width(1.0/3.0), FloatWidth::F64); // 1/3 loses precision in f32
/// ```
pub fn narrow_float_width(n: f64) -> FloatWidth {
    // Cast to f32 and back; if the round-trip is bit-identical the value fits in F32.
    let as_f32 = n as f32; // narrowing cast — may lose precision
    if (as_f32 as f64).to_bits() == n.to_bits() {
        FloatWidth::F32 // round-trip is exact: F32 is sufficient
    } else {
        FloatWidth::F64 // round-trip lost bits: F64 required
    }
}

/// The resolved numeric category of a compile-time–known number literal.
///
/// Used to determine which [`crate::elaborated::types::TypeHead`] variant a `TypeHead::Number`
/// should resolve to based solely on the literal value — before consulting usage context.
///
/// Resolution rules:
/// - `Prim::Float(_)` → `Float` (the literal has a decimal point / exponent)
/// - `Prim::Int(n)` where `n >= 0` → `UnsignedInt` (non-negative; fits in a `uint`)
/// - `Prim::Int(n)` where `n < 0` → `SignedInt` (negative; requires a signed type)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumericKind {
    /// The literal is a signed integer (negative or explicitly annotated `int`).
    SignedInt,
    /// The literal is a non-negative integer (can be stored as an unsigned type).
    UnsignedInt,
    /// The literal is a floating-point value.
    Float,
}

/// Classify a numeric primitive literal into its most specific [`NumericKind`].
///
/// This is the first step in resolving `TypeHead::Number`: call this function on the
/// compile-time–known `Prim` value, then map the result to a concrete `TypeHead`.
///
/// Non-numeric primitives (strings, chars) are not accepted; callers must only pass
/// `Prim::Int` or `Prim::Float`. Passing another variant will panic in debug builds.
///
/// # Arguments
///
/// * `prim` — The primitive literal to classify. Must be `Prim::Int` or `Prim::Float`.
///
/// # Returns
///
/// The most specific `NumericKind` derivable from the literal value alone.
///
/// # Panics
///
/// Panics if `prim` is not a numeric primitive (`Prim::Int` or `Prim::Float`).
pub fn classify_prim_number(prim: &Prim) -> NumericKind {
    match prim {
        Prim::Float(_) => NumericKind::Float, // any float literal resolves to Float
        Prim::Int(n) if *n >= 0 => NumericKind::UnsignedInt, // non-negative → Uint candidate
        Prim::Int(_) => NumericKind::SignedInt, // negative → must be signed Int
        Prim::String(_, _) | Prim::Char(_) => {
            // Callers must never pass non-numeric primitives to this function.
            panic!("classify_prim_number called on non-numeric primitive: {prim:?}")
        }
    }
}

/// A resolved numeric type pairing a category with the minimum required bit-width.
///
/// Produced by the numeric narrowing analysis pass to annotate every compile-time–known
/// numeric expression or variable with the smallest concrete hardware type that can
/// faithfully represent its value.  Used by codegen to select the right C/SQL types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NarrowedNumeric {
    /// Signed integer: value is negative, or context requires a signed type.
    Int(IntWidth),
    /// Unsigned integer: value is non-negative and fits in an unsigned representation.
    Uint(UintWidth),
    /// IEEE-754 floating-point value.
    Float(FloatWidth),
}

impl NarrowedNumeric {
    /// Derives the narrowest `NarrowedNumeric` for a compile-time–known primitive literal.
    ///
    /// Returns `None` for non-numeric primitives (strings, characters).
    ///
    /// # Arguments
    ///
    /// * `prim` — The compile-time–known literal to classify and narrow.
    pub fn from_prim(prim: &Prim) -> Option<Self> {
        match prim {
            // Float literal: narrow to F32 when exact, F64 otherwise.
            Prim::Float(f) => Some(Self::Float(narrow_float_width(*f))),
            // Non-negative integer: can be stored unsigned; narrow to smallest Uint.
            Prim::Int(n) if *n >= 0 => Some(Self::Uint(narrow_uint_width(*n as u64))),
            // Negative integer: must be stored signed; narrow to smallest Int.
            Prim::Int(n) => Some(Self::Int(narrow_int_width(*n))),
            // Non-numeric primitives have no narrowed numeric representation.
            Prim::String(_, _) | Prim::Char(_) => None,
        }
    }

    /// Returns the C type name for this narrowed numeric type.
    ///
    /// Suitable for embedding in generated C code headers or casts.
    pub fn c_type_name(self) -> &'static str {
        match self {
            Self::Int(width) => width.c_type_name(), // e.g. "int8_t", "int32_t"
            Self::Uint(width) => width.c_type_name(), // e.g. "uint8_t", "uint64_t"
            Self::Float(width) => width.c_type_name(), // "float" or "double"
        }
    }

    /// Returns the SQL type name for this narrowed numeric type.
    ///
    /// Suitable for embedding in generated SQL DDL (`CREATE TABLE` column types).
    pub fn sql_type_name(self) -> &'static str {
        match self {
            Self::Int(width) => width.sql_type_name(), // e.g. "SMALLINT", "BIGINT"
            Self::Uint(width) => width.sql_type_name(), // e.g. "SMALLINT", "NUMERIC"
            Self::Float(width) => width.sql_type_name(), // "REAL" or "DOUBLE PRECISION"
        }
    }

    /// Returns the least-upper-bound type that can represent values of both `self` and `other`.
    ///
    /// Used when merging narrowed types from multiple branches (e.g., `case` arms).
    /// The promotion hierarchy is Float > Int > Uint; widths within a category
    /// are joined by taking the maximum.
    ///
    /// # Arguments
    ///
    /// * `other` — The other narrowed type to merge with.
    pub fn wider(self, other: Self) -> Self {
        match (self, other) {
            // Same category: take the wider width within that category.
            (Self::Int(a), Self::Int(b)) => Self::Int(a.max(b)),
            (Self::Uint(a), Self::Uint(b)) => Self::Uint(a.max(b)),
            (Self::Float(a), Self::Float(b)) => Self::Float(a.max(b)),
            // Float dominates: any mix of float with int/uint needs F64 for safety.
            (Self::Float(_), _) | (_, Self::Float(_)) => Self::Float(FloatWidth::F64),
            // Int vs Uint: signed must cover the full unsigned range — promote unsigned width by one.
            (Self::Int(i), Self::Uint(u)) | (Self::Uint(u), Self::Int(i)) => {
                // One signed level wider than the unsigned width covers the full range.
                let promoted = match u {
                    UintWidth::U8 => IntWidth::I16, // I16 covers [-32768, 32767] ⊇ [0, 255]
                    UintWidth::U16 => IntWidth::I32, // I32 covers both signed and U16 values
                    UintWidth::U32 => IntWidth::I64, // I64 covers both signed and U32 values
                    UintWidth::U64 => IntWidth::I64, // best-effort: I64 cannot cover all U64 values
                };
                Self::Int(i.max(promoted)) // take whichever signed width is larger
            }
        }
    }

    /// Returns the `NumericKind` category of this narrowed type.
    ///
    /// Bridges `NarrowedNumeric` back to `NumericKind` for category-level decisions.
    pub fn numeric_kind(self) -> NumericKind {
        match self {
            Self::Int(_) => NumericKind::SignedInt,
            Self::Uint(_) => NumericKind::UnsignedInt,
            Self::Float(_) => NumericKind::Float,
        }
    }
}

/// Returns the minimum [`IntWidth`] that can hold the given signed 64-bit value.
///
/// This enables "compile down to the smallest possible type" for integer literals:
/// a literal `42` can be stored in `i8`, while `100_000` requires at least `i32`.
///
/// # Examples
///
/// ```
/// use ur::primitives::{IntWidth, narrow_int_width};
/// assert_eq!(narrow_int_width(42),      IntWidth::I8);
/// assert_eq!(narrow_int_width(200),     IntWidth::I16);
/// assert_eq!(narrow_int_width(100_000), IntWidth::I32);
/// assert_eq!(narrow_int_width(i64::MAX),IntWidth::I64);
/// ```
pub fn narrow_int_width(n: i64) -> IntWidth {
    if n >= i8::MIN as i64 && n <= i8::MAX as i64 {
        IntWidth::I8 // value fits in [-128, 127]
    } else if n >= i16::MIN as i64 && n <= i16::MAX as i64 {
        IntWidth::I16 // value fits in [-32768, 32767]
    } else if n >= i32::MIN as i64 && n <= i32::MAX as i64 {
        IntWidth::I32 // value fits in [-2^31, 2^31 - 1]
    } else {
        IntWidth::I64 // full 64-bit range required
    }
}

/// How string literals are escaped when emitting C or HTML-aware text.
#[derive(Debug, Clone, PartialEq)]
pub enum StringMode {
    Normal,
    Html,
}

/// Primitive literal values carried through all compiler intermediate representations.
#[derive(Debug, Clone, PartialEq)]
pub enum Prim {
    Int(i64),
    Float(f64),
    String(StringMode, std::string::String),
    Char(char),
}

impl Prim {
    /// Format a float with 16 decimal places in scientific notation (matches MLton behaviour).
    ///
    /// # Arguments
    ///
    /// * `n` — Floating-point value to serialize.
    ///
    /// # Returns
    ///
    /// `String` suitable for embedding in generated C or comparisons.
    pub fn float_to_string(n: f64) -> std::string::String {
        format!("{:.16e}", n)
    }

    /// Render the primitive as a C literal (used by the C code generator).
    ///
    /// # Returns
    ///
    /// Source fragment such as `123LL`, a quoted string, or a character literal.
    pub fn to_c_literal(&self) -> std::string::String {
        match self {
            Prim::Int(n) => {
                if *n < 0 {
                    format!("-{}LL", n.unsigned_abs())
                } else {
                    format!("{}LL", n)
                }
            }
            Prim::Float(n) => Self::float_to_string(*n),
            Prim::String(_, s) => {
                let escaped = Self::quote_double(s);
                format!("\"{}\"", escaped)
            }
            Prim::Char(ch) => {
                format!("'{}'", Self::to_c_char(*ch))
            }
        }
    }

    /// Escape a string for double-quoted C literals (mirrors upstream Char/string escaping rules).
    fn quote_double(string: &str) -> std::string::String {
        let mut out = std::string::String::new();
        for ch in string.chars() {
            match ch {
                '\'' => out.push_str("\\'"),
                _ => {
                    // Mirror Char.toCString: escape non-printable chars
                    if ch == '\\' {
                        out.push_str("\\\\");
                    } else if ch == '"' {
                        out.push_str("\\\"");
                    } else if ch == '\n' {
                        out.push_str("\\n");
                    } else if ch == '\r' {
                        out.push_str("\\r");
                    } else if ch == '\t' {
                        out.push_str("\\t");
                    } else if ch.is_ascii() && (ch as u8) < 32 {
                        out.push_str(&format!("\\x{:02x}", ch as u8));
                    } else {
                        out.push(ch);
                    }
                }
            }
        }
        out
    }

    /// Format a single Unicode scalar as a C character literal.
    fn to_c_char(ch: char) -> std::string::String {
        match ch {
            '"' => "\"".to_string(),
            _ => Self::quote_double(&ch.to_string()),
        }
    }

    /// Total ordering suitable for BTreeMap keys.
    ///
    /// # Returns
    ///
    /// Discriminator byte: integer `0`, float `1`, string `2`, character `3`.
    pub fn variant_tag(&self) -> u8 {
        match self {
            Prim::Int(_) => 0,
            Prim::Float(_) => 1,
            Prim::String(_, _) => 2,
            Prim::Char(_) => 3,
        }
    }
}

/// Human-readable rendering for logging and tests (not C syntax).
impl fmt::Display for Prim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Prim::Int(n) => write!(f, "{n}"),
            Prim::Float(n) => write!(f, "{}", Self::float_to_string(*n)),
            Prim::String(_, s) => write!(f, "{s}"),
            Prim::Char(ch) => write!(f, "{ch}"),
        }
    }
}

/// Delegates total compare to [`Ord`] for `Prim`.
impl PartialOrd for Prim {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Eq for Prim {}

/// Total order: integers, then floats, strings, then chars (see variant tags).
impl Ord for Prim {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        match (self, other) {
            (Prim::Int(a), Prim::Int(b)) => a.cmp(b),
            (Prim::Int(_), _) => Ordering::Less,
            (_, Prim::Int(_)) => Ordering::Greater,

            (Prim::Float(a), Prim::Float(b)) => a.partial_cmp(b).unwrap_or(Ordering::Equal),
            (Prim::Float(_), _) => Ordering::Less,
            (_, Prim::Float(_)) => Ordering::Greater,

            (Prim::String(_, a), Prim::String(_, b)) => a.cmp(b),
            (Prim::String(_, _), _) => Ordering::Less,
            (_, Prim::String(_, _)) => Ordering::Greater,

            (Prim::Char(a), Prim::Char(b)) => a.cmp(b),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn int_c_literal() {
        assert_eq!(Prim::Int(42).to_c_literal(), "42LL");
        assert_eq!(Prim::Int(-5).to_c_literal(), "-5LL");
    }

    #[test]
    fn int_c_literal_zero_not_negative() {
        assert_eq!(Prim::Int(0).to_c_literal(), "0LL");
    }

    #[test]
    fn int_c_literal_negative_uses_minus() {
        let s = Prim::Int(-1).to_c_literal();
        assert!(s.starts_with('-'), "negative int must start with -: {}", s);
    }

    #[test]
    fn float_to_string_sci_notation() {
        let s = Prim::float_to_string(3.0);
        assert!(s.contains('e'), "expected scientific notation, got: {}", s);
    }

    #[test]
    fn string_c_literal() {
        let p = Prim::String(StringMode::Normal, "hello".to_string());
        assert_eq!(p.to_c_literal(), "\"hello\"");
    }

    #[test]
    fn string_escapes_quotes() {
        let p = Prim::String(StringMode::Normal, r#""hello""#.into());
        assert!(p.to_c_literal().contains("\\\""));
    }

    #[test]
    fn string_escapes_apostrophe() {
        let p = Prim::String(StringMode::Normal, "it's".into());
        assert!(
            p.to_c_literal().contains("it\\'s"),
            "apostrophe must be escaped as \\'"
        );
    }

    #[test]
    fn string_with_apostrophe_preserved() {
        let p = Prim::String(StringMode::Normal, "don't".into());
        assert!(
            p.to_c_literal().contains("\\'"),
            "apostrophe must be escaped as \\'"
        );
    }

    #[test]
    fn string_with_control_char_escaped() {
        let p = Prim::String(StringMode::Normal, "\x01".into());
        assert!(p.to_c_literal().contains("\\x01"));
    }

    #[test]
    fn string_space_not_hex_escaped() {
        let p = Prim::String(StringMode::Normal, "a b".into());
        assert!(
            !p.to_c_literal().contains("\\x20"),
            "space (0x20) must not use \\x20"
        );
    }

    #[test]
    fn char_escapes_double_quote() {
        let p = Prim::Char('"');
        assert_eq!(p.to_c_literal(), "'\"'");
    }

    #[test]
    fn variant_tag_distinct() {
        assert_eq!(Prim::Int(0).variant_tag(), 0);
        assert_eq!(Prim::Float(0.0).variant_tag(), 1);
    }

    #[test]
    fn char_c_literal() {
        let p = Prim::Char('x');
        assert_eq!(p.to_c_literal(), "'x'");
    }

    #[test]
    fn ordering_int_lt_float() {
        assert!(Prim::Int(1) < Prim::Float(1.0));
    }

    #[test]
    fn ordering_float_lt_string() {
        assert!(Prim::Float(0.0) < Prim::String(StringMode::Normal, "a".into()));
    }

    #[test]
    fn prim_to_string() {
        assert_eq!(Prim::Int(7).to_string(), "7");
        assert_eq!(
            Prim::String(StringMode::Html, "hi".to_string()).to_string(),
            "hi"
        );
    }

    // ── IntWidth / narrow_int_width tests ────────────────────────────────────

    #[test]
    fn narrow_int_width_i8_boundary() {
        assert_eq!(narrow_int_width(0), IntWidth::I8); // zero fits in i8
        assert_eq!(narrow_int_width(127), IntWidth::I8); // i8::MAX
        assert_eq!(narrow_int_width(-128), IntWidth::I8); // i8::MIN
    }

    #[test]
    fn narrow_int_width_i16_boundary() {
        assert_eq!(narrow_int_width(128), IntWidth::I16); // one past i8::MAX
        assert_eq!(narrow_int_width(-129), IntWidth::I16); // one past i8::MIN
        assert_eq!(narrow_int_width(32767), IntWidth::I16); // i16::MAX
        assert_eq!(narrow_int_width(-32768), IntWidth::I16); // i16::MIN
    }

    #[test]
    fn narrow_int_width_i32_boundary() {
        assert_eq!(narrow_int_width(32768), IntWidth::I32); // one past i16::MAX
        assert_eq!(narrow_int_width(100_000), IntWidth::I32); // typical small integer constant
        assert_eq!(narrow_int_width(i32::MAX as i64), IntWidth::I32);
        assert_eq!(narrow_int_width(i32::MIN as i64), IntWidth::I32);
    }

    #[test]
    fn narrow_int_width_i64_boundary() {
        assert_eq!(narrow_int_width(i32::MAX as i64 + 1), IntWidth::I64); // one past i32::MAX
        assert_eq!(narrow_int_width(i64::MAX), IntWidth::I64); // maximum value
        assert_eq!(narrow_int_width(i64::MIN), IntWidth::I64); // minimum value
    }

    #[test]
    fn int_width_c_and_sql_type_names() {
        assert_eq!(IntWidth::I8.c_type_name(), "int8_t");
        assert_eq!(IntWidth::I16.c_type_name(), "int16_t");
        assert_eq!(IntWidth::I32.c_type_name(), "int32_t");
        assert_eq!(IntWidth::I64.c_type_name(), "int64_t");
        assert_eq!(IntWidth::I32.sql_type_name(), "INTEGER");
        assert_eq!(IntWidth::I64.sql_type_name(), "BIGINT");
    }

    #[test]
    fn int_width_ordering() {
        // Wider widths sort higher so you can use .max() to combine requirements.
        assert!(IntWidth::I8 < IntWidth::I16);
        assert!(IntWidth::I16 < IntWidth::I32);
        assert!(IntWidth::I32 < IntWidth::I64);
    }

    // ── UintWidth / narrow_uint_width tests ──────────────────────────────────

    #[test]
    fn narrow_uint_width_u8_boundary() {
        assert_eq!(narrow_uint_width(0), UintWidth::U8); // minimum value
        assert_eq!(narrow_uint_width(255), UintWidth::U8); // u8::MAX
    }

    #[test]
    fn narrow_uint_width_u16_boundary() {
        assert_eq!(narrow_uint_width(256), UintWidth::U16); // one past u8::MAX
        assert_eq!(narrow_uint_width(65535), UintWidth::U16); // u16::MAX
    }

    #[test]
    fn narrow_uint_width_u32_boundary() {
        assert_eq!(narrow_uint_width(65536), UintWidth::U32); // one past u16::MAX
        assert_eq!(narrow_uint_width(u32::MAX as u64), UintWidth::U32);
    }

    #[test]
    fn narrow_uint_width_u64_boundary() {
        assert_eq!(narrow_uint_width(u32::MAX as u64 + 1), UintWidth::U64);
        assert_eq!(narrow_uint_width(u64::MAX), UintWidth::U64);
    }

    #[test]
    fn uint_width_ordering() {
        // Wider widths sort higher.
        assert!(UintWidth::U8 < UintWidth::U16);
        assert!(UintWidth::U16 < UintWidth::U32);
        assert!(UintWidth::U32 < UintWidth::U64);
    }

    #[test]
    fn uint_width_c_and_sql_type_names() {
        assert_eq!(UintWidth::U8.c_type_name(), "uint8_t");
        assert_eq!(UintWidth::U32.c_type_name(), "uint32_t");
        assert_eq!(UintWidth::U8.sql_type_name(), "SMALLINT");
        assert_eq!(UintWidth::U64.sql_type_name(), "NUMERIC");
    }

    // ── FloatWidth / narrow_float_width tests ────────────────────────────────

    #[test]
    fn narrow_float_width_zero_is_f32() {
        assert_eq!(narrow_float_width(0.0), FloatWidth::F32); // zero is exact in f32
    }

    #[test]
    fn narrow_float_width_power_of_two_is_f32() {
        assert_eq!(narrow_float_width(1.0), FloatWidth::F32); // 2^0 exact
        assert_eq!(narrow_float_width(64.0), FloatWidth::F32); // 2^6 exact
    }

    #[test]
    fn narrow_float_width_one_third_requires_f64() {
        assert_eq!(narrow_float_width(1.0 / 3.0), FloatWidth::F64); // 1/3 is not exact in f32
    }

    #[test]
    fn float_width_ordering() {
        assert!(FloatWidth::F32 < FloatWidth::F64); // F32 is narrower
    }

    #[test]
    fn float_width_type_names() {
        assert_eq!(FloatWidth::F32.c_type_name(), "float");
        assert_eq!(FloatWidth::F64.c_type_name(), "double");
        assert_eq!(FloatWidth::F32.sql_type_name(), "REAL");
        assert_eq!(FloatWidth::F64.sql_type_name(), "DOUBLE PRECISION");
    }

    // ── classify_prim_number tests ───────────────────────────────────────────

    #[test]
    fn classify_prim_number_positive_int_is_unsigned() {
        assert_eq!(
            classify_prim_number(&Prim::Int(0)),
            NumericKind::UnsignedInt
        );
        assert_eq!(
            classify_prim_number(&Prim::Int(42)),
            NumericKind::UnsignedInt
        );
        assert_eq!(
            classify_prim_number(&Prim::Int(i64::MAX)),
            NumericKind::UnsignedInt
        );
    }

    #[test]
    fn classify_prim_number_negative_int_is_signed() {
        assert_eq!(classify_prim_number(&Prim::Int(-1)), NumericKind::SignedInt);
        assert_eq!(
            classify_prim_number(&Prim::Int(i64::MIN)),
            NumericKind::SignedInt
        );
    }

    #[test]
    fn classify_prim_number_float_is_float() {
        assert_eq!(classify_prim_number(&Prim::Float(0.0)), NumericKind::Float);
        assert_eq!(
            classify_prim_number(&Prim::Float(-3.14)),
            NumericKind::Float
        );
        assert_eq!(
            classify_prim_number(&Prim::Float(1.0 / 3.0)),
            NumericKind::Float
        );
    }
}
