//! Primitive literals shared across all IRs.
//!
//! - **Prim**: Int, Float, String(StringMode, _), Char
//! - **StringMode**: Normal vs Html (different escaping for codegen)
//! - Methods: to_c_literal, float_to_string; runtime text via `Display` (`ToString`)
//!
//! Mirrors SML's `Prim.t`.

use std::fmt;

/// Primitive literals (mirrors SML's `Prim.t`).
#[derive(Debug, Clone, PartialEq)]
pub enum StringMode {
    Normal,
    Html,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Prim {
    Int(i64),
    Float(f64),
    String(StringMode, std::string::String),
    Char(char),
}

impl Prim {
    /// Format a float with 16 decimal places in scientific notation (matches MLton behaviour).
    pub fn float_to_string(n: f64) -> std::string::String {
        format!("{:.16e}", n)
    }

    /// Render the primitive as a C literal (used by the C code generator).
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

    fn to_c_char(ch: char) -> std::string::String {
        match ch {
            '"' => "\"".to_string(),
            _ => Self::quote_double(&ch.to_string()),
        }
    }

    /// Total ordering suitable for BTreeMap keys.
    pub fn variant_tag(&self) -> u8 {
        match self {
            Prim::Int(_) => 0,
            Prim::Float(_) => 1,
            Prim::String(_, _) => 2,
            Prim::Char(_) => 3,
        }
    }
}

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

impl PartialOrd for Prim {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Eq for Prim {}

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
}
