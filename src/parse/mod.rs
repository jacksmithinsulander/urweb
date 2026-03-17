//! Parser for Ur/Web source files.
//!
//! - **parse_ur**: parse `.ur` files into `source::File`
//! - **parse_urs**: parse `.urs` signature files
//! - **lexer**: tokenization (Logos)

pub mod lexical_analyzer;

// Include the LALRPOP-generated parser when it has been built.
// `build.rs` sets `cargo:rustc-cfg=generated_parser` only when
// URWEB_GEN_PARSER=1 was passed.  Without that flag the grammar is not
// regenerated and the stubs below are used instead.
#[cfg(generated_parser)]
mod grammar {
    include!(concat!(env!("OUT_DIR"), "/parse/grammar.rs"));
}

use crate::error_types::{CompileError, ErrorReporter, Span};
use crate::source::{File, LocSgnItem};

/// Pre-process a `.urs` source string to convert bare implicit constructor
/// quantifiers into bracketed form that the LR(1) grammar can parse without
/// conflicts.
///
/// Transforms:
///   `name :: KindAtom ->`   →  `[name :: KindAtom] ->`
///   `name ::: KindAtom ->`  →  `[name ::: KindAtom] ->`
///
/// KindAtom can be an identifier, `{...}` (record kind), or `(...)` (arrow
/// kind in parens).  Characters inside `(* *)` comments and `"..."` strings
/// are left untouched.
///
/// The transformation is only applied when the `IDENT ::` pattern appears
/// INSIDE a type expression, not as the subject of a declaration keyword
/// (`con`, `class`, `type`, `structure`, `signature`, `datatype`).
pub fn preprocess_urs(src: &str) -> String {
    // Declaration-header keywords after which `IDENT ::` means a kind
    // annotation (not an implicit quantifier) and must NOT be bracketed.
    const DECL_KEYWORDS: &[&str] = &[
        "con",
        "class",
        "type",
        "structure",
        "signature",
        "datatype",
        "val",
    ];

    let b = src.as_bytes();
    let n = b.len();
    let mut out = String::with_capacity(n + 128);
    let mut i = 0;
    // Track the last non-whitespace, non-comment token we emitted so we can
    // decide whether an identifier is in "declaration head" position.
    let mut last_token = String::new();

    // Emit a char and update last_token if it's a word char.
    // For simplicity we only track the last WORD token (letters/digits).
    let emit_word = |out: &mut String, last: &mut String, w: &str| {
        out.push_str(w);
        last.clear();
        last.push_str(w);
    };

    while i < n {
        // Skip ML block comments (* ... *) verbatim
        if b[i] == b'(' && i + 1 < n && b[i + 1] == b'*' {
            out.push_str("(*");
            i += 2;
            let mut depth = 1usize;
            while i < n && depth > 0 {
                if b[i] == b'(' && i + 1 < n && b[i + 1] == b'*' {
                    out.push_str("(*");
                    i += 2;
                    depth += 1;
                } else if b[i] == b'*' && i + 1 < n && b[i + 1] == b')' {
                    out.push_str("*)");
                    i += 2;
                    depth -= 1;
                } else {
                    out.push(b[i] as char);
                    i += 1;
                }
            }
            continue;
        }

        // Skip string literals verbatim
        if b[i] == b'"' {
            out.push('"');
            last_token.clear();
            last_token.push('"');
            i += 1;
            while i < n && b[i] != b'"' {
                if b[i] == b'\\' && i + 1 < n {
                    out.push(b[i] as char);
                    out.push(b[i + 1] as char);
                    i += 2;
                } else {
                    out.push(b[i] as char);
                    i += 1;
                }
            }
            if i < n {
                out.push('"');
                i += 1;
            }
            continue;
        }

        // Whitespace: pass through without updating last_token
        if b[i] == b' ' || b[i] == b'\t' || b[i] == b'\n' || b[i] == b'\r' {
            out.push(b[i] as char);
            i += 1;
            continue;
        }

        // Identifier (letters, digits, underscore, apostrophe)
        if b[i].is_ascii_alphabetic() || b[i] == b'_' {
            let id_start = i;
            while i < n && (b[i].is_ascii_alphanumeric() || b[i] == b'_' || b[i] == b'\'') {
                i += 1;
            }
            let ident = &src[id_start..i];

            // Only attempt implicit-quantifier transformation for lowercase identifiers
            // that do NOT immediately follow a declaration keyword.
            let is_decl_name = DECL_KEYWORDS.contains(&last_token.as_str());

            // Update last_token
            last_token.clear();
            last_token.push_str(ident);

            if !is_decl_name && (b[id_start].is_ascii_lowercase() || b[id_start] == b'_') {
                // Skip whitespace after the identifier
                let ws1 = i;
                while i < n && (b[i] == b' ' || b[i] == b'\t' || b[i] == b'\n' || b[i] == b'\r') {
                    i += 1;
                }
                let colon_start = i; // position of the first colon (or non-colon if no match)

                // Match `:::` or `::` (but not `::::`)
                let colons: &str;
                if i + 2 < n && &b[i..i + 3] == b":::" && !(i + 3 < n && b[i + 3] == b':') {
                    colons = ":::";
                    i += 3;
                } else if i + 1 < n && &b[i..i + 2] == b"::" && !(i + 2 < n && b[i + 2] == b':') {
                    colons = "::";
                    i += 2;
                } else {
                    // Not a quantifier: emit the identifier and the whitespace
                    out.push_str(ident);
                    out.push_str(&src[ws1..i]);
                    continue;
                }

                // Skip whitespace after the colons
                let ws2 = i;
                while i < n && (b[i] == b' ' || b[i] == b'\t' || b[i] == b'\n' || b[i] == b'\r') {
                    i += 1;
                }

                // Scan the KindAtom: identifier, `{...}`, or `(...)`
                let ka_start = i;
                if i < n && b[i] == b'{' {
                    let mut depth = 1usize;
                    i += 1;
                    while i < n && depth > 0 {
                        if b[i] == b'{' {
                            depth += 1;
                        } else if b[i] == b'}' {
                            depth -= 1;
                        }
                        i += 1;
                    }
                } else if i < n && b[i] == b'(' {
                    let mut depth = 1usize;
                    i += 1;
                    while i < n && depth > 0 {
                        if b[i] == b'(' {
                            depth += 1;
                        } else if b[i] == b')' {
                            depth -= 1;
                        }
                        i += 1;
                    }
                } else if i < n && (b[i].is_ascii_alphabetic() || b[i] == b'_') {
                    while i < n && (b[i].is_ascii_alphanumeric() || b[i] == b'_' || b[i] == b'\'') {
                        i += 1;
                    }
                } else {
                    // No valid kind term: emit everything as-is
                    out.push_str(ident);
                    out.push_str(&src[ws1..ws2]);
                    out.push_str(colons);
                    out.push_str(&src[ws2..i]);
                    continue;
                }
                let kind_atom = &src[ka_start..i];

                // Skip whitespace before potential `->`
                let ws3 = i;
                while i < n && (b[i] == b' ' || b[i] == b'\t' || b[i] == b'\n' || b[i] == b'\r') {
                    i += 1;
                }

                // Check if followed by `->`
                if i + 1 < n && b[i] == b'-' && b[i + 1] == b'>' {
                    // Emit bracketed form
                    out.push('[');
                    out.push_str(ident);
                    out.push(' ');
                    out.push_str(colons);
                    out.push(' ');
                    out.push_str(kind_atom);
                    out.push(']');
                    out.push_str(&src[ws3..i]);
                    last_token.clear();
                    last_token.push(']');
                } else {
                    // Not followed by `->`: emit as-is
                    out.push_str(ident);
                    out.push_str(&src[ws1..colon_start]); // whitespace before colons
                    out.push_str(colons);
                    out.push_str(&src[ws2..ka_start]); // whitespace after colons
                    out.push_str(kind_atom);
                    out.push_str(&src[ws3..i]);
                }
                continue;
            }

            // Emit identifier as-is (either it's a decl-name or uppercase)
            emit_word(&mut out, &mut last_token, ident);
            continue;
        }

        // Non-word, non-whitespace character: emit and update last_token
        out.push(b[i] as char);
        last_token.clear();
        last_token.push(b[i] as char);
        i += 1;
    }

    out
}

/// Parse a single `.ur` source file.
///
/// Returns `None` and records an error in `errors` on parse failure.
pub fn parse_ur(_filename: &str, source: &str, errors: &mut ErrorReporter) -> Option<File> {
    #[cfg(generated_parser)]
    {
        let lexer = lexical_analyzer::Lexer::new(source);
        match grammar::FileParser::new().parse(lexer) {
            Ok(file) => Some(file),
            Err(e) => {
                let msg = format!("{:?}", e);
                errors.report(CompileError::at(Span::dummy(), msg));
                None
            }
        }
    }
    #[cfg(not(generated_parser))]
    {
        let _ = (filename, source);
        errors.report(CompileError::Plain(
            "parse_ur: parser not available — rebuild with URWEB_GEN_PARSER=1".into(),
        ));
        None
    }
}

/// Parse a `.urs` signature file.
///
/// Returns `None` and records an error in `errors` on parse failure.
pub fn parse_urs(
    _filename: &str,
    source: &str,
    errors: &mut ErrorReporter,
) -> Option<Vec<LocSgnItem>> {
    #[cfg(generated_parser)]
    {
        // Pre-process to convert bare implicit quantifiers `nm :: Kind ->`
        // to bracketed form `[nm :: Kind] ->` which the LR grammar handles.
        let preprocessed = preprocess_urs(source);
        let lexer = lexical_analyzer::Lexer::new(&preprocessed);
        match grammar::SgnItemsParser::new().parse(lexer) {
            Ok(items) => Some(items),
            Err(e) => {
                let msg = format!("{:?}", e);
                errors.report(CompileError::at(Span::dummy(), msg));
                None
            }
        }
    }
    #[cfg(not(generated_parser))]
    {
        let _ = (filename, source);
        errors.report(CompileError::Plain(
            "parse_urs: parser not available — rebuild with URWEB_GEN_PARSER=1".into(),
        ));
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_ur_returns_none_without_generated_parser() {
        let mut errors = ErrorReporter::new();
        let result = parse_ur("test.ur", "val x = 1", &mut errors);
        #[cfg(not(generated_parser))]
        {
            assert!(result.is_none());
            assert!(errors.has_errors());
        }
        #[cfg(generated_parser)]
        {
            // With the real parser a trivial declaration should parse.
            let _ = result;
        }
    }

    #[test]
    fn pp_basis_context() {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/lib/ur/basis.urs");
        let Ok(content) = std::fs::read_to_string(path) else {
            return;
        };
        let pp = preprocess_urs(&content);
        let pos: usize = 15599;
        let start = pos.saturating_sub(300);
        let end = (pos + 200).min(pp.len());
        eprintln!("PREPROCESSED around {}:\n{}", pos, &pp[start..end]);
        eprintln!("char at {}: {:?}", pos, pp.chars().nth(pos));
    }

    #[test]
    fn parse_urs_returns_none_without_generated_parser() {
        let mut errors = ErrorReporter::new();
        let result = parse_urs("test.urs", "val x : int", &mut errors);
        #[cfg(not(generated_parser))]
        {
            assert!(result.is_none());
            assert!(errors.has_errors());
        }
        #[cfg(generated_parser)]
        {
            let _ = result;
        }
    }
}
