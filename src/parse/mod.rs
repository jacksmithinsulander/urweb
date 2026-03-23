//! Parser for Ur/Web source files.
//!
//! - **parse_ur**: parse `.ur` files into `source::File`
//! - **parse_urs**: parse `.urs` signature files
//! - **lexer**: tokenization (Logos)

pub mod lexical_analyzer;
pub mod xml_helpers;

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

/// Decrement linear fuel; when exhausted, append the rest of `src` and return (stops Θ(n²) mutants).
macro_rules! preprocess_urs_burn {
    ($fuel:expr, $out:expr, $src:expr, $i:expr) => {{
        if $fuel == 0 {
            $out.push_str(&$src[$i..]);
            return $out;
        }
        $fuel -= 1;
    }};
}

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
    // Valid scans advance through the input at most once per loop (≤ n steps).
    // Keep the cap at n+1 so mutants that break `i` or conditions bail out fast
    // instead of doing O(8n) work (which times out on large .urs files).
    let step_cap = n.saturating_add(1);
    // Cap total inner-loop iterations across the whole pass (well-formed input uses O(n)).
    let mut fuel = n.saturating_mul(64).saturating_add(4096);
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

    // Bounded outer driver: `for _ in 0..` with `tick > cap` is fragile (`>` → `>=` / `==` mutants).
    // A fixed `take(step_cap + 1)`-style range always terminates.
    for _ in 0..step_cap.saturating_add(1) {
        if i >= n {
            break;
        }
        preprocess_urs_burn!(fuel, out, src, i);
        // Skip ML block comments (* ... *) verbatim
        if b[i] == b'(' && i + 1 < n && b[i + 1] == b'*' {
            out.push_str("(*");
            i += 2;
            let mut depth = 1usize;
            for _ in 0..step_cap {
                preprocess_urs_burn!(fuel, out, src, i);
                if i >= n || depth == 0 {
                    break;
                }
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
            if depth > 0 {
                out.push_str(&src[i..]);
                return out;
            }
            continue;
        }

        // Skip string literals verbatim
        if b[i] == b'"' {
            out.push('"');
            last_token.clear();
            last_token.push('"');
            i += 1;
            for _ in 0..step_cap {
                preprocess_urs_burn!(fuel, out, src, i);
                if i >= n || b[i] == b'"' {
                    break;
                }
                if b[i] == b'\\' && i + 1 < n {
                    out.push(b[i] as char);
                    out.push(b[i + 1] as char);
                    i += 2;
                } else {
                    out.push(b[i] as char);
                    i += 1;
                }
            }
            if i < n && b[i] != b'"' {
                out.push_str(&src[i..]);
                return out;
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
            for _ in 0..step_cap {
                preprocess_urs_burn!(fuel, out, src, i);
                if i >= n || !(b[i].is_ascii_alphanumeric() || b[i] == b'_' || b[i] == b'\'') {
                    break;
                }
                i += 1;
            }
            if i < n && (b[i].is_ascii_alphanumeric() || b[i] == b'_' || b[i] == b'\'') {
                out.push_str(&src[i..]);
                return out;
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
                for _ in 0..step_cap {
                    preprocess_urs_burn!(fuel, out, src, i);
                    if i >= n || !(b[i] == b' ' || b[i] == b'\t' || b[i] == b'\n' || b[i] == b'\r')
                    {
                        break;
                    }
                    i += 1;
                }
                if i < n && (b[i] == b' ' || b[i] == b'\t' || b[i] == b'\n' || b[i] == b'\r') {
                    out.push_str(&src[i..]);
                    return out;
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
                for _ in 0..step_cap {
                    preprocess_urs_burn!(fuel, out, src, i);
                    if i >= n || !(b[i] == b' ' || b[i] == b'\t' || b[i] == b'\n' || b[i] == b'\r')
                    {
                        break;
                    }
                    i += 1;
                }
                if i < n && (b[i] == b' ' || b[i] == b'\t' || b[i] == b'\n' || b[i] == b'\r') {
                    out.push_str(&src[i..]);
                    return out;
                }

                // Scan the KindAtom: identifier, `{...}`, or `(...)`
                let ka_start = i;
                if i < n && b[i] == b'{' {
                    let mut depth = 1usize;
                    i += 1;
                    for _ in 0..step_cap {
                        preprocess_urs_burn!(fuel, out, src, i);
                        if i >= n || depth == 0 {
                            break;
                        }
                        if b[i] == b'{' {
                            depth += 1;
                        } else if b[i] == b'}' {
                            depth -= 1;
                        }
                        i += 1;
                    }
                    if depth > 0 {
                        out.push_str(&src[i..]);
                        return out;
                    }
                } else if i < n && b[i] == b'(' {
                    let mut depth = 1usize;
                    i += 1;
                    for _ in 0..step_cap {
                        preprocess_urs_burn!(fuel, out, src, i);
                        if i >= n || depth == 0 {
                            break;
                        }
                        if b[i] == b'(' {
                            depth += 1;
                        } else if b[i] == b')' {
                            depth -= 1;
                        }
                        i += 1;
                    }
                    if depth > 0 {
                        out.push_str(&src[i..]);
                        return out;
                    }
                } else if i < n && (b[i].is_ascii_alphabetic() || b[i] == b'_') {
                    for _ in 0..step_cap {
                        preprocess_urs_burn!(fuel, out, src, i);
                        if i >= n
                            || !(b[i].is_ascii_alphanumeric() || b[i] == b'_' || b[i] == b'\'')
                        {
                            break;
                        }
                        i += 1;
                    }
                    if i < n && (b[i].is_ascii_alphanumeric() || b[i] == b'_' || b[i] == b'\'') {
                        out.push_str(&src[i..]);
                        return out;
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
                for _ in 0..step_cap {
                    preprocess_urs_burn!(fuel, out, src, i);
                    if i >= n || !(b[i] == b' ' || b[i] == b'\t' || b[i] == b'\n' || b[i] == b'\r')
                    {
                        break;
                    }
                    i += 1;
                }
                if i < n && (b[i] == b' ' || b[i] == b'\t' || b[i] == b'\n' || b[i] == b'\r') {
                    out.push_str(&src[i..]);
                    return out;
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

    if i < n {
        out.push_str(&src[i..]);
    }
    out
}

/// Preprocessed excerpt of `lib/ur/basis.urs` around `pos` (for dev binaries / mutation tests).
pub fn basis_urs_preprocessed_window(
    pos: usize,
    before: usize,
    after: usize,
) -> std::io::Result<String> {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/lib/ur/basis.urs");
    let src = std::fs::read_to_string(path)?;
    let pp = preprocess_urs(&src);
    let start = pos.saturating_sub(before);
    let end = (pos + after).min(pp.len());
    Ok(pp[start..end].to_string())
}

/// Parse a single `.ur` source file.
///
/// Returns `None` and records an error in `errors` on parse failure.
pub fn parse_ur(_filename: &str, source: &str, errors: &mut ErrorReporter) -> Option<File> {
    #[cfg(generated_parser)]
    {
        let lexer = lexical_analyzer::XmlAwareLexer::new(source);
        match grammar::FileParser::new().parse(lexer) {
            Ok(file) => Some(file),
            Err(e) => {
                let msg = format!("{:?}", e);
                eprintln!("parse_ur({}) error: {}", _filename, msg);
                errors.report(CompileError::at(Span::dummy(), msg));
                None
            }
        }
    }
    #[cfg(not(generated_parser))]
    {
        let _ = (_filename, source);
        errors.report(CompileError::Plain(
            "parse_ur: parser not available — rebuild with URWEB_GEN_PARSER=1".into(),
        ));
        None
    }
}

/// Parse `val x = 1` as a smoke check (shared with the `test_parse` binary).
pub fn smoke_parse_val_decl_count(errors: &mut ErrorReporter) -> Option<usize> {
    parse_ur("test.ur", "val x = 1", errors).map(|f| f.len())
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
                eprintln!("parse_urs({}) error: {}", _filename, msg);
                errors.report(CompileError::at(Span::dummy(), msg));
                None
            }
        }
    }
    #[cfg(not(generated_parser))]
    {
        let _ = (_filename, source);
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
            let file = result.expect("val x = 1 should parse");
            assert_eq!(file.len(), 1, "single top-level val decl");
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
    fn basis_urs_window_matches_fixed_width() {
        let pos = 38564usize;
        let before = 200usize;
        let after = 100usize;
        let s = basis_urs_preprocessed_window(pos, before, after).expect("read basis.urs");
        assert_eq!(
            s.len(),
            before + after,
            "slice must use (pos + after).min(len) — catches + → - / * mutants"
        );
    }

    #[test]
    fn smoke_val_decl_count_tracks_parser() {
        let mut errors = ErrorReporter::new();
        let n = smoke_parse_val_decl_count(&mut errors);
        #[cfg(not(generated_parser))]
        {
            assert!(n.is_none());
            assert!(errors.has_errors());
        }
        #[cfg(generated_parser)]
        {
            assert_eq!(n, Some(1), "smoke parse must count exactly one decl");
        }
    }

    #[test]
    fn parse_ur_two_vals_requires_two_decls() {
        let mut errors = ErrorReporter::new();
        let n = parse_ur("t.ur", "val a = 1\nval b = 2", &mut errors).map(|f| f.len());
        #[cfg(generated_parser)]
        {
            assert_eq!(
                n,
                Some(2),
                "catches smoke_parse_val_decl_count -> Some(1) style mutants"
            );
        }
        #[cfg(not(generated_parser))]
        {
            assert!(n.is_none());
        }
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
            let items = result.expect("val x : int should parse as a signature");
            assert!(
                !items.is_empty(),
                "catches parse_urs -> Some(vec![]) mutants"
            );
        }
    }
}
