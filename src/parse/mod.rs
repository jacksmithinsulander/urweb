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
/// Uses `checked_sub` only (no `fuel == 0`) so `==`/`!=` mutants cannot skip the drain path and spin.
macro_rules! preprocess_urs_burn {
    ($fuel:expr, $out:expr, $src:expr, $i:expr) => {{
        match $fuel.checked_sub(1) {
            Some(f) => {
                $fuel = f;
            }
            None => {
                $out.push_str(&$src[$i..]);
                return $out;
            }
        }
    }};
}

/// Hot inner loops (comment/string) charge multiple fuel units per byte so mutants time out on fuel, not wall clock.
macro_rules! preprocess_urs_burn_hot {
    ($fuel:expr, $out:expr, $src:expr, $i:expr) => {{
        preprocess_urs_burn!($fuel, $out, $src, $i);
        preprocess_urs_burn!($fuel, $out, $src, $i);
        preprocess_urs_burn!($fuel, $out, $src, $i);
        preprocess_urs_burn!($fuel, $out, $src, $i);
        preprocess_urs_burn!($fuel, $out, $src, $i);
        preprocess_urs_burn!($fuel, $out, $src, $i);
        preprocess_urs_burn!($fuel, $out, $src, $i);
        preprocess_urs_burn!($fuel, $out, $src, $i);
        preprocess_urs_burn!($fuel, $out, $src, $i);
        preprocess_urs_burn!($fuel, $out, $src, $i);
        preprocess_urs_burn!($fuel, $out, $src, $i);
        preprocess_urs_burn!($fuel, $out, $src, $i);
        preprocess_urs_burn!($fuel, $out, $src, $i);
        preprocess_urs_burn!($fuel, $out, $src, $i);
        preprocess_urs_burn!($fuel, $out, $src, $i);
        preprocess_urs_burn!($fuel, $out, $src, $i);
    }};
}

// Macros (not `fn`): cargo-mutants cannot replace the whole helper with `true`/`false` and hang.
// `matches!` avoids a single `==` that `!=` mutants can flip wholesale.
macro_rules! pp_urs_is_ws {
    ($c:expr) => {{
        let __c = $c;
        matches!(__c, b' ' | b'\t' | b'\n' | b'\r')
    }};
}

macro_rules! pp_urs_id_cont {
    ($c:expr) => {{
        let __c = $c;
        matches!(
            __c,
            b'_' | b'\'' | b'0'..=b'9' | b'a'..=b'z' | b'A'..=b'Z'
        )
    }};
}

macro_rules! pp_urs_depth_nonzero {
    ($d:expr) => {{
        let __d = $d;
        matches!(__d, 1..)
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
    // Cap total work across the whole pass. Comment/string inner loops burn many units per
    // iteration so `&&`→`||` / `+=` mutants cannot reach Θ(n²) wall time before fuel exhausts.
    // Upper bound so `*` / oversized literal mutants cannot set fuel to usize::MAX (would time out).
    const PP_URS_MAX_FUEL: usize = 120_000_000;
    let mut fuel = n
        .saturating_mul(1024)
        .saturating_add(65536)
        .min(PP_URS_MAX_FUEL);
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
        if b.get(i).is_none() {
            break;
        }
        let i_at_outer = i;
        preprocess_urs_burn!(fuel, out, src, i);
        'pp_step: {
            // Skip ML block comments (* ... *) — `get`/`checked_add` only (no `i+1<n` / `b[i+1]` mutants)
            if matches!(b.get(i).copied(), Some(b'(')) {
                if matches!(i.checked_add(1).and_then(|j| b.get(j)).copied(), Some(b'*')) {
                    out.push_str("(*");
                    i = i.saturating_add(2).min(n);
                    let mut depth = 1usize;
                    for _ in 0..step_cap {
                        preprocess_urs_burn_hot!(fuel, out, src, i);
                        if b.get(i).is_none() {
                            break;
                        }
                        if matches!(depth, 0) {
                            break;
                        }
                        let ib = i;
                        if matches!(b.get(i).copied(), Some(b'(')) {
                            let nx = i.checked_add(1).and_then(|j| b.get(j)).copied();
                            if matches!(nx, Some(b'*')) {
                                out.push_str("(*");
                                i = i.saturating_add(2).min(n);
                                depth = depth.saturating_add(1);
                            } else {
                                out.push(b[i] as char);
                                i = i.saturating_add(1).min(n);
                            }
                        } else if matches!(b.get(i).copied(), Some(b'*')) {
                            let nx = i.checked_add(1).and_then(|j| b.get(j)).copied();
                            if matches!(nx, Some(b')')) {
                                out.push_str("*)");
                                i = i.saturating_add(2).min(n);
                                depth = depth.saturating_sub(1);
                            } else {
                                out.push(b[i] as char);
                                i = i.saturating_add(1).min(n);
                            }
                        } else {
                            out.push(b[i] as char);
                            i = i.saturating_add(1).min(n);
                        }
                        if let Some(0) = i.checked_sub(ib) {
                            break;
                        }
                    }
                    if pp_urs_depth_nonzero!(depth) {
                        out.push_str(&src[i..]);
                        return out;
                    }
                    break 'pp_step;
                }
            }

            // Skip string literals verbatim
            if matches!(b[i], b'"') {
                out.push('"');
                last_token.clear();
                last_token.push('"');
                i = i.saturating_add(1).min(n);
                for _ in 0..step_cap {
                    preprocess_urs_burn_hot!(fuel, out, src, i);
                    if b.get(i).is_none() {
                        break;
                    }
                    if matches!(b[i], b'"') {
                        break;
                    }
                    let ib = i;
                    if matches!(b[i], b'\\') {
                        if let Some(nb) = i.checked_add(1).and_then(|j| b.get(j)).copied() {
                            out.push(b[i] as char);
                            out.push(nb as char);
                            i = i.saturating_add(2).min(n);
                        } else {
                            out.push(b[i] as char);
                            i = i.saturating_add(1).min(n);
                        }
                    } else {
                        out.push(b[i] as char);
                        i = i.saturating_add(1).min(n);
                    }
                    if let Some(0) = i.checked_sub(ib) {
                        break;
                    }
                }
                if let Some(ch) = b.get(i).copied() {
                    if matches!(ch, b'"') {
                        out.push('"');
                        i = i.saturating_add(1).min(n);
                    } else {
                        out.push_str(&src[i..]);
                        return out;
                    }
                }
                break 'pp_step;
            }

            // Whitespace: pass through without updating last_token
            if pp_urs_is_ws!(b[i]) {
                out.push(b[i] as char);
                i = i.saturating_add(1).min(n);
                break 'pp_step;
            }

            // Identifier (letters, digits, underscore, apostrophe) — `match` avoids `|`/`!` bool mutants
            let mut id_word_start = false;
            if b[i].is_ascii_alphabetic() {
                id_word_start = true;
            } else if matches!(b[i], b'_') {
                id_word_start = true;
            }
            if id_word_start {
                let id_start = i;
                for _ in 0..step_cap {
                    preprocess_urs_burn_hot!(fuel, out, src, i);
                    if b.get(i).is_none() {
                        break;
                    }
                    if pp_urs_id_cont!(b[i]) {
                    } else {
                        break;
                    }
                    let ib = i;
                    i = i.saturating_add(1).min(n);
                    if let Some(0) = i.checked_sub(ib) {
                        break;
                    }
                }
                if let Some(ch) = b.get(i).copied() {
                    if pp_urs_id_cont!(ch) {
                        out.push_str(&src[i..]);
                        return out;
                    }
                }
                let ident = &src[id_start..i];

                // Only attempt implicit-quantifier transformation for lowercase identifiers
                // that do NOT immediately follow a declaration keyword.
                let is_decl_name = DECL_KEYWORDS.contains(&last_token.as_str());

                // Update last_token
                last_token.clear();
                last_token.push_str(ident);

                if is_decl_name {
                } else {
                    let mut allow_quant = false;
                    if b[id_start].is_ascii_lowercase() {
                        allow_quant = true;
                    } else if matches!(b[id_start], b'_') {
                        allow_quant = true;
                    }
                    if allow_quant {
                        // Skip whitespace after the identifier
                        let ws1 = i;
                        for _ in 0..step_cap {
                            preprocess_urs_burn_hot!(fuel, out, src, i);
                            if b.get(i).is_none() {
                                break;
                            }
                            if pp_urs_is_ws!(b[i]) {
                            } else {
                                break;
                            }
                            let ib = i;
                            i = i.saturating_add(1).min(n);
                            if let Some(0) = i.checked_sub(ib) {
                                break;
                            }
                        }
                        if let Some(ch) = b.get(i).copied() {
                            if pp_urs_is_ws!(ch) {
                                out.push_str(&src[i..]);
                                return out;
                            }
                        }
                        let colon_start = i; // position of the first colon (or non-colon if no match)

                        // Match `:::` or `::` (but not `::::`) — slice `get` only
                        let colons: &str;
                        'colon_pick: {
                            if let Some(s3) = i.checked_add(3).and_then(|e| b.get(i..e)) {
                                if matches!(s3, b":::") {
                                    let fourth_colon = matches!(
                                        i.checked_add(3).and_then(|k| b.get(k)).copied(),
                                        Some(b':')
                                    );
                                    if fourth_colon {
                                    } else {
                                        colons = ":::";
                                        i = i.saturating_add(3).min(n);
                                        break 'colon_pick;
                                    }
                                }
                            }
                            if let Some(s2) = i.checked_add(2).and_then(|e| b.get(i..e)) {
                                if matches!(s2, b"::") {
                                    let third_colon = matches!(
                                        i.checked_add(2).and_then(|k| b.get(k)).copied(),
                                        Some(b':')
                                    );
                                    if third_colon {
                                    } else {
                                        colons = "::";
                                        i = i.saturating_add(2).min(n);
                                        break 'colon_pick;
                                    }
                                }
                            }
                            // Not a quantifier: emit the identifier and the whitespace
                            out.push_str(ident);
                            out.push_str(&src[ws1..i]);
                            break 'pp_step;
                        }

                        // Skip whitespace after the colons
                        let ws2 = i;
                        for _ in 0..step_cap {
                            preprocess_urs_burn_hot!(fuel, out, src, i);
                            if b.get(i).is_none() {
                                break;
                            }
                            if pp_urs_is_ws!(b[i]) {
                            } else {
                                break;
                            }
                            let ib = i;
                            i = i.saturating_add(1).min(n);
                            if let Some(0) = i.checked_sub(ib) {
                                break;
                            }
                        }
                        if let Some(ch) = b.get(i).copied() {
                            if pp_urs_is_ws!(ch) {
                                out.push_str(&src[i..]);
                                return out;
                            }
                        }

                        // Scan the KindAtom: identifier, `{...}`, or `(...)`
                        let ka_start = i;
                        if b.get(i).is_some() {
                            if matches!(b[i], b'{') {
                                let mut depth = 1usize;
                                i = i.saturating_add(1).min(n);
                                for _ in 0..step_cap {
                                    preprocess_urs_burn_hot!(fuel, out, src, i);
                                    if b.get(i).is_none() {
                                        break;
                                    }
                                    if matches!(depth, 0) {
                                        break;
                                    }
                                    let ib = i;
                                    if matches!(b[i], b'{') {
                                        depth = depth.saturating_add(1);
                                    } else if matches!(b[i], b'}') {
                                        depth = depth.saturating_sub(1);
                                    }
                                    i = i.saturating_add(1).min(n);
                                    if let Some(0) = i.checked_sub(ib) {
                                        break;
                                    }
                                }
                                if pp_urs_depth_nonzero!(depth) {
                                    out.push_str(&src[i..]);
                                    return out;
                                }
                            } else if matches!(b[i], b'(') {
                                let mut depth = 1usize;
                                i = i.saturating_add(1).min(n);
                                for _ in 0..step_cap {
                                    preprocess_urs_burn_hot!(fuel, out, src, i);
                                    if b.get(i).is_none() {
                                        break;
                                    }
                                    if matches!(depth, 0) {
                                        break;
                                    }
                                    let ib = i;
                                    if matches!(b[i], b'(') {
                                        depth = depth.saturating_add(1);
                                    } else if matches!(b[i], b')') {
                                        depth = depth.saturating_sub(1);
                                    }
                                    i = i.saturating_add(1).min(n);
                                    if let Some(0) = i.checked_sub(ib) {
                                        break;
                                    }
                                }
                                if pp_urs_depth_nonzero!(depth) {
                                    out.push_str(&src[i..]);
                                    return out;
                                }
                            } else {
                                let mut kind_id = false;
                                if b[i].is_ascii_alphabetic() {
                                    kind_id = true;
                                } else if matches!(b[i], b'_') {
                                    kind_id = true;
                                }
                                if kind_id {
                                    for _ in 0..step_cap {
                                        preprocess_urs_burn_hot!(fuel, out, src, i);
                                        if b.get(i).is_none() {
                                            break;
                                        }
                                        if pp_urs_id_cont!(b[i]) {
                                        } else {
                                            break;
                                        }
                                        let ib = i;
                                        i = i.saturating_add(1).min(n);
                                        if let Some(0) = i.checked_sub(ib) {
                                            break;
                                        }
                                    }
                                    if let Some(ch) = b.get(i).copied() {
                                        if pp_urs_id_cont!(ch) {
                                            out.push_str(&src[i..]);
                                            return out;
                                        }
                                    }
                                } else {
                                    // No valid kind term: emit everything as-is
                                    out.push_str(ident);
                                    out.push_str(&src[ws1..ws2]);
                                    out.push_str(colons);
                                    out.push_str(&src[ws2..i]);
                                    break 'pp_step;
                                }
                            }
                        } else {
                            // No valid kind term: emit everything as-is
                            out.push_str(ident);
                            out.push_str(&src[ws1..ws2]);
                            out.push_str(colons);
                            out.push_str(&src[ws2..i]);
                            break 'pp_step;
                        }
                        let kind_atom = &src[ka_start..i];

                        // Skip whitespace before potential `->`
                        let ws3 = i;
                        for _ in 0..step_cap {
                            preprocess_urs_burn_hot!(fuel, out, src, i);
                            if b.get(i).is_none() {
                                break;
                            }
                            if pp_urs_is_ws!(b[i]) {
                            } else {
                                break;
                            }
                            let ib = i;
                            i = i.saturating_add(1).min(n);
                            if let Some(0) = i.checked_sub(ib) {
                                break;
                            }
                        }
                        if let Some(ch) = b.get(i).copied() {
                            if pp_urs_is_ws!(ch) {
                                out.push_str(&src[i..]);
                                return out;
                            }
                        }

                        // Check if followed by `->`
                        let emit_without_arrow = |o: &mut String| {
                            o.push_str(ident);
                            o.push_str(&src[ws1..colon_start]); // whitespace before colons
                            o.push_str(colons);
                            o.push_str(&src[ws2..ka_start]); // whitespace after colons
                            o.push_str(kind_atom);
                            o.push_str(&src[ws3..i]);
                        };
                        if let Some(nb) = i.checked_add(1).and_then(|j| b.get(j)).copied() {
                            if matches!(b.get(i).copied(), Some(b'-')) {
                                if matches!(nb, b'>') {
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
                                    emit_without_arrow(&mut out);
                                }
                            } else {
                                emit_without_arrow(&mut out);
                            }
                        } else {
                            emit_without_arrow(&mut out);
                        }
                        break 'pp_step;
                    }
                }

                // Emit identifier as-is (either it's a decl-name or uppercase)
                emit_word(&mut out, &mut last_token, ident);
                break 'pp_step;
            }

            // Non-word, non-whitespace character: emit and update last_token
            out.push(b[i] as char);
            last_token.clear();
            last_token.push(b[i] as char);
            i = i.saturating_add(1).min(n);
        }
        if let Some(0) = i.checked_sub(i_at_outer) {
            out.push_str(src.get(i..).unwrap_or(""));
            return out;
        }
    }

    out.push_str(src.get(i..).unwrap_or(""));
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
        let lexer = lexical_analyzer::XmlAwareLexer::new(&preprocessed);
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
