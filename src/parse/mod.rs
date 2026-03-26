//! Parser for Ur/Web source files.
//!
//! - **parse_ur**: parse `.ur` files into `source::File`
//! - **parse_urs**: parse `.urs` signature files
//! - **lexer**: tokenization (Logos)
//!
//! ## Strict recognition (LangSec-oriented)
//!
//! - **CFG gate**: This crate's `build.rs` runs LALRPOP on every build; shift/reduce and
//!   reduce/reduce conflicts **fail the build** — the surface language is not treated
//!   as “best effort” at table generation time.
//! - **Lexer**: invalid or unterminated literals yield [`lexical_analyzer::LexError`];
//!   there is no silent recovery into a token stream.
//! - **Expression spine**: [`expr_langsec`] defines the reference recognizer for the
//!   comparison → arithmetic → juxtaposition tier; grammar actions that fold AST
//!   nodes use explicit [`Result`] paths (e.g. fallible `=>?`) where an invariant
//!   could be broken instead of panicking in the parser.
//!   **Regression lock:** after changing `ArithExp` / precedence in `grammar.lalrpop`, extend
//!   [`expr_langsec`] and `tests::langsec_spine_equiv` in this module so the CFG stays aligned
//!   with the recognizer (LangSec: one formal language for the spine).
//!
//! ## Preprocess ∘ parse (composed surface language)
//!
//! The **accepted** `.ur` text is not only `L(grammar)` on raw bytes; it is the
//! preimage of that grammar under a **specified** preprocessor chain:
//!
//! 1. **`.ur`**: `rewrite_datatype_constructors` → `rewrite_sgn_where` → `rewrite_case_expressions`,
//!    then [`parse_ur`](parse_ur) runs [`XmlAwareLexer`](lexical_analyzer::XmlAwareLexer) + `FileParser`.
//! 2. **`.urs`**: [`preprocess_urs`](preprocess_urs) (fuel-bounded), then lexer + `SgnItemsParser`.
//!
//! These rewrites are **total** string transducers on UTF-8 (invalid surrogate-edge cases are
//! ordinary char iteration). [`preprocess_urs`](preprocess_urs) can truncate with the remainder
//! appended if fuel exhausts — documented in its body. Integration tests in `tests/langsec_preprocess.rs`
//! pin representative rewrite + parse behavior.

pub mod expr_langsec;
pub mod grammar_helpers;
pub mod lexical_analyzer;
pub mod xml_helpers;

// `build.rs` always runs LALRPOP and sets `cargo:rustc-cfg=generated_parser` on success.
#[cfg(generated_parser)]
mod grammar {
    include!(concat!(env!("OUT_DIR"), "/parse/grammar.rs"));
}

use crate::error_types::{CompileError, ErrorReporter, Span};
use crate::source::{File, LocSgnItem};

#[cfg(test)]
static PREPROCESS_URS_FUEL_TEST_OVERRIDE: std::sync::Mutex<Option<usize>> =
    std::sync::Mutex::new(None);

/// Test-only: override initial fuel for the next [`preprocess_urs`] call(s). Pass `None` to disable.
#[cfg(test)]
pub fn test_set_preprocess_urs_fuel_override(fuel: Option<usize>) {
    *PREPROCESS_URS_FUEL_TEST_OVERRIDE.lock().unwrap() = fuel;
}

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

fn pp_kw_cont(c: u8) -> bool {
    matches!(
        c,
        b'_' | b'\'' | b'0'..=b'9' | b'a'..=b'z' | b'A'..=b'Z'
    )
}

fn is_case_keyword(b: &[u8], i: usize) -> bool {
    if i + 4 > b.len() || &b[i..i + 4] != b"case" {
        return false;
    }
    if i > 0 && pp_kw_cont(b[i - 1]) {
        return false;
    }
    if i + 4 < b.len() && pp_kw_cont(b[i + 4]) {
        return false;
    }
    true
}

fn is_of_keyword(b: &[u8], i: usize) -> bool {
    if i + 2 > b.len() || &b[i..i + 2] != b"of" {
        return false;
    }
    if i > 0 && pp_kw_cont(b[i - 1]) {
        return false;
    }
    if i + 2 < b.len() && pp_kw_cont(b[i + 2]) {
        return false;
    }
    true
}

fn skip_ml_comment_bytes(b: &[u8], mut i: usize, n: usize) -> usize {
    let mut depth = 1usize;
    while i < n && depth > 0 {
        if i + 1 < n && b[i] == b'(' && b[i + 1] == b'*' {
            i += 2;
            depth += 1;
        } else if i + 1 < n && b[i] == b'*' && b[i + 1] == b')' {
            i += 2;
            depth -= 1;
        } else {
            i += 1;
        }
    }
    i
}

fn skip_string_bytes(b: &[u8], mut i: usize, n: usize) -> usize {
    while i < n {
        if b[i] == b'"' {
            return i + 1;
        }
        if b[i] == b'\\' && i + 1 < n {
            i += 2;
        } else {
            i += 1;
        }
    }
    n
}

/// Byte index just after the `of` in `case` ⟨scrutinee⟩ `of`, or `None` if unterminated.
fn scan_case_of_end(b: &[u8], mut i: usize, n: usize) -> Option<usize> {
    let mut depth = 0i32;
    while i < n {
        if i + 1 < n && b[i] == b'(' && b[i + 1] == b'*' {
            i = skip_ml_comment_bytes(b, i + 2, n);
            continue;
        }
        if b[i] == b'"' {
            i = skip_string_bytes(b, i + 1, n);
            continue;
        }
        if depth == 0 && is_of_keyword(b, i) {
            return Some(i + 2);
        }
        match b.get(i).copied() {
            Some(b'(' | b'[' | b'{') => {
                depth += 1;
                i += 1;
            }
            Some(b')' | b']' | b'}') => {
                depth = (depth - 1).max(0);
                i += 1;
            }
            Some(_) => i += 1,
            None => break,
        }
    }
    None
}

fn arm_sep_at(b: &[u8], i: usize, n: usize) -> bool {
    if i + 8 > n || &b[i..i + 8] != b"arm_sep" {
        return false;
    }
    match b.get(i + 8).copied() {
        None => true,
        Some(c) => !pp_kw_cont(c),
    }
}

fn case_end_at(b: &[u8], i: usize, n: usize) -> bool {
    if i + 8 > n || &b[i..i + 8] != b"case_end" {
        return false;
    }
    match b.get(i + 8).copied() {
        None => true,
        Some(c) => !pp_kw_cont(c),
    }
}

fn case_bar_at(b: &[u8], i: usize, n: usize) -> bool {
    if i + 8 > n || &b[i..i + 8] != b"case_bar" {
        return false;
    }
    match b.get(i + 8).copied() {
        None => true,
        Some(c) => !pp_kw_cont(c),
    }
}

fn emit_ws_comments_prefix(out: &mut String, input: &str, b: &[u8], i: &mut usize, n: usize) {
    while *i < n {
        if pp_urs_is_ws!(b[*i]) {
            out.push(b[*i] as char);
            *i += 1;
            continue;
        }
        if *i + 1 < n && b[*i] == b'(' && b[*i + 1] == b'*' {
            let start = *i;
            *i = skip_ml_comment_bytes(b, *i + 2, n);
            out.push_str(&input[start..*i]);
            continue;
        }
        if b[*i] == b'"' {
            let start = *i;
            *i = skip_string_bytes(b, *i + 1, n);
            out.push_str(&input[start..*i]);
            continue;
        }
        break;
    }
}

/// Pass-through scan (legacy hook): `case`/`of` arm rewriting is done in
/// `rewrite_case_arm_separators` to match `urweb.grm` `barOpt branch branchs` — no forced
/// `arm_sep` after every `of`.
pub fn rewrite_case_leading_bars(input: &str) -> String {
    input.to_string()
}

/// After each `case … of | …`, replace subsequent arm-separator `|` at arm-body depth 0 with
/// `arm_sep` (see `grammar.lalrpop` `CaseArmSep`). Pattern scan stops at the first `=>` at
/// paren depth 0; bodies treat `(* … *)` and `"…"` like the leading-bar pass.  Patterns with
/// top-level `|` (or-pats) can confuse this pass — parenthesize if needed.
pub fn rewrite_case_arm_separators(input: &str) -> String {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum BodyStop {
        NextArm,
        CaseDone,
    }

    fn copy_ml_comment(out: &mut String, input: &str, b: &[u8], mut i: usize, n: usize) -> usize {
        let start = i;
        i = skip_ml_comment_bytes(b, i + 2, n);
        out.push_str(&input[start..i]);
        i
    }

    fn copy_string(out: &mut String, input: &str, b: &[u8], mut i: usize, n: usize) -> usize {
        let start = i;
        i = skip_string_bytes(b, i + 1, n);
        out.push_str(&input[start..i]);
        i
    }

    /// Copy [i..] to `out` until `=>` at `depth==0`, return index after `=>`.
    fn scan_pat_to_arrow(
        out: &mut String,
        input: &str,
        b: &[u8],
        mut i: usize,
        n: usize,
    ) -> Option<usize> {
        let mut depth = 0i32;
        while i < n {
            if i + 1 < n && b[i] == b'(' && b[i + 1] == b'*' {
                i = copy_ml_comment(out, input, b, i, n);
                continue;
            }
            if b[i] == b'"' {
                i = copy_string(out, input, b, i, n);
                continue;
            }
            if depth == 0 && i + 1 < n && b[i] == b'=' && b[i + 1] == b'>' {
                out.push_str("=>");
                return Some(i + 2);
            }
            match b[i] {
                b'(' | b'[' | b'{' => {
                    out.push(b[i] as char);
                    depth += 1;
                    i += 1;
                }
                b')' | b']' | b'}' => {
                    out.push(b[i] as char);
                    depth = (depth - 1).max(0);
                    i += 1;
                }
                _ => {
                    let ch = input[i..].chars().next()?;
                    out.push(ch);
                    i += ch.len_utf8();
                }
            }
        }
        None
    }

    /// Scan a case arm body, writing raw text to a local buffer.
    /// Returns `(stop_pos, stop_reason, body_text)`.
    ///
    /// Stops (does NOT consume) at:
    ///  - `arm_sep` / `|` at depth 0              → NextArm
    ///  - `)` / `]` / `}` at depth 0             → CaseDone (closes enclosing bracket)
    ///  - `in` / `end` of enclosing `let`         → CaseDone
    ///  - `fun` / `val` / `and` at depth 0        → CaseDone (new top-level decl)
    ///
    /// `;` is NOT a stop — it sequences monadic actions within an arm body.
    /// Nested case expressions' `|` separators are inside bracketed subterms or
    /// will be handled by the recursive rewrite applied to the returned body.
    fn scan_body(
        input: &str,
        b: &[u8],
        mut i: usize,
        n: usize,
    ) -> Option<(usize, BodyStop, String)> {
        let mut body = String::new();
        let mut depth = 0i32;
        let mut let_depth = 0i32; // tracks open `let` keywords
        while i < n {
            if i + 1 < n && b[i] == b'(' && b[i + 1] == b'*' {
                i = copy_ml_comment(&mut body, input, b, i, n);
                continue;
            }
            if b[i] == b'"' {
                i = copy_string(&mut body, input, b, i, n);
                continue;
            }
            if depth == 0 && arm_sep_at(b, i, n) {
                return Some((i, BodyStop::NextArm, body));
            }
            if depth == 0 && case_end_at(b, i, n) {
                return Some((i, BodyStop::CaseDone, body));
            }
            if depth == 0 && b[i] == b'|' {
                return Some((i, BodyStop::NextArm, body));
            }
            // `)` / `]` / `}` at depth 0 close an enclosing bracket → arm ends
            if depth == 0 && matches!(b[i], b')' | b']' | b'}') {
                return Some((i, BodyStop::CaseDone, body));
            }
            // Keyword tracking at bracket depth 0
            if depth == 0 && pp_kw_word_at(b, i, n, b"let") {
                body.push_str("let");
                i += 3;
                let_depth += 1;
                continue;
            }
            if depth == 0 && pp_kw_word_at(b, i, n, b"in") {
                if let_depth > 0 {
                    body.push_str("in");
                    i += 2;
                } else {
                    return Some((i, BodyStop::CaseDone, body));
                }
                continue;
            }
            if depth == 0 && pp_kw_word_at(b, i, n, b"end") {
                if let_depth > 0 {
                    body.push_str("end");
                    i += 3;
                    let_depth -= 1;
                } else {
                    return Some((i, BodyStop::CaseDone, body));
                }
                continue;
            }
            // Top-level declaration keywords (only safe ones unlikely to appear in XML text)
            if depth == 0 && let_depth == 0 {
                for kw in &[b"fun" as &[u8], b"val", b"and"] {
                    if pp_kw_word_at(b, i, n, kw) {
                        return Some((i, BodyStop::CaseDone, body));
                    }
                }
            }
            match b[i] {
                b'(' | b'[' | b'{' => {
                    body.push(b[i] as char);
                    depth += 1;
                    i += 1;
                }
                b')' | b']' | b'}' => {
                    // depth > 0 here (checked depth==0 above); decrement
                    body.push(b[i] as char);
                    depth -= 1;
                    i += 1;
                }
                _ => {
                    let ch = input[i..].chars().next()?;
                    body.push(ch);
                    i += ch.len_utf8();
                }
            }
        }
        Some((i, BodyStop::CaseDone, body))
    }

    let b = input.as_bytes();
    let n = b.len();
    let mut out = String::with_capacity(n.saturating_add(32));
    let mut i = 0usize;
    let cap = n.saturating_add(1);
    for _ in 0..cap {
        if i >= n {
            break;
        }
        if i + 1 < n && b[i] == b'(' && b[i + 1] == b'*' {
            let start = i;
            i = skip_ml_comment_bytes(b, i + 2, n);
            out.push_str(&input[start..i]);
            continue;
        }
        if b[i] == b'"' {
            let start = i;
            i = skip_string_bytes(b, i + 1, n);
            out.push_str(&input[start..i]);
            continue;
        }
        if is_case_keyword(b, i) {
            let after_case = i + 4;
            if let Some(after_of) = scan_case_of_end(b, after_case, n) {
                out.push_str(&input[i..after_of]);
                let mut j = after_of;
                emit_ws_comments_prefix(&mut out, input, b, &mut j, n);
                // `urweb.grm` `barOpt`: optional leading `|` — `case_bar`, never `arm_sep`.
                if case_bar_at(b, j, n) {
                    out.push_str(&input[j..j + 8]);
                    j += 8;
                } else if arm_sep_at(b, j, n) {
                    out.push_str(" case_bar ");
                    j += 8;
                } else if b.get(j) == Some(&b'|') {
                    out.push_str(" case_bar ");
                    j += 1;
                }
                emit_ws_comments_prefix(&mut out, input, b, &mut j, n);
                loop {
                    let Some(after_arrow) = scan_pat_to_arrow(&mut out, input, b, j, n) else {
                        out.push_str(&input[j..]);
                        return out;
                    };
                    j = after_arrow;
                    let Some((stop_i, stop, raw_body)) = scan_body(input, b, j, n) else {
                        out.push_str(&input[j..]);
                        return out;
                    };
                    j = stop_i;
                    // Recursively preprocess nested case expressions within the arm body
                    out.push_str(&rewrite_case_arm_separators(&raw_body));
                    match stop {
                        BodyStop::CaseDone => {
                            if case_end_at(b, j, n) {
                                out.push_str(&input[j..j + 8]);
                                i = j + 8;
                            } else {
                                out.push_str(" case_end ");
                                i = j;
                            }
                            break;
                        }
                        BodyStop::NextArm => {
                            if arm_sep_at(b, j, n) {
                                out.push_str(&input[j..j + 8]);
                                j += 8;
                                emit_ws_comments_prefix(&mut out, input, b, &mut j, n);
                                continue;
                            }
                            if b.get(j) == Some(&b'|') {
                                out.push_str(" arm_sep ");
                                j += 1;
                                emit_ws_comments_prefix(&mut out, input, b, &mut j, n);
                                continue;
                            }
                            out.push_str(&input[j..]);
                            return out;
                        }
                    }
                }
                continue;
            }
        }
        let Some(ch) = input[i..].chars().next() else {
            break;
        };
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

pub fn rewrite_case_expressions(src: &str) -> String {
    rewrite_case_arm_separators(&rewrite_case_leading_bars(src))
}

/// Rewrite bare kind binders `nm :: KindExpr ->` to `[nm :: KindExpr] ->`.
///
/// In Ur/Web, `nm :: K -> C` is valid at the constructor level (equivalent to `[nm :: K] -> C`).
/// Adding this as a grammar rule causes LR(1) conflicts because `IDENT` is used for both
/// `AtomConNode` and `KindAtom`.  The preprocessor handles the common case by scanning for
/// `lowercase-ident :: kind ->` patterns and wrapping in brackets.
pub fn rewrite_bare_kind_binders(src: &str) -> String {
    let b = src.as_bytes();
    let n = b.len();
    let mut out = String::with_capacity(n);
    let mut i = 0usize;

    while i < n {
        // Skip ML comments
        if i + 1 < n && b[i] == b'(' && b[i + 1] == b'*' {
            let start = i;
            i = skip_ml_comment_bytes(b, i + 2, n);
            out.push_str(&src[start..i]);
            continue;
        }
        // Skip strings
        if b[i] == b'"' {
            let start = i;
            i = skip_string_bytes(b, i + 1, n);
            out.push_str(&src[start..i]);
            continue;
        }
        // Check for lowercase ident
        if b[i].is_ascii_lowercase() || b[i] == b'_' {
            // Require word boundary on left
            if i > 0 && pp_kw_cont(b[i - 1]) {
                out.push(b[i] as char);
                i += 1;
                continue;
            }
            // Scan identifier
            let id_start = i;
            while i < n && pp_kw_cont(b[i]) {
                i += 1;
            }
            let id = &src[id_start..i];
            // Skip whitespace
            let ws_start = i;
            while i < n && matches!(b[i], b' ' | b'\t' | b'\n' | b'\r') {
                i += 1;
            }
            let ws1 = &src[ws_start..i];
            // Check for `::` (not `:::`)
            if i + 2 <= n && &b[i..i + 2] == b"::" && b.get(i + 2).copied() != Some(b':') {
                i += 2;
                // Skip whitespace after ::
                let ws2_start = i;
                while i < n && matches!(b[i], b' ' | b'\t') {
                    i += 1;
                }
                let ws2 = &src[ws2_start..i];
                // Scan kind expression: tokens until `->` at bracket depth 0
                let kind_start = i;
                let mut depth = 0i32;
                let mut found_arrow = false;
                let mut arrow_pos = i;
                let mut j = i;
                while j < n {
                    if j + 1 < n && b[j] == b'(' && b[j + 1] == b'*' {
                        j = skip_ml_comment_bytes(b, j + 2, n);
                        continue;
                    }
                    if b[j] == b'"' {
                        j = skip_string_bytes(b, j + 1, n);
                        continue;
                    }
                    if matches!(b[j], b'(' | b'[' | b'{') {
                        depth += 1;
                        j += 1;
                        continue;
                    }
                    if matches!(b[j], b')' | b']' | b'}') {
                        depth -= 1;
                        if depth < 0 {
                            break;
                        }
                        j += 1;
                        continue;
                    }
                    if depth == 0 && j + 2 <= n && &b[j..j + 2] == b"->" {
                        found_arrow = true;
                        arrow_pos = j;
                        break;
                    }
                    // Stop at tokens that can't appear in a kind at depth 0
                    if depth == 0 && matches!(b[j], b',' | b'=' | b'|' | b';') {
                        break;
                    }
                    j += 1;
                }
                if found_arrow {
                    let kind_text = src[kind_start..arrow_pos].trim_end();
                    out.push('[');
                    out.push_str(id);
                    out.push_str(ws1);
                    out.push_str("::");
                    out.push_str(ws2);
                    out.push_str(kind_text);
                    out.push_str("] -> ");
                    i = arrow_pos + 2;
                    while i < n && matches!(b[i], b' ' | b'\t') {
                        i += 1;
                    }
                    continue;
                } else {
                    // No arrow: emit id, whitespace, `::`, whitespace as-is
                    out.push_str(id);
                    out.push_str(ws1);
                    out.push_str("::");
                    out.push_str(ws2);
                    // i is already at kind_start
                    continue;
                }
            } else {
                out.push_str(id);
                out.push_str(ws1);
                // i is already past ws1
                continue;
            }
        }
        let ch = src[i..].chars().next().unwrap_or('\0');
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

/// Strip SQL table-constraint continuation lines from `.ur` source.
///
/// In Ur/Web, `table name : {fields}` declarations may be followed by indented
/// SQL constraint clauses (`PRIMARY KEY ...`, `CONSTRAINT ...`, `UNIQUE ...`, `CHECK ...`).
/// These clauses are not part of the Ur/Web AST but are SQL DDL extras.  The Rust
/// parser would otherwise consume the UIDENT tokens as constructor applications of
/// the table type.  Stripping them here keeps the grammar simple.
///
/// We replace each constraint line with a blank line to preserve line numbers.
pub fn strip_table_constraints(src: &str) -> String {
    fn is_constraint_line(trimmed: &str) -> bool {
        trimmed.starts_with("PRIMARY ")
            || trimmed.starts_with("PRIMARY\t")
            || trimmed.starts_with("CONSTRAINT ")
            || trimmed.starts_with("CONSTRAINT\t")
            || trimmed.starts_with("UNIQUE ")
            || trimmed.starts_with("UNIQUE\t")
            || trimmed.starts_with("CHECK ")
            || trimmed.starts_with("CHECK\t")
    }

    let mut result = String::with_capacity(src.len());
    for line in src.split('\n') {
        let trimmed = line.trim_start();
        if !trimmed.is_empty() && is_constraint_line(trimmed) {
            // Replace with blank line preserving line count
            result.push('\n');
        } else {
            result.push_str(line);
            result.push('\n');
        }
    }
    // Remove the trailing extra newline we added (split produces N+1 pieces for N newlines)
    if result.ends_with('\n') && !src.ends_with('\n') {
        result.pop();
    } else if result.ends_with("\n\n") && src.ends_with('\n') {
        result.pop();
    }
    result
}

fn pp_kw_word_at(b: &[u8], i: usize, n: usize, word: &[u8]) -> bool {
    if i + word.len() > n || &b[i..i + word.len()] != word {
        return false;
    }
    if i > 0 && pp_kw_cont(b[i - 1]) {
        return false;
    }
    let after = i + word.len();
    if after < n && pp_kw_cont(b[after]) {
        return false;
    }
    true
}

/// Rewrite SQL-context expression splices `{expr}` → `(expr)` when the content is NOT a record.
///
/// Ur/Web allows `{expr}` inside SQL expressions (SELECT/WHERE/etc.) to splice a Ur/Web value.
/// The LR(1) grammar can't distinguish `{field = val}` (record) from `{expr}` (SQL splice)
/// in a single lookahead. This pass converts the SQL-splice form to `(expr)` which is
/// unambiguously a parenthesized expression.
///
/// Heuristic: a `{...}` block is a SQL splice if, after skipping whitespace/comments, the first
/// non-ws token is NOT followed by `=` (record field separator) and is NOT `...` or `}`.
pub fn rewrite_sql_brace_splices(input: &str) -> String {
    let b = input.as_bytes();
    let n = b.len();
    let mut out = String::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        // Skip comments
        if i + 1 < n && b[i] == b'(' && b[i + 1] == b'*' {
            let start = i;
            i = skip_ml_comment_bytes(b, i + 2, n);
            out.push_str(&input[start..i]);
            continue;
        }
        // Skip strings
        if b[i] == b'"' {
            let start = i;
            i = skip_string_bytes(b, i + 1, n);
            out.push_str(&input[start..i]);
            continue;
        }
        if b[i] != b'{' {
            let ch = input[i..].chars().next().unwrap_or('\0');
            out.push(ch);
            i += ch.len_utf8();
            continue;
        }
        // Found `{`. Check what follows to decide if it's a SQL splice.
        // If next non-ws is `[` → SQL text splice `{[...]}` handled by grammar, leave alone.
        // If next non-ws is `}` → empty record, leave alone.
        // If next non-ws is `...` → spread record, leave alone.
        // If next non-ws is ident/UIDENT followed by `=` → record field, leave alone.
        // Otherwise → SQL splice: emit `(` instead of `{` and `)` instead of matching `}`.
        let mut j = i + 1;
        while j < n && pp_urs_is_ws!(b[j]) {
            j += 1;
        }
        // Skip comment
        if j + 1 < n && b[j] == b'(' && b[j + 1] == b'*' {
            j = skip_ml_comment_bytes(b, j + 2, n);
            while j < n && pp_urs_is_ws!(b[j]) {
                j += 1;
            }
        }
        let is_sql_splice = if j >= n {
            false
        } else if b[j] == b'[' {
            // `{[...]}` — text splice, leave alone
            false
        } else if b[j] == b'}' {
            // empty record
            false
        } else if j + 2 < n && &b[j..j + 3] == b"..." {
            // spread record
            false
        } else {
            // Check if it's `ident =` (record field)
            let ident_start = j;
            if b[ident_start].is_ascii_alphabetic() || b[ident_start] == b'_' {
                let mut k = ident_start + 1;
                while k < n && (b[k].is_ascii_alphanumeric() || b[k] == b'_' || b[k] == b'\'') {
                    k += 1;
                }
                // Skip whitespace after ident
                while k < n && pp_urs_is_ws!(b[k]) {
                    k += 1;
                }
                // If followed by `=` (but not `=>` or `==`), it's a record field
                if k < n && b[k] == b'=' && (k + 1 >= n || (b[k + 1] != b'>' && b[k + 1] != b'=')) {
                    false // record field
                } else {
                    true // SQL splice
                }
            } else {
                // Starts with something other than ident → likely an expression
                true
            }
        };
        if !is_sql_splice {
            out.push('{');
            i += 1;
            continue;
        }
        // It's a SQL splice: find matching `}` and replace `{` → `(`, `}` → `)`
        out.push('(');
        i += 1;
        let mut depth = 1i32;
        while i < n && depth > 0 {
            if i + 1 < n && b[i] == b'(' && b[i + 1] == b'*' {
                let start = i;
                i = skip_ml_comment_bytes(b, i + 2, n);
                out.push_str(&input[start..i]);
            } else if b[i] == b'"' {
                let start = i;
                i = skip_string_bytes(b, i + 1, n);
                out.push_str(&input[start..i]);
            } else if b[i] == b'{' {
                out.push('(');
                depth += 1;
                i += 1;
            } else if b[i] == b'}' {
                depth -= 1;
                if depth > 0 {
                    out.push(')');
                } else {
                    out.push(')');
                }
                i += 1;
            } else {
                let ch = input[i..].chars().next().unwrap_or('\0');
                out.push(ch);
                i += ch.len_utf8();
            }
        }
    }
    out
}

/// After `datatype` … `=`, rewrite constructor-list `|` and payload `of` to magic tokens so the
/// grammar need not share `|` / `of` with patterns and other constructs (LangSec / LALR).
/// Rewrite keyword `where` for signatures: `sgn_where` at paren depth 0, `sgn_subwhere` when
/// nested in `(...)`, so LR(1) can separate top-level vs inner `Sgn` boundaries.
pub fn rewrite_sgn_where(input: &str) -> String {
    let b = input.as_bytes();
    let n = b.len();
    let mut out = String::with_capacity(n.saturating_add(16));
    let mut i = 0usize;
    let mut paren_depth = 0i32;
    let cap = n.saturating_add(1);
    for _ in 0..cap {
        if i >= n {
            break;
        }
        if i + 1 < n && b[i] == b'(' && b[i + 1] == b'*' {
            let start = i;
            i = skip_ml_comment_bytes(b, i + 2, n);
            out.push_str(&input[start..i]);
            continue;
        }
        if b[i] == b'"' {
            let start = i;
            i = skip_string_bytes(b, i + 1, n);
            out.push_str(&input[start..i]);
            continue;
        }
        if b[i] == b'(' {
            paren_depth += 1;
            out.push('(');
            i += 1;
            continue;
        }
        if b[i] == b')' {
            paren_depth = (paren_depth - 1).max(0);
            out.push(')');
            i += 1;
            continue;
        }
        if pp_kw_word_at(b, i, n, b"where") {
            if paren_depth == 0 {
                out.push_str("sgn_where");
            } else {
                out.push_str("sgn_subwhere");
            }
            i += 5;
            continue;
        }
        let Some(ch) = input[i..].chars().next() else {
            break;
        };
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

pub fn rewrite_datatype_constructors(input: &str) -> String {
    fn find_dtype_equals(input: &str, b: &[u8], mut i: usize, n: usize) -> Option<usize> {
        let mut depth = 0i32;
        while i < n {
            if i + 1 < n && b[i] == b'(' && b[i + 1] == b'*' {
                i = skip_ml_comment_bytes(b, i + 2, n);
                continue;
            }
            if b[i] == b'"' {
                i = skip_string_bytes(b, i + 1, n);
                continue;
            }
            match b[i] {
                b'(' | b'[' | b'{' => {
                    depth += 1;
                    i += 1;
                }
                b')' | b']' | b'}' => {
                    depth = (depth - 1).max(0);
                    i += 1;
                }
                b'=' if depth == 0 => return Some(i),
                _ => {
                    let w = match input.get(i..).and_then(|s| s.chars().next()) {
                        Some(c) => c.len_utf8(),
                        None => return None,
                    };
                    i += w;
                }
            }
        }
        None
    }

    fn rewrite_dt_body(out: &mut String, input: &str, b: &[u8], mut i: usize, n: usize) -> usize {
        let mut depth = 0i32;
        let mut after_uident = false;
        while i < n {
            if i + 1 < n && b[i] == b'(' && b[i + 1] == b'*' {
                let start = i;
                i = skip_ml_comment_bytes(b, i + 2, n);
                out.push_str(&input[start..i]);
                continue;
            }
            if b[i] == b'"' {
                let start = i;
                i = skip_string_bytes(b, i + 1, n);
                out.push_str(&input[start..i]);
                continue;
            }
            if depth == 0 && pp_kw_word_at(b, i, n, b"and") {
                if after_uident {
                    out.push_str(" dt_con0 ");
                }
                out.push_str(" dt_done ");
                return i;
            }
            if depth == 0 && b[i] == b';' {
                if after_uident {
                    out.push_str(" dt_con0 ");
                }
                out.push_str(" dt_done ");
                return i;
            }
            // Stop at a new top-level declaration keyword — happens in `.urs` files
            // where each declaration is separate (not joined by `and`).
            if depth == 0 {
                for kw in &[
                    b"datatype" as &[u8],
                    b"con",
                    b"val",
                    b"fun",
                    b"type",
                    b"class",
                    b"structure",
                    b"signature",
                    b"open",
                    b"constraint",
                    b"table",
                    b"sequence",
                    b"view",
                    b"cookie",
                    b"style",
                    b"task",
                    b"policy",
                    b"include",
                ] {
                    if pp_kw_word_at(b, i, n, kw) {
                        if after_uident {
                            out.push_str(" dt_con0 ");
                        }
                        out.push_str(" dt_done ");
                        return i;
                    }
                }
            }
            if depth == 0 && b[i] == b'|' {
                if after_uident {
                    out.push_str(" dt_con0 ");
                }
                out.push_str(" dt_bar ");
                i += 1;
                after_uident = false;
                continue;
            }
            if depth == 0 && after_uident && pp_kw_word_at(b, i, n, b"of") {
                out.push_str(" dtype_of ");
                i += 2;
                after_uident = false;
                continue;
            }
            if depth == 0 && b[i].is_ascii_uppercase() {
                let start = i;
                i += 1;
                while i < n && (b[i].is_ascii_alphanumeric() || b[i] == b'_' || b[i] == b'\'') {
                    i += 1;
                }
                out.push_str(&input[start..i]);
                after_uident = true;
                continue;
            }
            // Whitespace between an UIDENT and `|` / `of` must NOT reset after_uident,
            // otherwise `Foo | Bar` fails to emit `dt_con0` before `dt_bar`.
            if b[i].is_ascii_whitespace() {
                out.push(b[i] as char);
                i += 1;
                continue;
            }
            after_uident = false;
            match b[i] {
                b'(' | b'[' | b'{' => {
                    out.push(b[i] as char);
                    depth += 1;
                    i += 1;
                }
                b')' | b']' | b'}' => {
                    out.push(b[i] as char);
                    depth = (depth - 1).max(0);
                    i += 1;
                }
                _ => {
                    let Some(ch) = input[i..].chars().next() else {
                        break;
                    };
                    out.push(ch);
                    i += ch.len_utf8();
                }
            }
        }
        if depth == 0 {
            if after_uident {
                out.push_str(" dt_con0 ");
            }
            out.push_str(" dt_done ");
        }
        i
    }

    let b = input.as_bytes();
    let n = b.len();
    let mut out = String::with_capacity(n.saturating_add(64));
    let mut i = 0usize;
    let cap = n.saturating_add(1);
    for _ in 0..cap {
        if i >= n {
            break;
        }
        if i + 1 < n && b[i] == b'(' && b[i + 1] == b'*' {
            let start = i;
            i = skip_ml_comment_bytes(b, i + 2, n);
            out.push_str(&input[start..i]);
            continue;
        }
        if b[i] == b'"' {
            let start = i;
            i = skip_string_bytes(b, i + 1, n);
            out.push_str(&input[start..i]);
            continue;
        }
        if pp_kw_word_at(b, i, n, b"datatype") {
            let start = i;
            i += b"datatype".len();
            if let Some(eq) = find_dtype_equals(input, b, i, n) {
                out.push_str(&input[start..eq]);
                out.push('=');
                i = eq + 1;
                i = rewrite_dt_body(&mut out, input, b, i, n);
                continue;
            }
            out.push_str(&input[start..i]);
            continue;
        }
        let Some(ch) = input[i..].chars().next() else {
            break;
        };
        out.push(ch);
        i += ch.len_utf8();
    }
    out
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
///
/// ## Signature `LTYPE` / `CON` alignment (`urweb.lex`)
/// The reference lexer maps `type` → `LTYPE` and `con` → `CON`. Bare abstract
/// `type t` and default `class c` lines would require optional-empty LR slices
/// next to `=` / `::` continuations. We rewrite **simple** lines (no `=`, no `::`)
/// so the CFG stays single-recognizer strict:
/// - `type t` → `con t :: Type`
/// - `class c` → `class c :: Type -> Type` (default kind, matching `SgiClassAbs`)
///
/// ## Signature `con` / `class` kind definitions (`sgn_def_con`)
/// After `:: Kind`, the grammar expects a dedicated keyword `sgn_def_con` before the
/// defining `Con` so `=` is not overloaded and no ε competes with the RHS. Source
/// files still write ordinary `=`; we rewrite the first defining `=` after `::` on
/// `con` / `class` lines to `sgn_def_con`.
///
/// Line-oriented pass (not yet composed into [`preprocess_urs`]); kept for tooling / future merge.
#[allow(dead_code)]
fn rewrite_sig_type_class_abstract_lines(input: &str) -> String {
    fn ident_head(rest: &str) -> Option<(String, &str)> {
        let mut it = rest.chars();
        let c0 = it.next()?;
        if !(c0.is_ascii_alphabetic() || c0 == '_') {
            return None;
        }
        let mut id = c0.to_string();
        for c in it.by_ref() {
            if c.is_ascii_alphanumeric() || c == '_' || c == '\'' {
                id.push(c);
            } else {
                break;
            }
        }
        let consumed = id.len();
        Some((id, &rest[consumed..]))
    }

    /// First single `=` in `s` that is not part of `==`, `=>`, `<=`, `>=`, `!=`, or `:=`.
    /// Replaced by `sgn_def_con` (see `rewrite_con_class_kind_def_eq`).
    fn find_defining_single_eq(s: &str) -> Option<usize> {
        let b = s.as_bytes();
        let mut i = 0usize;
        while i < b.len() {
            if b[i] != b'=' {
                i += 1;
                continue;
            }
            if i + 1 < b.len() && b[i + 1] == b'=' {
                i += 2;
                continue;
            }
            if i + 1 < b.len() && b[i + 1] == b'>' {
                i += 2;
                continue;
            }
            if i > 0 && b[i - 1] == b'<' {
                i += 1;
                continue;
            }
            if i > 0 && b[i - 1] == b'>' {
                i += 1;
                continue;
            }
            if i > 0 && b[i - 1] == b'!' {
                i += 1;
                continue;
            }
            if i > 0 && b[i - 1] == b':' {
                i += 1;
                continue;
            }
            return Some(i);
        }
        None
    }

    /// `con nm :: K` / `class nm :: K` without a defining RHS: insert `sgn_abs` before `::`
    /// so abstract and `sgn_def_con` definitions use disjoint grammar prefixes.
    /// Also handles lines prefixed by `dt_done ` from `rewrite_datatype_constructors`.
    fn rewrite_con_class_sgn_abs(trimmed: &str) -> Option<String> {
        if trimmed.contains("sgn_def_con") || trimmed.contains("sgn_abs") {
            return None;
        }
        // Strip dt_done prefix that rewrite_datatype_constructors may have prepended
        let (keep_prefix, s) = if let Some(r) = trimmed.strip_prefix("dt_done") {
            let r = r.trim_start();
            (&trimmed[..trimmed.len() - r.len()], r)
        } else {
            ("", trimmed)
        };
        if !(s.starts_with("con ") || s.starts_with("class ")) {
            return None;
        }
        if !s.contains("::") {
            return None;
        }
        let (kw, rest) = if let Some(r) = s.strip_prefix("con ") {
            ("con ", r)
        } else if let Some(r) = s.strip_prefix("class ") {
            ("class ", r)
        } else {
            return None;
        };
        let (id, after_id) = ident_head(rest)?;
        let after_ws = after_id.trim_start();
        if !after_ws.starts_with("::") {
            return None;
        }
        Some(format!("{keep_prefix}{kw}{id} sgn_abs {after_ws}"))
    }

    fn rewrite_con_class_kind_def_eq(trimmed: &str) -> Option<String> {
        if trimmed.contains("sgn_def_con") {
            return None;
        }
        if !(trimmed.starts_with("con ") || trimmed.starts_with("class ")) {
            return None;
        }
        let dc = trimmed.find("::")?;
        let after_colons = trimmed.get(dc + 2..)?;
        let eq_rel = find_defining_single_eq(after_colons)?;
        let abs = dc + 2 + eq_rel;
        let mut s = String::with_capacity(trimmed.len() + 1);
        s.push_str(&trimmed[..abs]);
        s.push_str(" sgn_def_con ");
        s.push_str(trimmed.get(abs + 1..).unwrap_or(""));
        Some(s)
    }

    let mut out = String::with_capacity(input.len().saturating_add(256));
    let lines: Vec<&str> = input.lines().collect();
    for (i, line) in lines.iter().enumerate() {
        if i > 0 {
            out.push('\n');
        }
        let trimmed = line.trim_start();
        let indent_len = line.len().saturating_sub(trimmed.len());
        let indent = &line[..indent_len];

        let mut new_trimmed = trimmed.to_string();
        if !new_trimmed.contains('=') && !new_trimmed.contains("::") {
            if let Some(rest) = new_trimmed.strip_prefix("type ") {
                if let Some((id, after)) = ident_head(rest) {
                    let after_trim = after.trim_start();
                    if after_trim.is_empty() || after_trim.starts_with("(*") {
                        new_trimmed = format!("con {id} :: Type{after}");
                    }
                }
            } else if let Some(rest) = new_trimmed.strip_prefix("class ") {
                if let Some((id, after)) = ident_head(rest) {
                    let after_trim = after.trim_start();
                    if after_trim.is_empty() || after_trim.starts_with("(*") {
                        new_trimmed = format!("class {id} :: Type -> Type{after}");
                    }
                }
            }
        }
        if let Some(nt) = rewrite_con_class_kind_def_eq(&new_trimmed) {
            new_trimmed = nt;
        }
        if let Some(nt) = rewrite_con_class_sgn_abs(&new_trimmed) {
            new_trimmed = nt;
        }
        out.push_str(indent);
        out.push_str(&new_trimmed);
    }
    if input.ends_with('\n') && !lines.is_empty() {
        out.push('\n');
    }
    out
}

pub fn preprocess_urs(src: &str) -> String {
    let src = rewrite_case_expressions(&rewrite_sgn_where(&rewrite_datatype_constructors(src)));
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
    #[cfg(test)]
    {
        if let Ok(guard) = PREPROCESS_URS_FUEL_TEST_OVERRIDE.lock() {
            if let Some(f) = *guard {
                fuel = f;
            }
        }
    }
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
            if matches!(b.get(i).copied(), Some(b'('))
                && matches!(i.checked_add(1).and_then(|j| b.get(j)).copied(), Some(b'*'))
            {
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

                // Preprocessor pseudo-tokens must never be wrapped in [...].
                let is_pseudo_token = matches!(
                    ident,
                    "sgn_where"
                        | "sgn_subwhere"
                        | "arm_sep"
                        | "case_bar"
                        | "case_end"
                        | "dt_con0"
                        | "dt_bar"
                        | "dt_done"
                        | "dtype_of"
                );
                if is_decl_name || is_pseudo_token {
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

/// Replace `( * )` (SQL aggregate wildcard) with `( sql_star )` so the grammar doesn't need
/// `"*"` as an expression token (which conflicts with multiplication).
/// Only replaces `*` when it is the sole non-whitespace content between a matching `(…)` pair
/// (and the `(` is NOT the start of a comment `(*`).
pub fn rewrite_sql_star(input: &str) -> String {
    let b = input.as_bytes();
    let n = b.len();
    let mut out = String::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        // Skip ML comments `(* ... *)`
        if i + 1 < n && b[i] == b'(' && b[i + 1] == b'*' {
            let start = i;
            i = skip_ml_comment_bytes(b, i + 2, n);
            out.push_str(&input[start..i]);
            continue;
        }
        // Skip strings
        if b[i] == b'"' {
            let start = i;
            i = skip_string_bytes(b, i + 1, n);
            out.push_str(&input[start..i]);
            continue;
        }
        // Look for `(` followed by optional whitespace + `*` + optional whitespace + `)`
        if b[i] == b'(' {
            let mut j = i + 1;
            while j < n && (b[j] == b' ' || b[j] == b'\t' || b[j] == b'\n' || b[j] == b'\r') {
                j += 1;
            }
            if j < n && b[j] == b'*' {
                let mut k = j + 1;
                while k < n && (b[k] == b' ' || b[k] == b'\t' || b[k] == b'\n' || b[k] == b'\r') {
                    k += 1;
                }
                if k < n && b[k] == b')' {
                    // `( ws* * ws* )` — replace with `( sql_star )`
                    out.push_str("( sql_star )");
                    i = k + 1;
                    continue;
                }
            }
        }
        let ch = input[i..].chars().next().unwrap_or('\0');
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

/// Convert `{expr}` → `(expr)` when the `{` immediately follows a SQL keyword that introduces
/// a boolean or expression context: `WHERE`, `HAVING`, `ON` (case-sensitive, as Ur/Web SQL uses
/// uppercase).  Only the outermost braces are rewritten; inner `{...}` remains untouched.
/// Record literals (`{field = ...}`) and text-splices (`{[...]}`) are never touched.
pub fn rewrite_sql_keyword_brace_splices(input: &str) -> String {
    let b = input.as_bytes();
    let n = b.len();
    let mut out = String::with_capacity(n);
    let mut i = 0usize;

    // SQL keywords after which `{expr}` is a splice, not a record
    const SQL_KEYWORDS: &[&[u8]] = &[b"WHERE", b"HAVING", b"ON"];

    while i < n {
        // Skip ML comments
        if i + 1 < n && b[i] == b'(' && b[i + 1] == b'*' {
            let start = i;
            i = skip_ml_comment_bytes(b, i + 2, n);
            out.push_str(&input[start..i]);
            continue;
        }
        // Skip strings
        if b[i] == b'"' {
            let start = i;
            i = skip_string_bytes(b, i + 1, n);
            out.push_str(&input[start..i]);
            continue;
        }
        // Check for SQL keywords at word boundary
        let mut found_keyword = false;
        for kw in SQL_KEYWORDS {
            let klen = kw.len();
            if i + klen <= n && b[i..i + klen].eq_ignore_ascii_case(kw) {
                // Must be at a word boundary (not preceded by alnum/_)
                let at_word_start = i == 0 || {
                    let pb = b[i - 1];
                    !pb.is_ascii_alphanumeric() && pb != b'_'
                };
                // And followed by non-alnum (word boundary)
                let at_word_end = i + klen >= n || {
                    let nb = b[i + klen];
                    !nb.is_ascii_alphanumeric() && nb != b'_'
                };
                if at_word_start && at_word_end {
                    // Emit the keyword
                    out.push_str(&input[i..i + klen]);
                    i += klen;
                    // Skip whitespace after keyword
                    let ws_start = i;
                    while i < n && (b[i] == b' ' || b[i] == b'\t' || b[i] == b'\n' || b[i] == b'\r')
                    {
                        i += 1;
                    }
                    out.push_str(&input[ws_start..i]);
                    // If next non-whitespace is `{`, check if it's a splice or record
                    if i < n && b[i] == b'{' {
                        // Skip `(*...)` comments before peeking inside
                        let mut j = i + 1;
                        while j + 1 < n && b[j] == b'(' && b[j + 1] == b'*' {
                            j = skip_ml_comment_bytes(b, j + 2, n);
                            while j < n
                                && (b[j] == b' ' || b[j] == b'\t' || b[j] == b'\n' || b[j] == b'\r')
                            {
                                j += 1;
                            }
                        }
                        // Advance past whitespace inside `{`
                        while j < n
                            && (b[j] == b' ' || b[j] == b'\t' || b[j] == b'\n' || b[j] == b'\r')
                        {
                            j += 1;
                        }
                        // `{[...]}` — text splice: leave alone
                        // `{}` — empty record: leave alone
                        // `{...}` — spread: leave alone
                        // `{ident =` — record field: leave alone
                        // `{ident non-eq}` — SQL splice: convert to `(...)`
                        let is_sql_splice = if j >= n || b[j] == b'}' || b[j] == b'[' {
                            false
                        } else if j + 2 < n && &b[j..j + 3] == b"..." {
                            false
                        } else if b[j].is_ascii_alphabetic() || b[j] == b'_' {
                            let mut k = j + 1;
                            while k < n
                                && (b[k].is_ascii_alphanumeric() || b[k] == b'_' || b[k] == b'\'')
                            {
                                k += 1;
                            }
                            // Skip whitespace
                            while k < n && (b[k] == b' ' || b[k] == b'\t') {
                                k += 1;
                            }
                            // If followed by `=` (but not `=>` or `==`) → record field
                            !(k < n
                                && b[k] == b'='
                                && (k + 1 >= n || (b[k + 1] != b'>' && b[k + 1] != b'=')))
                        } else {
                            true
                        };
                        if is_sql_splice {
                            // Convert only the outermost { → ( and matching } → )
                            // Inner braces are emitted verbatim so grammar rules handle them.
                            out.push('(');
                            i += 1; // skip `{`
                            let mut depth = 1i32;
                            while i < n && depth > 0 {
                                if i + 1 < n && b[i] == b'(' && b[i + 1] == b'*' {
                                    let start = i;
                                    i = skip_ml_comment_bytes(b, i + 2, n);
                                    out.push_str(&input[start..i]);
                                } else if b[i] == b'"' {
                                    let start = i;
                                    i = skip_string_bytes(b, i + 1, n);
                                    out.push_str(&input[start..i]);
                                } else if b[i] == b'{' {
                                    out.push('{');
                                    depth += 1;
                                    i += 1;
                                } else if b[i] == b'}' {
                                    depth -= 1;
                                    if depth > 0 {
                                        out.push('}');
                                    } else {
                                        out.push(')'); // closing outer splice
                                    }
                                    i += 1;
                                } else {
                                    let ch = input[i..].chars().next().unwrap_or('\0');
                                    out.push(ch);
                                    i += ch.len_utf8();
                                }
                            }
                        }
                        // else: leave as-is (will be handled normally below)
                    }
                    found_keyword = true;
                    break;
                }
            }
        }
        if found_keyword {
            continue;
        }
        let ch = input[i..].chars().next().unwrap_or('\0');
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

/// Preprocess `.ur` source exactly like [`parse_ur`] before the lexer runs (rewrites only).
/// Used by LSP semantic highlighting and other tools that need the same surface as the parser.
pub fn preprocess_ur_for_parse(src: &str) -> String {
    rewrite_case_expressions(&rewrite_sgn_where(&rewrite_datatype_constructors(
        &rewrite_bare_kind_binders(&rewrite_sql_star(&rewrite_sql_keyword_brace_splices(
            &strip_table_constraints(src),
        ))),
    )))
}

/// Parse a single `.ur` source file.
///
/// `project_db` is the effective [`crate::db::ProjectDb`] for this compile (from `ur.toml` /
/// `.urp` / CLI). It selects LangSec / future backend-specific surface rules; the LALRPOP parser
/// is shared, but preprocess and recognizers can branch on it.
///
/// Returns `None` and records an error in `errors` on parse failure.
pub fn parse_ur(
    _filename: &str,
    source: &str,
    errors: &mut ErrorReporter,
    project_db: crate::db::ProjectDb,
) -> Option<File> {
    #[cfg(generated_parser)]
    {
        let _parse_profile = project_db.langsec_parse_profile();
        let _ = (_parse_profile, project_db); // LangSec tiers branch on profile + db
        let pre = preprocess_ur_for_parse(source);
        let lexer = lexical_analyzer::XmlAwareLexer::new(&pre);
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
        let _ = (_filename, source, project_db);
        errors.report(CompileError::Plain(
            "parse_ur: parser not available — rebuild with URWEB_GEN_PARSER=1".into(),
        ));
        None
    }
}

/// Count top-level declarations after parsing `source` as a `.ur` file.
///
/// Used by the `test_parse` binary and tests (avoids a trivial `-> Some(1)` mutant surface).
pub fn parse_top_level_decl_count(
    virtual_path: &str,
    source: &str,
    errors: &mut ErrorReporter,
) -> Option<usize> {
    parse_ur(
        virtual_path,
        source,
        errors,
        crate::db::ProjectDb::default(),
    )
    .map(|f| f.len())
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
    fn preprocess_urs_low_fuel_appends_remainder_without_panic() {
        let src = "val f : nm :: Type -> int -> int\n";
        test_set_preprocess_urs_fuel_override(Some(8));
        let out = preprocess_urs(src);
        test_set_preprocess_urs_fuel_override(None);
        assert!(
            !out.is_empty(),
            "fuel exhaustion must return partial output + suffix, not panic"
        );
        assert!(
            out.contains("nm") || out.contains("val"),
            "output should retain source text: {out:?}"
        );
    }

    #[test]
    fn parse_ur_returns_none_without_generated_parser() {
        let mut errors = ErrorReporter::new();
        let result = parse_ur(
            "test.ur",
            "val x = 1",
            &mut errors,
            crate::db::ProjectDb::default(),
        );
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
    fn debug_cookie_bars() {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/demo/cookie.ur");
        let Ok(src) = std::fs::read_to_string(path) else {
            return;
        };
        let pp = preprocess_ur_for_parse(&src);
        for (i, c) in pp.char_indices() {
            if c == '|' {
                let s = i.saturating_sub(40);
                let e = (i + 40).min(pp.len());
                eprintln!("|@{}: {:?}", i, &pp[s..e]);
            }
        }
        eprintln!("total len={}", pp.len());
    }

    #[test]
    fn pp_basis_context() {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/lib/ur/basis.urs");
        let Ok(content) = std::fs::read_to_string(path) else {
            return;
        };
        let pp = preprocess_urs(&content);
        let pos: usize = 504;
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
    fn parse_top_level_decl_count_tracks_parser() {
        let mut errors = ErrorReporter::new();
        let n = parse_top_level_decl_count("test.ur", "val x = 1", &mut errors);
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
        let n = parse_ur(
            "t.ur",
            "val a = 1\nval b = 2",
            &mut errors,
            crate::db::ProjectDb::default(),
        )
        .map(|f| f.len());
        #[cfg(generated_parser)]
        {
            assert_eq!(
                n,
                Some(2),
                "catches parse_top_level_decl_count -> Some(1) style mutants"
            );
        }
        #[cfg(not(generated_parser))]
        {
            assert!(n.is_none());
        }
    }

    #[test]
    fn parse_top_level_decl_count_matches_parse_ur_len() {
        let mut e1 = ErrorReporter::new();
        let mut e2 = ErrorReporter::new();
        let src = "val p = 1\nval q = 2\nval r = 3";
        let a = parse_top_level_decl_count("m.ur", src, &mut e1);
        let b = parse_ur("m.ur", src, &mut e2, crate::db::ProjectDb::default()).map(|f| f.len());
        assert_eq!(a, b);
        #[cfg(generated_parser)]
        assert_eq!(a, Some(3));
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

    /// LALRPOP `ArithExp` vs [`expr_langsec::parse_cmp_app_spine`] on the same token stream
    /// (subset: atoms + paren / arithmetic / cons / strcat; no postfix `.` / `[Con]`).
    #[cfg(generated_parser)]
    mod langsec_spine_equiv {
        use super::*;
        use crate::error_types::{Located, Span};
        use crate::parse::expr_langsec::{parse_cmp_app_spine, ExprRecognizeError, TokenCursor};
        use crate::parse::lexical_analyzer::{tokenize_xml_aware, Token};
        use crate::primitives::Prim;
        use crate::source::{Decl, Exp, Inference};

        fn line_starts_for(src: &str) -> Vec<usize> {
            let mut v = vec![0usize];
            for (i, c) in src.char_indices() {
                if c == '\n' {
                    v.push(i + c.len_utf8());
                }
            }
            v
        }

        fn span_at(file: &str, line_starts: &[usize], lo: usize, hi: usize) -> Span {
            Span::from_offsets(file, lo, hi, line_starts)
        }

        fn spine_langsec_primary(
            cur: &mut TokenCursor<'_>,
        ) -> Result<Located<Exp>, ExprRecognizeError> {
            let Some((l, tok, r)) = cur.peek().cloned() else {
                return Err(ExprRecognizeError::UnexpectedEof);
            };
            match &tok {
                Token::UrwebPut => {
                    cur.bump();
                    Ok(Located::new(
                        Exp::Var(
                            vec!["UrwebNative".into()],
                            "urweb_put".into(),
                            Inference::DontInfer,
                        ),
                        span_at(cur.file, cur.line_starts, l, r),
                    ))
                }
                Token::UrwebGet => {
                    cur.bump();
                    Ok(Located::new(
                        Exp::Var(
                            vec!["UrwebNative".into()],
                            "urweb_get".into(),
                            Inference::DontInfer,
                        ),
                        span_at(cur.file, cur.line_starts, l, r),
                    ))
                }
                Token::UrwebTbTransfer => {
                    cur.bump();
                    Ok(Located::new(
                        Exp::Var(
                            vec!["UrwebNative".into()],
                            "urweb_tb_transfer".into(),
                            Inference::DontInfer,
                        ),
                        span_at(cur.file, cur.line_starts, l, r),
                    ))
                }
                Token::Ident(name) | Token::UpperIdent(name) => {
                    let name = name.clone();
                    cur.bump();
                    Ok(Located::new(
                        Exp::Var(vec![], name, Inference::DontInfer),
                        span_at(cur.file, cur.line_starts, l, r),
                    ))
                }
                Token::Int(n) => {
                    let n = *n;
                    cur.bump();
                    Ok(Located::new(
                        Exp::Prim(Prim::Int(n)),
                        span_at(cur.file, cur.line_starts, l, r),
                    ))
                }
                Token::Float(f) => {
                    let f = *f;
                    cur.bump();
                    Ok(Located::new(
                        Exp::Prim(Prim::Float(f)),
                        span_at(cur.file, cur.line_starts, l, r),
                    ))
                }
                Token::Unit => {
                    cur.bump();
                    Ok(Located::dummy(Exp::Record(vec![], false)))
                }
                Token::Lparen => {
                    cur.bump();
                    let inner = parse_cmp_app_spine(cur, spine_langsec_primary)?;
                    match cur.bump() {
                        Some((_, Token::Rparen, r2)) => Ok(Located::new(
                            inner.node,
                            span_at(cur.file, cur.line_starts, l, r2),
                        )),
                        _ => Err(ExprRecognizeError::UnbalancedParen { at_byte: l }),
                    }
                }
                _ => Err(ExprRecognizeError::ExpectedPrimary { at_byte: l }),
            }
        }

        fn exp_structure_eq(a: &Located<Exp>, b: &Located<Exp>) -> bool {
            exp_node_eq(&a.node, &b.node)
        }

        fn exp_node_eq(a: &Exp, b: &Exp) -> bool {
            match (a, b) {
                (Exp::Var(qa, na, ia), Exp::Var(qb, nb, ib)) => qa == qb && na == nb && ia == ib,
                (Exp::Prim(pa), Exp::Prim(pb)) => pa == pb,
                (Exp::Record(fa, sa), Exp::Record(fb, sb)) => {
                    fa.is_empty() && fb.is_empty() && sa == sb
                }
                (Exp::App(fa, xa), Exp::App(fb, xb)) => {
                    exp_structure_eq(fa, fb) && exp_structure_eq(xa, xb)
                }
                (Exp::Infix(oa, la, ra), Exp::Infix(ob, lb, rb)) => {
                    oa == ob && exp_structure_eq(la, lb) && exp_structure_eq(ra, rb)
                }
                _ => false,
            }
        }

        #[test]
        fn lalrpop_arith_exp_matches_expr_langsec() {
            let cases = [
                "a + b * c",
                "f g h",
                "f x * y",
                "(a + b) * c",
                "a :: b :: c",
                "a + b :: c",
                "a :: b + c",
                "a + b = c",
                "a ^ b",
                "()",
                "1",
                "(1 + 2) * 3",
            ];
            for expr in cases {
                let file_src = format!("val _ = {}\n", expr);
                let mut errs = ErrorReporter::new();
                let Some(file) = parse_ur(
                    "equiv.ur",
                    &file_src,
                    &mut errs,
                    crate::db::ProjectDb::default(),
                ) else {
                    panic!("parse_ur failed for {:?}: {:?}", expr, errs.errors);
                };
                let Some(got) = file.iter().find_map(|d| {
                    if let Decl::Val(_, e) = &d.node {
                        Some(e.clone())
                    } else {
                        None
                    }
                }) else {
                    panic!("no val decl for {:?}", expr);
                };

                let toks = tokenize_xml_aware(expr)
                    .unwrap_or_else(|e| panic!("lex {:?}: {}", expr, e.message));
                let line_starts = line_starts_for(expr);
                let mut cur = TokenCursor::new(&toks, &line_starts, "");
                let spine = parse_cmp_app_spine(&mut cur, spine_langsec_primary)
                    .unwrap_or_else(|e| panic!("langsec {:?}: {:?}", expr, e));
                assert!(
                    cur.at_end(),
                    "leftover tokens for {:?} at {}",
                    expr,
                    cur.pos
                );
                assert!(
                    exp_structure_eq(&got, &spine),
                    "spine mismatch {:?}\n LALR {:?}\n LS {:?}",
                    expr,
                    got.node,
                    spine.node
                );
            }
        }
    }
}
