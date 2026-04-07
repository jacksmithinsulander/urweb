//! Macros shared by [`super::preprocess_urs`] and other `.urs`-style byte scanners in `parse`.
//!
//! Macros (not `fn`): cargo-mutants cannot replace the whole helper with `true`/`false` and hang.
//! `matches!` avoids a single `==` that `!=` mutants can flip wholesale.

/// True if `c` is ASCII whitespace we treat as skippable in `.urs` preprocessing.
macro_rules! pp_urs_is_ws {
    ($c:expr) => {{
        let __c = $c;
        matches!(__c, b' ' | b'\t' | b'\n' | b'\r')
    }};
}

/// True if `c` can continue an identifier (after the first byte) in `.urs` preprocessing.
macro_rules! pp_urs_id_cont {
    ($c:expr) => {{
        let __c = $c;
        matches!(
            __c,
            b'_' | b'\'' | b'0'..=b'9' | b'a'..=b'z' | b'A'..=b'Z'
        )
    }};
}

/// True if delimiter/nesting depth is still positive (unterminated scan).
macro_rules! pp_urs_depth_nonzero {
    ($d:expr) => {{
        let __d = $d;
        matches!(__d, 1..)
    }};
}
