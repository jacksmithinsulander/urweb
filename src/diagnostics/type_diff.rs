//! Word-level diff highlighting for type unification error messages.
//!
//! Compares two formatted type strings token-by-token and produces ANSI-colored
//! versions where differing tokens are highlighted: red background on the
//! inferred (wrong) type, green background on the expected (needed) type.
//! Matching tokens are rendered plain. The result looks similar to a GitHub
//! inline diff, making the point of divergence easy to spot.

/// Red background SGR sequence — applied to inferred tokens that are not in the LCS.
const ANSI_RED_BG: &str = "\x1b[41m";
/// Green background SGR sequence — applied to expected tokens that are not in the LCS.
const ANSI_GREEN_BG: &str = "\x1b[42m";
/// SGR reset — must follow every highlighted token to avoid bleeding into surrounding text.
const ANSI_RESET: &str = "\x1b[0m";

/// Build the O(nm) LCS dynamic-programming table for two token slices.
///
/// # Arguments
///
/// * `a` — First token sequence.
/// * `b` — Second token sequence.
///
/// # Returns
///
/// A `(m+1) × (n+1)` table where `dp[i][j]` is the LCS length of `a[..i]` and `b[..j]`.
fn compute_lcs_table(a: &[&str], b: &[&str]) -> Vec<Vec<usize>> {
    let a_len = a.len(); // number of tokens in the inferred type
    let b_len = b.len(); // number of tokens in the expected type
    let mut dp = vec![vec![0usize; b_len + 1]; a_len + 1]; // zero-initialized DP table
    for row in 1..=a_len {
        for col in 1..=b_len {
            if a[row - 1] == b[col - 1] {
                // Tokens match: extend the diagonal LCS count.
                dp[row][col] = dp[row - 1][col - 1] + 1;
            } else {
                // No match: take the better of the two previous cells.
                dp[row][col] = dp[row - 1][col].max(dp[row][col - 1]);
            }
        }
    }
    dp
}

/// Backtrack through the LCS table to recover which token indices were matched.
///
/// # Arguments
///
/// * `dp` — Table produced by [`compute_lcs_table`].
/// * `a` — First token sequence (same order used to build `dp`).
/// * `b` — Second token sequence.
///
/// # Returns
///
/// A vector of `(a_index, b_index)` pairs in ascending order, one per matched token.
fn backtrack_lcs(dp: &[Vec<usize>], a: &[&str], b: &[&str]) -> Vec<(usize, usize)> {
    let mut matches: Vec<(usize, usize)> = Vec::new(); // collected match pairs, filled in reverse
    let mut row = a.len(); // current position in a, walking backwards
    let mut col = b.len(); // current position in b, walking backwards
    while row > 0 && col > 0 {
        if a[row - 1] == b[col - 1] {
            // Diagonal: this pair of tokens is part of the LCS.
            matches.push((row - 1, col - 1));
            row -= 1;
            col -= 1;
        } else if dp[row - 1][col] >= dp[row][col - 1] {
            // Moving up is at least as good as moving left: skip a token.
            row -= 1;
        } else {
            // Moving left is strictly better: skip b token.
            col -= 1;
        }
    }
    matches.reverse(); // backtracking collected pairs in reverse; put them in forward order
    matches
}

/// Produce ANSI-highlighted versions of two formatted type strings by comparing them token-by-token.
///
/// Tokens are split on ASCII whitespace. Tokens that appear in the longest-common-subsequence of
/// both strings are rendered without color. Tokens in `inferred` that are *not* in the LCS get a
/// red background (`\x1b[41m`); tokens in `expected` that are *not* in the LCS get a green
/// background (`\x1b[42m`). This mirrors the convention of GitHub / unified-diff output where
/// the "removed" side is red and the "wanted" side is green.
///
/// If either input is empty after tokenizing, the function returns the originals unchanged to
/// avoid a noisy all-highlighted display when one side is missing entirely.
///
/// # Arguments
///
/// * `inferred` — The type the compiler inferred (what was found).
/// * `expected` — The type the context requires (what is needed).
///
/// # Returns
///
/// `(colored_inferred, colored_expected)` — two strings with embedded ANSI escape sequences.
pub fn diff_type_strings(inferred: &str, expected: &str) -> (String, String) {
    let inferred_tokens: Vec<&str> = inferred.split_whitespace().collect(); // whitespace-tokenize inferred
    let expected_tokens: Vec<&str> = expected.split_whitespace().collect(); // whitespace-tokenize expected

    // If either side has no tokens (e.g., the empty type or a display error), return originals
    // unchanged rather than producing a misleadingly fully-highlighted output.
    if inferred_tokens.is_empty() || expected_tokens.is_empty() {
        return (inferred.to_string(), expected.to_string());
    }

    // Skip diff computation when the strings are identical; every token would match anyway.
    if inferred == expected {
        return (inferred.to_string(), expected.to_string());
    }

    let dp = compute_lcs_table(&inferred_tokens, &expected_tokens); // build LCS DP table
    let matches = backtrack_lcs(&dp, &inferred_tokens, &expected_tokens); // recover matched pairs

    // Build a boolean mask: true means this token index participates in the LCS.
    let mut inferred_matched = vec![false; inferred_tokens.len()]; // mask for inferred tokens
    let mut expected_matched = vec![false; expected_tokens.len()]; // mask for expected tokens
    for (inferred_idx, expected_idx) in matches {
        inferred_matched[inferred_idx] = true; // mark inferred token as matching
        expected_matched[expected_idx] = true; // mark expected token as matching
    }

    // Assemble the colored inferred string: highlight unmatched tokens with red background.
    let mut colored_inferred = String::new();
    for (token_index, token) in inferred_tokens.iter().enumerate() {
        if token_index > 0 {
            colored_inferred.push(' '); // restore whitespace between tokens
        }
        if inferred_matched[token_index] {
            colored_inferred.push_str(token); // matched: plain text
        } else {
            colored_inferred.push_str(ANSI_RED_BG); // unmatched inferred token: red background
            colored_inferred.push_str(token);
            colored_inferred.push_str(ANSI_RESET); // reset after each highlighted token
        }
    }

    // Assemble the colored expected string: highlight unmatched tokens with green background.
    let mut colored_expected = String::new();
    for (token_index, token) in expected_tokens.iter().enumerate() {
        if token_index > 0 {
            colored_expected.push(' '); // restore whitespace between tokens
        }
        if expected_matched[token_index] {
            colored_expected.push_str(token); // matched: plain text
        } else {
            colored_expected.push_str(ANSI_GREEN_BG); // unmatched expected token: green background
            colored_expected.push_str(token);
            colored_expected.push_str(ANSI_RESET); // reset after each highlighted token
        }
    }

    (colored_inferred, colored_expected)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identical_strings_return_unchanged() {
        let (a, b) = diff_type_strings("int -> string", "int -> string");
        assert_eq!(a, "int -> string");
        assert_eq!(b, "int -> string");
    }

    #[test]
    fn completely_different_strings_highlight_all_tokens() {
        let (inferred, expected) = diff_type_strings("int", "string");
        // All tokens differ so both should be fully highlighted
        assert!(inferred.contains(ANSI_RED_BG));
        assert!(expected.contains(ANSI_GREEN_BG));
        assert!(!inferred.contains(ANSI_GREEN_BG));
        assert!(!expected.contains(ANSI_RED_BG));
    }

    #[test]
    fn partial_match_highlights_only_diverging_tokens() {
        // "int -> string -> bool" vs "int -> int -> bool"
        // "int", "->", "->", "bool" match; "string" vs "int" diverges
        let (inferred, expected) = diff_type_strings("int -> string -> bool", "int -> int -> bool");
        // Matching tokens should be plain (no ANSI around them)
        assert!(!inferred.starts_with(ANSI_RED_BG)); // first token "int" matches, so no red at start
                                                     // The diverging tokens must be highlighted
        assert!(inferred.contains(ANSI_RED_BG));
        assert!(expected.contains(ANSI_GREEN_BG));
    }

    #[test]
    fn empty_inferred_returns_originals_unchanged() {
        let (inferred, expected) = diff_type_strings("", "int");
        assert_eq!(inferred, "");
        assert_eq!(expected, "int");
    }

    #[test]
    fn empty_expected_returns_originals_unchanged() {
        let (inferred, expected) = diff_type_strings("int", "");
        assert_eq!(inferred, "int");
        assert_eq!(expected, "");
    }
}
