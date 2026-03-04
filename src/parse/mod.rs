//! Parser for Ur/Web source files.
//!
//! - **parse_ur**: parse `.ur` files into `source::File`
//! - **parse_urs**: parse `.urs` signature files
//! - **lexer**: tokenization (Logos)

pub mod lexical_analyzer;

use crate::error_types::ErrorReporter;
use crate::source::File;

/// Parse a single `.ur` source file.
///
/// The grammar is in `grammar.lalrpop`; this is the entry point called by
/// `compiler.rs`.
pub fn parse_ur(_filename: &str, _source: &str, _errors: &mut ErrorReporter) -> Option<File> {
    todo!("parse_ur: LALRPOP grammar not yet generated")
}

/// Parse a `.urs` signature file (prepends `sig\n` before parsing).
pub fn parse_urs(
    _filename: &str,
    _source: &str,
    _errors: &mut ErrorReporter,
) -> Option<Vec<crate::source::LocSgnItem>> {
    todo!("parse_urs: LALRPOP grammar not yet generated")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic(expected = "parse_ur")]
    fn parse_ur_panics_until_implemented() {
        let mut errors = ErrorReporter::new();
        let _ = parse_ur("test.ur", "val x = 1", &mut errors);
    }

    #[test]
    #[should_panic(expected = "parse_urs")]
    fn parse_urs_panics_until_implemented() {
        let mut errors = ErrorReporter::new();
        let _ = parse_urs("test.urs", "val x : int", &mut errors);
    }
}
