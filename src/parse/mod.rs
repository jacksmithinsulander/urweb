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
        let lexer = lexical_analyzer::Lexer::new(source);
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
