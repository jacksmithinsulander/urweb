//! Error handling and source locations.
//!
//! - **Pos**: (line, column) in a source file
//! - **Span**: file + start/end positions
//! - **Located<T>**: pairs any value with a Span for error reporting
//! - **CompileError**: parse/type/I/O errors
//! - **ErrorReporter**: accumulates errors during compilation

use thiserror::Error;

/// A (line, column) position in a source file.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Pos {
    pub line: u32,
    pub col: u32,
}

impl Pos {
    pub const DUMMY: Pos = Pos { line: 0, col: 0 };
}

impl std::fmt::Display for Pos {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

/// A source span: file + start + end position.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Span {
    pub file: String,
    pub first: Pos,
    pub last: Pos,
}

impl Default for Span {
    fn default() -> Self {
        Span::dummy()
    }
}

impl Span {
    pub fn dummy() -> Self {
        Span {
            file: String::new(),
            first: Pos::DUMMY,
            last: Pos::DUMMY,
        }
    }

    /// Build a Span from byte offsets, given a sorted list of newline positions.
    pub fn from_offsets(file: &str, start: usize, end: usize, line_starts: &[usize]) -> Self {
        let pos_of = |offset: usize| {
            // line_starts[i] = byte offset of start of line i+1 (0-indexed)
            match line_starts.binary_search(&offset) {
                Ok(i) => Pos {
                    line: (i + 1) as u32,
                    col: 0,
                },
                Err(i) => {
                    let line_start = if i == 0 { 0 } else { line_starts[i - 1] + 1 };
                    Pos {
                        line: (i + 1) as u32,
                        col: (offset - line_start) as u32,
                    }
                }
            }
        };
        Span {
            file: file.to_string(),
            first: pos_of(start),
            last: pos_of(end),
        }
    }
}

impl std::fmt::Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}-{}", self.file, self.first, self.last)
    }
}

/// Wrapper that pairs any value with a source span (mirrors SML's `'a located`).
#[derive(Debug, Clone)]
pub struct Located<T> {
    pub node: T,
    pub span: Span,
}

impl<T> Located<T> {
    pub fn new(node: T, span: Span) -> Self {
        Located { node, span }
    }

    pub fn dummy(node: T) -> Self {
        Located {
            node,
            span: Span::dummy(),
        }
    }

    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Located<U> {
        Located {
            node: f(self.node),
            span: self.span,
        }
    }
}

impl<T: Default> Default for Located<T> {
    fn default() -> Self {
        Located::dummy(T::default())
    }
}

/// Compile-time error with optional span information.
#[derive(Debug, Error)]
pub enum CompileError {
    #[error("{0}")]
    Plain(String),

    #[error("{span}: {message}")]
    AtSpan { span: Span, message: String },

    #[error("Parse error at {span}: {message}")]
    ParseError { span: Span, message: String },

    #[error("Type error at {span}: {message}")]
    TypeError { span: Span, message: String },

    #[error(transparent)]
    Io(#[from] std::io::Error),
}

impl Default for CompileError {
    fn default() -> Self {
        CompileError::Plain(String::new())
    }
}

impl CompileError {
    pub fn at(span: Span, message: impl Into<String>) -> Self {
        CompileError::AtSpan {
            span,
            message: message.into(),
        }
    }

    pub fn span(&self) -> Option<&Span> {
        match self {
            CompileError::AtSpan { span, .. }
            | CompileError::ParseError { span, .. }
            | CompileError::TypeError { span, .. } => Some(span),
            _ => None,
        }
    }
}

/// Accumulates compile errors (mirrors SML's global error ref + errorLog).
#[derive(Debug, Default)]
pub struct ErrorReporter {
    pub errors: Vec<CompileError>,
}

impl ErrorReporter {
    pub fn new() -> Self {
        ErrorReporter::default()
    }

    pub fn report(&mut self, error: CompileError) {
        eprintln!("{error}");
        self.errors.push(error);
    }

    pub fn report_at(&mut self, span: Span, message: impl Into<String>) {
        self.report(CompileError::at(span, message));
    }

    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    pub fn reset(&mut self) {
        self.errors.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pos_display() {
        let p = Pos { line: 1, col: 5 };
        assert_eq!(p.to_string(), "1:5");
    }

    #[test]
    fn dummy_span_display() {
        let s = Span::dummy();
        assert!(s.to_string().contains(':'));
    }

    #[test]
    fn span_from_offsets_binary_search_ok() {
        // offset 11 falls between line_starts, Err branch.
        let line_starts = vec![10, 20];
        let s = Span::from_offsets("f", 11, 15, &line_starts);
        assert_eq!(s.first.line, 2);
    }

    #[test]
    fn span_from_offsets_ok_branch_uses_plus_for_line() {
        // offset 10 equals line_starts[0] → Ok(0) → line = (i+1) = 1. Catches + vs - or *.
        let line_starts = vec![10, 20];
        let s = Span::from_offsets("f", 10, 11, &line_starts);
        assert_eq!(s.first.line, 1, "line must be i+1 not i-1 or i*1");
    }

    #[test]
    fn span_from_offsets_arithmetic() {
        let line_starts: Vec<usize> = vec![];
        let s = Span::from_offsets("f", 3, 7, &line_starts);
        assert_eq!(s.first.col, 3);
        assert_eq!(s.last.col, 7);
    }

    #[test]
    fn error_reporter_report_at() {
        let mut r = ErrorReporter::new();
        let span = Span::dummy();
        r.report_at(span, "err");
        assert!(r.has_errors());
    }

    #[test]
    fn span_from_offsets_single_line() {
        let line_starts: Vec<usize> = vec![]; // no newlines
        let s = Span::from_offsets("foo.ur", 3, 7, &line_starts);
        assert_eq!(s.first.line, 1);
        assert_eq!(s.first.col, 3);
        assert_eq!(s.last.col, 7);
    }

    #[test]
    fn span_from_offsets_multi_line() {
        // "hello\nworld\n"
        //  01234 5 67890 11
        let line_starts = vec![5usize, 11]; // newline positions
        let s = Span::from_offsets("f.ur", 6, 10, &line_starts);
        assert_eq!(s.first.line, 2);
        assert_eq!(s.first.col, 0);
    }

    #[test]
    fn span_from_offsets_line_start_arithmetic() {
        // line_starts[i] = offset of newline at end of line i
        // Line 1 ends at 5, line 2 starts at 6. So line_start for line 2 = line_starts[0] + 1
        let line_starts = vec![5usize];
        let s = Span::from_offsets("f", 6, 7, &line_starts);
        assert_eq!(
            s.first.col, 0,
            "col must use line_start = line_starts[i-1]+1, not - or *"
        );
    }

    #[test]
    fn span_from_offsets_err_branch_uses_plus_not_minus_or_star() {
        // offset 12 is on line 2; line_starts[0]=10 means line 1 ends at 10, line 2 starts at 11.
        // Correct: line_start = 10+1 = 11, col = 12-11 = 1.
        // Mutant -: line_start = 10-1 = 9, col = 3.
        // Mutant *: line_start = 10*1 = 10, col = 2.
        let line_starts = vec![10usize];
        let s = Span::from_offsets("f", 12, 13, &line_starts);
        assert_eq!(s.first.col, 1);
        assert_eq!(s.first.line, 2);
    }

    #[test]
    fn located_map() {
        let l: Located<i32> = Located::dummy(42);
        let l2 = l.map(|n| n + 1);
        assert_eq!(l2.node, 43);
    }

    #[test]
    fn error_reporter_accumulates() {
        let mut r = ErrorReporter::new();
        r.report(CompileError::Plain("oops".into()));
        assert!(r.has_errors());
        r.reset();
        assert!(!r.has_errors());
    }

    #[test]
    fn compile_error_at_span() {
        let span = Span {
            file: "test.ur".to_string(),
            first: Pos { line: 1, col: 0 },
            last: Pos { line: 1, col: 5 },
        };
        let e = CompileError::at(span.clone(), "bad type");
        assert!(e.to_string().contains("bad type"));
        assert_eq!(e.span(), Some(&span));
    }
}
