//! Diagnostics: positions, spans, and error accumulation for the batch compiler and the language server.
//!
//! [`Pos`] is a line and column in a source file (one-based line numbers in human output).
//! [`Span`] names the file plus start and end [`Pos`] values.
//! [`Located`] pairs any node with a [`Span`] (like Standard ML’s located type).
//! [`CompileError`] covers parse and type messages, warnings, and input/output failures.
//! [`ErrorReporter`] collects diagnostics; silent reporters feed the Language Server Protocol without printing.

use thiserror::Error;

/// A (line, column) position in a source file.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Pos {
    pub line: u32,
    pub col: u32,
}

impl Pos {
    /// Sentinel position used before real source locations are known.
    pub const DUMMY: Pos = Pos { line: 0, col: 0 };
}

/// Prints `line:col` for diagnostics.
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

/// Default span is empty file and dummy positions.
impl Default for Span {
    fn default() -> Self {
        Span::dummy()
    }
}

impl Span {
    /// Empty path and [`Pos::DUMMY`] at both ends — used for non-source errors.
    ///
    /// # Returns
    ///
    /// A [`Span`] with empty `file` and dummy positions.
    pub fn dummy() -> Self {
        Span {
            file: String::new(),
            first: Pos::DUMMY,
            last: Pos::DUMMY,
        }
    }

    /// Build a span from Unicode UTF-8 byte offsets and a sorted list of newline byte offsets in the same buffer.
    ///
    /// # Arguments
    ///
    /// * `file` — Logical filename stored in the span (often a path or `file:` URL string).
    /// * `start` — Inclusive UTF-8 byte offset of the range start in the source buffer.
    /// * `end` — Inclusive UTF-8 byte offset of the range end in the source buffer.
    /// * `line_starts` — Sorted indices of newline bytes; defines line boundaries for `start` / `end`.
    ///
    /// # Returns
    ///
    /// A [`Span`] with one-based line numbers and UTF-8 byte columns within each line.
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

/// `file:first-last` for human-readable error banners.
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
    /// Attach an arbitrary AST node to a concrete source span.
    ///
    /// # Arguments
    ///
    /// * `node` — Parsed syntax or other value to carry.
    /// * `span` — Source extent for diagnostics.
    ///
    /// # Returns
    ///
    /// [`Located`] pairing `node` with `span`.
    pub fn new(node: T, span: Span) -> Self {
        Located { node, span }
    }

    /// Wrap `node` with [`Span::dummy`] for synthetic or recovered trees.
    ///
    /// # Arguments
    ///
    /// * `node` — Value without a real source location.
    ///
    /// # Returns
    ///
    /// [`Located`] with [`Span::dummy`].
    pub fn dummy(node: T) -> Self {
        Located {
            node,
            span: Span::dummy(),
        }
    }
}

/// Never call this in real code: it always panics.
///
/// It exists so `Located<T>` implements [`Default`] for **every** `T`, which keeps
/// `cargo mutants` substitutions like “replace body with `Default::default()`”
/// type-correct for generic methods such as [`Located::dummy`].
/// Those mutants are then caught by tests when they run.
impl<T> Default for Located<T> {
    fn default() -> Self {
        panic!(
            "Located<T>::default() is not supported; use Located::new(node, span) or Located::dummy(node)"
        )
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

    #[error("Warning at {span}: {message}")]
    WarningAt { span: Span, message: String },

    #[error(transparent)]
    Io(#[from] std::io::Error),
}

/// Sentinel empty plain error (used by mutation testing subs).
impl Default for CompileError {
    fn default() -> Self {
        CompileError::Plain(String::new())
    }
}

impl CompileError {
    /// Build a generic at-location error carrying only `message`.
    ///
    /// # Arguments
    ///
    /// * `span` — Where the problem was found.
    /// * `message` — Human-readable explanation.
    ///
    /// # Returns
    ///
    /// [`CompileError::AtSpan`].
    pub fn at(span: Span, message: impl Into<String>) -> Self {
        CompileError::AtSpan {
            span,
            message: message.into(),
        }
    }

    /// Error at `span` with an extra “hint:” line (handholding / Elm-style).
    ///
    /// # Arguments
    ///
    /// * `span` — Where the problem was found.
    /// * `message` — Primary explanation.
    /// * `hint` — Second line; if empty, only `message` is kept.
    ///
    /// # Returns
    ///
    /// [`CompileError::AtSpan`] with an optional appended hint line.
    pub fn at_with_hint(span: Span, message: impl Into<String>, hint: impl Into<String>) -> Self {
        let hint_s = hint.into();
        let msg = if hint_s.is_empty() {
            message.into()
        } else {
            format!("{}\n  hint: {}", message.into(), hint_s)
        };
        CompileError::AtSpan { span, message: msg }
    }

    /// Return the primary span when this variant carries one.
    ///
    /// # Returns
    ///
    /// `Some(span)` for located variants; `None` for [`CompileError::Plain`] and [`CompileError::Io`].
    pub fn span(&self) -> Option<&Span> {
        match self {
            CompileError::AtSpan { span, .. }
            | CompileError::WarningAt { span, .. }
            | CompileError::ParseError { span, .. }
            | CompileError::TypeError { span, .. } => Some(span),
            _ => None,
        }
    }

    /// Non-fatal diagnostic surfaced as [`CompileError::WarningAt`].
    ///
    /// # Arguments
    ///
    /// * `span` — Warning location.
    /// * `message` — Warning text.
    ///
    /// # Returns
    ///
    /// [`CompileError::WarningAt`].
    pub fn warning_at(span: Span, message: impl Into<String>) -> Self {
        CompileError::WarningAt {
            span,
            message: message.into(),
        }
    }
}

/// Collected compile diagnostics (similar to the Standard ML compiler’s global error log).
#[derive(Debug)]
pub struct ErrorReporter {
    pub errors: Vec<CompileError>,
    /// When false, errors are stored only (language server and incremental analysis).
    pub eprint: bool,
}

/// Default reporter prints each error to stderr as it is collected.
impl Default for ErrorReporter {
    fn default() -> Self {
        ErrorReporter {
            errors: Vec::new(),
            eprint: true,
        }
    }
}

impl ErrorReporter {
    /// Construct a reporter that echoes errors to stderr (CLI default).
    pub fn new() -> Self {
        ErrorReporter::default()
    }

    /// Collect diagnostics without printing to stderr (language servers, tests).
    ///
    /// # Returns
    ///
    /// Fresh reporter with `eprint: false`.
    pub fn new_silent() -> Self {
        ErrorReporter {
            errors: Vec::new(),
            eprint: false,
        }
    }

    /// Store `error` and optionally print it immediately.
    ///
    /// # Arguments
    ///
    /// * `error` — Diagnostic to append to [`ErrorReporter::errors`].
    ///
    /// # Returns
    ///
    /// Nothing.
    pub fn report(&mut self, error: CompileError) {
        if self.eprint {
            eprintln!("{error}");
        }
        self.errors.push(error);
    }

    /// Shorthand for [`CompileError::at`] followed by [`Self::report`].
    ///
    /// # Arguments
    ///
    /// * `span` — Error location.
    /// * `message` — Error text.
    ///
    /// # Returns
    ///
    /// Nothing.
    pub fn report_at(&mut self, span: Span, message: impl Into<String>) {
        self.report(CompileError::at(span, message));
    }

    /// Report at `span` with a second-line hint.
    ///
    /// # Arguments
    ///
    /// * `span` — Error location.
    /// * `message` — Primary text.
    /// * `hint` — Optional hint line.
    ///
    /// # Returns
    ///
    /// Nothing.
    pub fn report_at_with_hint(
        &mut self,
        span: Span,
        message: impl Into<String>,
        hint: impl Into<String>,
    ) {
        self.report(CompileError::at_with_hint(span, message, hint));
    }

    /// `true` if any diagnostic has been collected (warnings count too).
    ///
    /// # Returns
    ///
    /// Whether [`ErrorReporter::errors`] is non-empty.
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Clear accumulated diagnostics (tests and incremental analysis).
    ///
    /// # Returns
    ///
    /// Nothing.
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
    fn located_map_node_preserves_span() {
        let l: Located<i32> = Located::dummy(42);
        let l2 = Located::new(l.node + 1, l.span.clone());
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
    fn compile_error_at_with_hint_concatenates_hint_line() {
        let span = Span::dummy();
        let e = CompileError::at_with_hint(span.clone(), "bad", "try removing the duplicate");
        let s = e.to_string();
        assert!(s.contains("bad"));
        assert!(s.contains("hint:"));
        assert!(s.contains("duplicate"));
        assert_eq!(e.span(), Some(&span));
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

    /// `new_silent` must differ from [`Default::default`] so language-server analysis does not echo to stderr.
    #[test]
    fn error_reporter_new_silent_disables_eprint() {
        let silent = ErrorReporter::new_silent();
        assert!(!silent.eprint, "new_silent must set eprint=false");
        let loud = ErrorReporter::default();
        assert!(loud.eprint, "Default must keep eprint=true");
    }

    /// Replacing [`ErrorReporter::report_at_with_hint`] with a no-op would drop diagnostics (cargo-mutants).
    #[test]
    fn error_reporter_report_at_with_hint_pushes_one_diagnostic() {
        let mut reporter = ErrorReporter::new_silent();
        reporter.report_at_with_hint(Span::dummy(), "primary", "hint line");
        assert_eq!(reporter.errors.len(), 1);
        let text = reporter.errors[0].to_string();
        assert!(text.contains("primary"));
        assert!(text.contains("hint"));
    }
}
