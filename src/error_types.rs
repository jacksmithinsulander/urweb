//! Diagnostics: positions, spans, and error accumulation for the batch compiler and the language server.
//!
//! [`Pos`] is a line and column in a source file (one-based line numbers in human output).
//! [`Span`] names the file plus start and end [`Pos`] values.
//! [`Located`] pairs any node with a [`Span`] (like Standard ML’s located type).
//! [`CompileError`] covers parse and type messages, warnings, and input/output failures.
//! Use [`CompileError::type_at`] for elaboration, [`CompileError::parse_at`] for surface syntax,
//! [`CompileError::sql_at`] for SQL/view/table issues in lowering, [`CompileError::xml_at`] for markup-focused
//! diagnostics, and [`CompileError::at`] when none of those fits (generic `-- ERROR`).
//! [`ErrorReporter`] collects diagnostics; silent reporters feed the Language Server Protocol without printing.
//!
//! Terminal output uses a structured, conversational layout (Elm-inspired): a labeled banner,
//! a short explanation, the source location, and optional hints so fixes feel guided rather than abrupt.
//!
//! **Language Server Protocol:** use [`format_compile_error_for_user`] with a project [`DiagnosticLocale`] for
//! `Diagnostic.message` so editors match the batch compiler (no ANSI escapes). **Interactive terminals:** the batch
//! compiler’s [`ErrorReporter`] prints with [`format_compile_error_for_terminal`] when stderr is a TTY
//! and [`NO_COLOR`](https://no-color.org/) is unset. **CLI tools** (for example the debugger) can use
//! [`format_tool_diagnostic_banner_and_body`] when the failure is not a [`CompileError`].
//! [`CompileError`]'s [`std::fmt::Display`] delegates to [`format_compile_error_for_terminal`] with
//! [`crate::cli_common::diagnostic_locale_for_cli`] so default printing matches the catalog + locale story.
//! Use [`UrDiagnostic`] when you want the same name across compiler, LSP, DAP, and CLI (`CompileError` is that type).

use std::fmt;
use std::fmt::Write as _;
use std::io::IsTerminal as _;
use std::io::Write as _;

use crate::diagnostics::{
    format_diagnostic_payload_for_user, DiagnosticId, DiagnosticLocale, DiagnosticPayload,
};

/// Minimum dash run width so banners never collapse to a tiny rule.
const DIAGNOSTIC_BANNER_MIN_DASH_RUN: usize = 8;
/// Target total width for the `-- LABEL --- file` banner line (excluding trailing newline).
const DIAGNOSTIC_BANNER_TARGET_WIDTH: usize = 62;
/// Prefix after the main paragraph when a [`DiagnosticPayload`] carries a [`crate::diagnostics::DiagnosticHint`].
pub(crate) use crate::diagnostics::HINT_TRAILER_PREFIX;

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
    /// Writes this position as `line:col` for humans.
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
    /// Builds [`Span::dummy`] as the default.
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

    /// Set [`Span::file`] when the parser left it empty (LALRPOP actions use `Span::from_offsets("", …)`).
    ///
    /// Wrapper declarations that already use labels like `"<basis>"` are unchanged.
    pub fn ensure_file_label(&mut self, file_label: &str) {
        if self.file.is_empty() {
            self.file = file_label.to_string();
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

    /// UTF-8 byte indices of every `\n` in `source`, sorted (same convention as [`Span::from_offsets`] tests).
    pub(crate) fn newline_byte_indices_in_utf8_source(source: &str) -> Vec<usize> {
        source
            .char_indices()
            .filter_map(|(byte_offset, ch)| (ch == '\n').then_some(byte_offset))
            .collect()
    }

    /// Turn LALRPOP placeholder spans (`from_offsets("", l, r, &[])`) into real line/column using lexer bytes.
    ///
    /// Those spans store UTF-8 **byte offsets** from the start of the preprocessed buffer as
    /// `line == 1`, `col == offset`. Pass the **exact** string the lexer parsed (preprocessed `.ur` / `.urs`).
    pub fn remap_after_lalrpop_parse(&mut self, file_label: &str, preprocessed: &str) {
        let line_table = Span::newline_byte_indices_in_utf8_source(preprocessed);
        self.remap_after_lalrpop_parse_with_line_table(file_label, preprocessed, &line_table);
    }

    /// Same as [`Span::remap_after_lalrpop_parse`], but reuses a precomputed newline table.
    pub fn remap_after_lalrpop_parse_with_line_table(
        &mut self,
        file_label: &str,
        preprocessed: &str,
        line_table: &[usize],
    ) {
        if self.first.line == 0 || self.last.line == 0 {
            self.ensure_file_label(file_label);
            return;
        }
        if self.first.line != 1 || self.last.line != 1 {
            self.ensure_file_label(file_label);
            return;
        }
        if preprocessed.is_empty() {
            self.ensure_file_label(file_label);
            return;
        }
        let start_byte = self.first.col as usize;
        let end_byte = self.last.col as usize;
        if start_byte > end_byte {
            self.ensure_file_label(file_label);
            return;
        }
        let last_byte = preprocessed.len().saturating_sub(1);
        let start_byte = start_byte.min(last_byte);
        let end_byte = end_byte.min(last_byte).max(start_byte);
        *self = Span::from_offsets(file_label, start_byte, end_byte, line_table);
    }
}

/// `file:first-last` for human-readable error banners.
impl std::fmt::Display for Span {
    /// Writes `file:first-last` using [`Pos`] display for each end.
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
#[derive(Debug)]
pub enum CompileError {
    /// Catalogued body without a concrete source span (configuration, whole-project issues).
    Plain(DiagnosticPayload),
    /// Generic located diagnostic (elaboration, explicit, backend checks).
    AtSpan {
        span: Span,
        payload: DiagnosticPayload,
    },
    /// Lex/parse problems; same layout as other located errors but labeled “parse”.
    ParseError {
        span: Span,
        payload: DiagnosticPayload,
    },
    /// Type elaboration problems; labeled “type” for faster scanning.
    TypeError {
        span: Span,
        payload: DiagnosticPayload,
    },
    /// SQL / `table` / `view` / `sequence` lowering problems (`-- SQL` banner).
    SqlError {
        span: Span,
        payload: DiagnosticPayload,
    },
    /// Markup and `<xml>`-related compile diagnostics (`-- XML` banner).
    XmlError {
        span: Span,
        payload: DiagnosticPayload,
    },
    /// Non-fatal note; same layout with a “warning” banner.
    WarningAt {
        span: Span,
        payload: DiagnosticPayload,
    },
    /// Wrapped operating-system I/O failure (details are OS text after the catalog prelude).
    Io(std::io::Error),
}

/// Sentinel empty plain error (used by mutation testing subs).
impl Default for CompileError {
    fn default() -> Self {
        CompileError::Plain(DiagnosticPayload::new(DiagnosticId::EmptyPlain, Vec::new()))
    }
}

/// Builds an Elm-style `-- CATEGORY ----…---- file` banner line.
///
/// # Arguments
///
/// * `category_label` — Short uppercase-ish label, for example `TYPE` or `PARSE`.
/// * `location_suffix` — Usually a filename; empty when there is nothing to show at the end.
///
/// # Returns
///
/// A single line suitable for printing as the first line of a diagnostic.
fn format_diagnostic_banner_line(category_label: &str, location_suffix: &str) -> String {
    let mut banner = String::new();
    banner.push_str("-- ");
    banner.push_str(category_label);
    banner.push(' ');
    let used_without_dashes = banner.len();
    if location_suffix.is_empty() {
        let dash_count = DIAGNOSTIC_BANNER_TARGET_WIDTH
            .saturating_sub(used_without_dashes)
            .max(DIAGNOSTIC_BANNER_MIN_DASH_RUN);
        banner.push_str(&"-".repeat(dash_count));
    } else {
        let tail_len = location_suffix.len().saturating_add(1);
        let dash_count = DIAGNOSTIC_BANNER_TARGET_WIDTH
            .saturating_sub(used_without_dashes + tail_len)
            .max(DIAGNOSTIC_BANNER_MIN_DASH_RUN);
        banner.push_str(&"-".repeat(dash_count));
        banner.push(' ');
        banner.push_str(location_suffix);
    }
    banner
}

/// Splits a message body from an optional hint line produced by [`CompileError::at_with_hint`].
///
/// # Arguments
///
/// * `message` — Full stored message, possibly including a `hint:` trailer.
///
/// # Returns
///
/// `(main_text, optional_hint_without_prefix)`.
fn split_message_and_hint(message: &str) -> (&str, Option<&str>) {
    if let Some(index) = message.find(HINT_TRAILER_PREFIX) {
        let main_part = message[..index].trim_end();
        let hint_part = message[index + HINT_TRAILER_PREFIX.len()..].trim();
        if hint_part.is_empty() {
            (message, None)
        } else {
            (main_part, Some(hint_part))
        }
    } else {
        (message, None)
    }
}

// ---------------------------------------------------------------------------
// Terminal ANSI styling (stderr only; never use for LSP or `to_string()`)
// ---------------------------------------------------------------------------

/// Reset all SGR attributes so later output is normal.
const ANSI_RESET: &str = "\x1b[0m";
/// Bold red banners for errors (`TYPE`, `PARSE`, generic `ERROR`, …).
const ANSI_BOLD_RED: &str = "\x1b[1;31m";
/// Bold yellow banner for [`CompileError::WarningAt`].
const ANSI_BOLD_YELLOW: &str = "\x1b[1;33m";
/// Bold cyan for the `-->` location line.
const ANSI_BOLD_CYAN: &str = "\x1b[1;36m";
/// Green hint body (readable on dark and light terminals).
const ANSI_GREEN: &str = "\x1b[32m";
/// Bold green `Hint:` label.
const ANSI_BOLD_GREEN: &str = "\x1b[1;32m";

/// Banner emphasis: error-like vs warning.
#[derive(Clone, Copy)]
enum BannerTone {
    /// All error severities except warnings.
    Error,
    /// [`CompileError::WarningAt`] only.
    Warning,
}

impl BannerTone {
    /// Opening SGR sequence for the dashed banner line.
    fn ansi_open(self) -> &'static str {
        match self {
            BannerTone::Error => ANSI_BOLD_RED,
            BannerTone::Warning => ANSI_BOLD_YELLOW,
        }
    }
}

/// True when stderr is a TTY and the user has not set [`NO_COLOR`](https://no-color.org/).
fn stderr_should_use_color() -> bool {
    std::env::var_os("NO_COLOR").is_none() && std::io::stderr().is_terminal()
}

/// Append trimmed multi-line explanation `body` to `out` (no trailing newline after last line).
fn write_wrapped_explanation_to_string(out: &mut String, body: &str) -> fmt::Result {
    let trimmed = body.trim();
    if trimmed.is_empty() {
        return Ok(());
    }
    for (line_index, line) in trimmed.lines().enumerate() {
        if line_index > 0 {
            out.push('\n');
        }
        out.push_str(line);
    }
    Ok(())
}

/// Append a located diagnostic with ANSI colors (banner, body, `--> span`, optional `Hint:`).
fn write_located_diagnostic_colored_to_string(
    out: &mut String,
    category_label: &str,
    span: &Span,
    message: &str,
    tone: BannerTone,
) -> fmt::Result {
    let banner_suffix = if span.file.is_empty() {
        String::new()
    } else {
        span.file.clone()
    };
    let banner_line = format_diagnostic_banner_line(category_label, banner_suffix.as_str());
    writeln!(out, "{}{}{}", tone.ansi_open(), banner_line, ANSI_RESET)?;
    writeln!(out)?;
    let (main_text, hint) = split_message_and_hint(message);
    write_wrapped_explanation_to_string(out, main_text)?;
    writeln!(out)?;
    writeln!(out)?;
    writeln!(out, "{}    --> {}{}", ANSI_BOLD_CYAN, span, ANSI_RESET)?;
    if let Some(hint_text) = hint {
        writeln!(out)?;
        writeln!(
            out,
            "{}Hint:{} {}{hint_text}{}",
            ANSI_BOLD_GREEN, ANSI_RESET, ANSI_GREEN, ANSI_RESET
        )?;
    }
    Ok(())
}

/// Append a non-located diagnostic with a colored banner and plain body.
fn write_plain_diagnostic_colored_to_string(
    out: &mut String,
    category_label: &str,
    message: &str,
) -> fmt::Result {
    let banner_line = format_diagnostic_banner_line(category_label, "");
    writeln!(out, "{}{}{}", ANSI_BOLD_RED, banner_line, ANSI_RESET)?;
    writeln!(out)?;
    write_wrapped_explanation_to_string(out, message)?;
    Ok(())
}

/// Colored variant of the [`CompileError::Io`] branch of [`fmt::Display`].
fn write_io_error_colored_to_string(
    out: &mut String,
    io_error: &std::io::Error,
    locale: DiagnosticLocale,
) -> fmt::Result {
    let banner_line = format_diagnostic_banner_line("IO", "");
    writeln!(out, "{}{}{}", ANSI_BOLD_RED, banner_line, ANSI_RESET)?;
    writeln!(out)?;
    let intro = format_diagnostic_payload_for_user(
        &DiagnosticPayload::new(DiagnosticId::IoSomethingWrongReadingWriting, Vec::new()),
        locale,
    );
    writeln!(out, "{intro}")?;
    writeln!(out)?;
    writeln!(out, "    {}", io_error)?;
    Ok(())
}

/// Colored stderr layout like [`fmt::Display`] but with [`DiagnosticLocale`] for template choice.
fn format_compile_error_for_terminal_inner(
    error: &CompileError,
    use_color: bool,
    locale: DiagnosticLocale,
) -> String {
    if !use_color {
        return format_compile_error_for_user(error, locale);
    }
    let mut out = String::new();
    let write_result = match error {
        CompileError::Plain(_) => {
            let localized = error.localized_body(locale);
            write_plain_diagnostic_colored_to_string(&mut out, "ERROR", localized.as_str())
        }
        CompileError::AtSpan { span, .. } => {
            let localized = error.localized_body(locale);
            write_located_diagnostic_colored_to_string(
                &mut out,
                "ERROR",
                span,
                localized.as_str(),
                BannerTone::Error,
            )
        }
        CompileError::ParseError { span, .. } => {
            let localized = error.localized_body(locale);
            write_located_diagnostic_colored_to_string(
                &mut out,
                "PARSE",
                span,
                localized.as_str(),
                BannerTone::Error,
            )
        }
        CompileError::TypeError { span, .. } => {
            let localized = error.localized_body(locale);
            write_located_diagnostic_colored_to_string(
                &mut out,
                "TYPE",
                span,
                localized.as_str(),
                BannerTone::Error,
            )
        }
        CompileError::SqlError { span, .. } => {
            let localized = error.localized_body(locale);
            write_located_diagnostic_colored_to_string(
                &mut out,
                "SQL",
                span,
                localized.as_str(),
                BannerTone::Error,
            )
        }
        CompileError::XmlError { span, .. } => {
            let localized = error.localized_body(locale);
            write_located_diagnostic_colored_to_string(
                &mut out,
                "XML",
                span,
                localized.as_str(),
                BannerTone::Error,
            )
        }
        CompileError::WarningAt { span, .. } => {
            let localized = error.localized_body(locale);
            write_located_diagnostic_colored_to_string(
                &mut out,
                "WARNING",
                span,
                localized.as_str(),
                BannerTone::Warning,
            )
        }
        CompileError::Io(io_error) => write_io_error_colored_to_string(&mut out, io_error, locale),
    };
    let _ = write_result; // discard the always-Ok String write result (String::write_fmt is infallible)
    out
}

/// Writes indented paragraphs for the main diagnostic text (leading/trailing whitespace trimmed).
///
/// # Arguments
///
/// * `formatter` — Destination formatter.
/// * `body` — Human-readable explanation; may contain internal newlines.
///
/// # Returns
///
/// `Ok(())` on successful write.
fn write_wrapped_explanation<W: fmt::Write>(formatter: &mut W, body: &str) -> fmt::Result {
    let trimmed = body.trim();
    if trimmed.is_empty() {
        return Ok(());
    }
    for (line_index, line) in trimmed.lines().enumerate() {
        if line_index > 0 {
            formatter.write_char('\n')?;
        }
        formatter.write_str(line)?;
    }
    Ok(())
}

/// Formats a located diagnostic: banner, explanation, `--> span`, optional hint block.
///
/// # Arguments
///
/// * `formatter` — Destination formatter.
/// * `category_label` — Banner label (`PORT`, `TYPE`, …).
/// * `span` — Source region; file name feeds the banner when non-empty.
/// * `message` — Possibly includes a hint trailer from [`CompileError::at_with_hint`].
///
/// # Returns
///
/// `Ok(())` on successful write.
fn write_located_diagnostic<W: fmt::Write>(
    formatter: &mut W,
    category_label: &str,
    span: &Span,
    message: &str,
) -> fmt::Result {
    let banner_suffix = if span.file.is_empty() {
        String::new()
    } else {
        span.file.clone()
    };
    writeln!(
        formatter,
        "{}",
        format_diagnostic_banner_line(category_label, banner_suffix.as_str())
    )?;
    writeln!(formatter)?;
    let (main_text, hint) = split_message_and_hint(message);
    write_wrapped_explanation(formatter, main_text)?;
    writeln!(formatter)?;
    writeln!(formatter)?;
    writeln!(formatter, "    --> {}", span)?;
    if let Some(hint_text) = hint {
        writeln!(formatter)?;
        writeln!(formatter, "Hint: {}", hint_text)?;
    }
    Ok(())
}

/// Formats errors that have no span: banner plus body only.
///
/// # Arguments
///
/// * `formatter` — Destination formatter.
/// * `category_label` — Short label for the dashed banner.
/// * `message` — Full error text.
///
/// # Returns
///
/// `Ok(())` on successful write.
fn write_plain_diagnostic<W: fmt::Write>(
    formatter: &mut W,
    category_label: &str,
    message: &str,
) -> fmt::Result {
    writeln!(
        formatter,
        "{}",
        format_diagnostic_banner_line(category_label, "")
    )?;
    writeln!(formatter)?;
    write_wrapped_explanation(formatter, message)?;
    Ok(())
}

impl fmt::Display for CompileError {
    /// Renders with [`format_compile_error_for_terminal`] and [`crate::cli_common::diagnostic_locale_for_cli`]
    /// (environment `URWEB_LANG`; project `ur.toml` applies once cwd/manifest loading has run).
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let locale = crate::cli_common::diagnostic_locale_for_cli(None);
        let localized = format_compile_error_for_terminal(self, locale);
        write!(formatter, "{localized}")
    }
}

/// [`std::error::Error::source`] is not overridden: full text (including I/O context for
/// [`CompileError::Io`]) is formatted in [`Display`](std::fmt::Display) via
/// [`format_compile_error_for_terminal`] / [`format_compile_error_for_user`], so callers do not
/// need an error chain through [`std::error::Error::source`].
impl std::error::Error for CompileError {}

/// Full multi-line diagnostic (banner, body, `-->`, hints) in `locale`.
///
/// # Arguments
///
/// * `error` — Collected diagnostic.
/// * `locale` — Project language from `ur.toml` / [`crate::settings::Settings`].
///
/// # Returns
///
/// Plain text suitable for Language Server Protocol `Diagnostic.message` and non-TTY stderr.
pub fn format_compile_error_for_user(error: &CompileError, locale: DiagnosticLocale) -> String {
    use std::fmt::Write as _;
    let mut buf = String::new();
    let localized = error.localized_body(locale);
    match error {
        CompileError::Plain(_) => {
            write_plain_diagnostic(&mut buf, "ERROR", localized.as_str()).ok(); // String writes are infallible; discard the always-Ok result
        }
        CompileError::AtSpan { span, .. } => {
            write_located_diagnostic(&mut buf, "ERROR", span, localized.as_str()).ok();
            // String writes are infallible; discard the always-Ok result
        }
        CompileError::ParseError { span, .. } => {
            write_located_diagnostic(&mut buf, "PARSE", span, localized.as_str()).ok();
            // String writes are infallible; discard the always-Ok result
        }
        CompileError::TypeError { span, .. } => {
            write_located_diagnostic(&mut buf, "TYPE", span, localized.as_str()).ok();
            // String writes are infallible; discard the always-Ok result
        }
        CompileError::SqlError { span, .. } => {
            write_located_diagnostic(&mut buf, "SQL", span, localized.as_str()).ok();
            // String writes are infallible; discard the always-Ok result
        }
        CompileError::XmlError { span, .. } => {
            write_located_diagnostic(&mut buf, "XML", span, localized.as_str()).ok();
            // String writes are infallible; discard the always-Ok result
        }
        CompileError::WarningAt { span, .. } => {
            let (main_text, hint) = split_message_and_hint(localized.as_str());
            let banner_suffix = if span.file.is_empty() {
                String::new()
            } else {
                span.file.clone()
            };
            writeln!(
                buf,
                "{}",
                format_diagnostic_banner_line("WARNING", banner_suffix.as_str())
            )
            .ok(); // String writes are infallible; discard the always-Ok result
            writeln!(buf).ok(); // String writes are infallible; discard the always-Ok result
            write_wrapped_explanation(&mut buf, main_text).ok(); // String writes are infallible; discard the always-Ok result
            writeln!(buf).ok(); // String writes are infallible; discard the always-Ok result
            writeln!(buf).ok(); // String writes are infallible; discard the always-Ok result
            writeln!(buf, "    --> {}", span).ok(); // String writes are infallible; discard the always-Ok result
            if let Some(hint_text) = hint {
                writeln!(buf).ok(); // String writes are infallible; discard the always-Ok result
                writeln!(buf, "Hint: {}", hint_text).ok(); // String writes are infallible; discard the always-Ok result
            }
        }
        CompileError::Io(io_error) => {
            writeln!(buf, "{}", format_diagnostic_banner_line("IO", "")).ok(); // String writes are infallible; discard the always-Ok result
            writeln!(buf).ok(); // String writes are infallible; discard the always-Ok result
            let intro = format_diagnostic_payload_for_user(
                &DiagnosticPayload::new(DiagnosticId::IoSomethingWrongReadingWriting, Vec::new()),
                locale,
            );
            writeln!(buf, "{intro}").ok(); // String writes are infallible; discard the always-Ok result
            writeln!(buf).ok(); // String writes are infallible; discard the always-Ok result
            writeln!(buf, "    {}", io_error).ok(); // String writes are infallible; discard the always-Ok result
        }
    }
    buf
}

/// Like [`format_compile_error_for_user`] but adds ANSI colors when stderr is a terminal and `NO_COLOR` is unset.
///
/// # Arguments
///
/// * `error` — Same diagnostic as stored in [`ErrorReporter::errors`].
/// * `locale` — Language for catalog templates (matches [`ErrorReporter::diagnostic_locale`] in batch compile).
///
/// # Returns
///
/// Plain text (identical to [`format_compile_error_for_user`]) or the same layout with SGR color sequences.
pub fn format_compile_error_for_terminal(error: &CompileError, locale: DiagnosticLocale) -> String {
    format_compile_error_for_terminal_inner(error, stderr_should_use_color(), locale)
}

/// Stable numeric [`DiagnosticId`] for Language Server Protocol `Diagnostic.code`, when present.
///
/// # Arguments
///
/// * `error` — Compiler diagnostic (I/O maps to [`DiagnosticId::IoSomethingWrongReadingWriting`]).
///
/// # Returns
///
/// `None` only if we cannot derive an id (should not happen for current variants).
pub fn compile_error_diagnostic_code(error: &CompileError) -> Option<u32> {
    Some(match error {
        CompileError::Plain(payload)
        | CompileError::AtSpan { payload, .. }
        | CompileError::ParseError { payload, .. }
        | CompileError::TypeError { payload, .. }
        | CompileError::SqlError { payload, .. }
        | CompileError::XmlError { payload, .. }
        | CompileError::WarningAt { payload, .. } => {
            crate::diagnostics::diagnostic_id_as_u32(payload.id)
        }
        CompileError::Io(_) => {
            crate::diagnostics::diagnostic_id_as_u32(DiagnosticId::IoSomethingWrongReadingWriting)
        }
    })
}

/// Exposes [`format_compile_error_for_terminal_inner`] for unit tests (force color on/off).
#[cfg(test)]
pub(crate) fn format_compile_error_for_terminal_test(
    error: &CompileError,
    ansi: bool,
    locale: DiagnosticLocale,
) -> String {
    format_compile_error_for_terminal_inner(error, ansi, locale)
}

/// Elm-style banner plus body for tools that are not [`CompileError`] (for example `ur-debugger`).
///
/// # Arguments
///
/// * `tool_banner_label` — Word after `-- ` on the banner line.
/// * `body` — Explanation; trimmed of outer whitespace.
///
/// # Returns
///
/// Banner line, blank line, then `body`.
pub fn format_tool_diagnostic_banner_and_body(tool_banner_label: &str, body: &str) -> String {
    let mut out = String::new();
    writeln!(
        out,
        "{}",
        format_diagnostic_banner_line(tool_banner_label, "")
    )
    .ok(); // String writes are infallible; discard the always-Ok result
    writeln!(out).ok(); // String writes are infallible; discard the always-Ok result
    out.push_str(body.trim());
    out
}

impl From<std::io::Error> for CompileError {
    /// Wraps an I/O error as [`CompileError::Io`] for `?` in I/O-heavy code paths.
    fn from(io_error: std::io::Error) -> Self {
        CompileError::Io(io_error)
    }
}

/// Alias for [`CompileError`]: one structured diagnostic type for the compiler, LSP, CLI, DAP, and debugger.
pub type UrDiagnostic = CompileError;

impl CompileError {
    /// Catalog-backed diagnostic with no source span (tools, protocol adapters, orchestration).
    ///
    /// # Arguments
    ///
    /// * `id` — Stable [`DiagnosticId`] template.
    /// * `args` — Placeholder values for `{0}`, `{1}`, … in that template.
    ///
    /// # Returns
    ///
    /// [`CompileError::Plain`] holding [`DiagnosticPayload::new`].
    pub fn catalog(id: DiagnosticId, args: Vec<String>) -> Self {
        CompileError::Plain(DiagnosticPayload::new(id, args))
    }

    /// Localized body (and hint trailer) without banner or `-->` line — used internally for splitting hints.
    ///
    /// # Arguments
    ///
    /// * `locale` — Active project language.
    ///
    /// # Returns
    ///
    /// Rendered catalog text for this error’s payload(s), including `hint:` prefix when applicable.
    pub fn localized_body(&self, locale: DiagnosticLocale) -> String {
        match self {
            CompileError::Plain(payload)
            | CompileError::AtSpan { payload, .. }
            | CompileError::ParseError { payload, .. }
            | CompileError::TypeError { payload, .. }
            | CompileError::SqlError { payload, .. }
            | CompileError::XmlError { payload, .. }
            | CompileError::WarningAt { payload, .. } => {
                format_diagnostic_payload_for_user(payload, locale)
            }
            CompileError::Io(io_error) => {
                let intro = format_diagnostic_payload_for_user(
                    &DiagnosticPayload::new(
                        DiagnosticId::IoSomethingWrongReadingWriting,
                        Vec::new(),
                    ),
                    locale,
                );
                format!("{intro}\n\n    {io_error}")
            }
        }
    }

    /// Build a generic at-location diagnostic from a catalog [`DiagnosticPayload`].
    ///
    /// # Arguments
    ///
    /// * `span` — Where the problem was found.
    /// * `payload` — Template id, arguments, optional hint / suffix payloads.
    ///
    /// # Returns
    ///
    /// [`CompileError::AtSpan`].
    pub fn at(span: Span, payload: DiagnosticPayload) -> Self {
        CompileError::AtSpan { span, payload }
    }

    /// [`CompileError::at`] with a hint template (`hint_id`, `hint_args`).
    ///
    /// # Arguments
    ///
    /// * `span` — Where the problem was found.
    /// * `payload` — Primary diagnostic (id + args); must not already carry a hint.
    /// * `hint_id` — Hint template id.
    /// * `hint_args` — Hint placeholder values.
    ///
    /// # Returns
    ///
    /// [`CompileError::AtSpan`] with [`DiagnosticPayload::hint`] set.
    pub fn at_with_hint(
        span: Span,
        payload: DiagnosticPayload,
        hint_id: DiagnosticId,
        hint_args: Vec<String>,
    ) -> Self {
        CompileError::AtSpan {
            span,
            payload: payload.with_hint(hint_id, hint_args),
        }
    }

    /// Located diagnostic for type elaboration (`-- TYPE` banner).
    ///
    /// # Arguments
    ///
    /// * `span` — Where the type problem was found.
    /// * `payload` — Catalog payload for the message.
    ///
    /// # Returns
    ///
    /// [`CompileError::TypeError`].
    pub fn type_at(span: Span, payload: DiagnosticPayload) -> Self {
        CompileError::TypeError { span, payload }
    }

    /// [`CompileError::type_at`] plus a structured hint.
    ///
    /// # Arguments
    ///
    /// * `span` — Source extent.
    /// * `payload` — Primary type error payload.
    /// * `hint_id` — Hint template id.
    /// * `hint_args` — Hint arguments.
    ///
    /// # Returns
    ///
    /// [`CompileError::TypeError`] with hint attached.
    pub fn type_at_with_hint(
        span: Span,
        payload: DiagnosticPayload,
        hint_id: DiagnosticId,
        hint_args: Vec<String>,
    ) -> Self {
        CompileError::TypeError {
            span,
            payload: payload.with_hint(hint_id, hint_args),
        }
    }

    /// Lexer/parser diagnostic (`-- PARSE` banner).
    ///
    /// # Arguments
    ///
    /// * `span` — Best-known source extent.
    /// * `payload` — Parse-related catalog payload.
    ///
    /// # Returns
    ///
    /// [`CompileError::ParseError`].
    pub fn parse_at(span: Span, payload: DiagnosticPayload) -> Self {
        CompileError::ParseError { span, payload }
    }

    /// Parse error with hint.
    ///
    /// # Arguments
    ///
    /// * `span` — Source extent.
    /// * `payload` — Primary payload.
    /// * `hint_id` — Hint template id.
    /// * `hint_args` — Hint args.
    ///
    /// # Returns
    ///
    /// [`CompileError::ParseError`] carrying `payload.with_hint(...)`.
    pub fn parse_at_with_hint(
        span: Span,
        payload: DiagnosticPayload,
        hint_id: DiagnosticId,
        hint_args: Vec<String>,
    ) -> Self {
        CompileError::ParseError {
            span,
            payload: payload.with_hint(hint_id, hint_args),
        }
    }

    /// SQL / table / view lowering (`-- SQL` banner).
    ///
    /// # Arguments
    ///
    /// * `span` — Source location.
    /// * `payload` — SQL-phase catalog payload.
    ///
    /// # Returns
    ///
    /// [`CompileError::SqlError`].
    pub fn sql_at(span: Span, payload: DiagnosticPayload) -> Self {
        CompileError::SqlError { span, payload }
    }

    /// SQL error with hint.
    ///
    /// # Arguments
    ///
    /// * `span` — Location.
    /// * `payload` — Primary payload.
    /// * `hint_id` — Hint id.
    /// * `hint_args` — Hint args.
    ///
    /// # Returns
    ///
    /// [`CompileError::SqlError`] with hint.
    pub fn sql_at_with_hint(
        span: Span,
        payload: DiagnosticPayload,
        hint_id: DiagnosticId,
        hint_args: Vec<String>,
    ) -> Self {
        CompileError::SqlError {
            span,
            payload: payload.with_hint(hint_id, hint_args),
        }
    }

    /// XML / markup diagnostic (`-- XML` banner).
    ///
    /// # Arguments
    ///
    /// * `span` — Source location.
    /// * `payload` — XML-phase catalog payload.
    ///
    /// # Returns
    ///
    /// [`CompileError::XmlError`].
    pub fn xml_at(span: Span, payload: DiagnosticPayload) -> Self {
        CompileError::XmlError { span, payload }
    }

    /// XML error with hint.
    ///
    /// # Arguments
    ///
    /// * `span` — Location.
    /// * `payload` — Primary payload.
    /// * `hint_id` — Hint id.
    /// * `hint_args` — Hint args.
    ///
    /// # Returns
    ///
    /// [`CompileError::XmlError`] with hint.
    pub fn xml_at_with_hint(
        span: Span,
        payload: DiagnosticPayload,
        hint_id: DiagnosticId,
        hint_args: Vec<String>,
    ) -> Self {
        CompileError::XmlError {
            span,
            payload: payload.with_hint(hint_id, hint_args),
        }
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
            | CompileError::TypeError { span, .. }
            | CompileError::SqlError { span, .. }
            | CompileError::XmlError { span, .. } => Some(span),
            _ => None,
        }
    }

    /// Non-fatal diagnostic surfaced as [`CompileError::WarningAt`].
    ///
    /// # Arguments
    ///
    /// * `span` — Warning location.
    /// * `payload` — Catalog payload for the warning body.
    ///
    /// # Returns
    ///
    /// [`CompileError::WarningAt`].
    pub fn warning_at(span: Span, payload: DiagnosticPayload) -> Self {
        CompileError::WarningAt { span, payload }
    }

    /// [`CompileError::warning_at`] with a structured hint template.
    ///
    /// # Arguments
    ///
    /// * `span` — Warning location.
    /// * `payload` — Primary warning payload.
    /// * `hint_id` — Hint template id.
    /// * `hint_args` — Hint arguments.
    ///
    /// # Returns
    ///
    /// [`CompileError::WarningAt`] with hint.
    pub fn warning_at_with_hint(
        span: Span,
        payload: DiagnosticPayload,
        hint_id: DiagnosticId,
        hint_args: Vec<String>,
    ) -> Self {
        CompileError::WarningAt {
            span,
            payload: payload.with_hint(hint_id, hint_args),
        }
    }
}

/// Collected compile diagnostics (similar to the Standard ML compiler’s global error log).
#[derive(Debug)]
pub struct ErrorReporter {
    pub errors: Vec<CompileError>,
    /// When false, errors are stored only (language server and incremental analysis).
    pub eprint: bool,
    /// Language for [`format_compile_error_for_terminal`] when `eprint` is true.
    pub diagnostic_locale: DiagnosticLocale,
}

/// Default reporter prints each error to stderr as it is collected.
impl Default for ErrorReporter {
    fn default() -> Self {
        ErrorReporter {
            errors: Vec::new(),
            eprint: true,
            diagnostic_locale: DiagnosticLocale::default(),
        }
    }
}

impl ErrorReporter {
    /// Construct a reporter that echoes errors to stderr (CLI default), English catalog strings.
    pub fn new() -> Self {
        ErrorReporter::default()
    }

    /// Reporter with a specific diagnostic locale (matches [`crate::settings::Settings::diagnostic_locale`] after manifest merge).
    ///
    /// # Arguments
    ///
    /// * `diagnostic_locale` — Project language from `ur.toml` `[package].language`.
    ///
    /// # Returns
    ///
    /// Reporter that still prints to stderr when reporting.
    pub fn new_with_locale(diagnostic_locale: DiagnosticLocale) -> Self {
        ErrorReporter {
            errors: Vec::new(),
            eprint: true,
            diagnostic_locale,
        }
    }

    /// Build from merged compiler [`crate::settings::Settings`] (stderr echo on).
    pub fn from_settings(settings: &crate::settings::Settings) -> Self {
        Self::new_with_locale(settings.diagnostic_locale)
    }

    /// Silent collection with explicit locale (language server analysis).
    pub fn new_silent_with_locale(diagnostic_locale: DiagnosticLocale) -> Self {
        ErrorReporter {
            errors: Vec::new(),
            eprint: false,
            diagnostic_locale,
        }
    }

    /// Silent reporter, English templates.
    pub fn new_silent() -> Self {
        Self::new_silent_with_locale(DiagnosticLocale::default())
    }

    /// Silent reporter using `settings.diagnostic_locale`.
    pub fn from_settings_silent(settings: &crate::settings::Settings) -> Self {
        Self::new_silent_with_locale(settings.diagnostic_locale)
    }

    /// Store `error` and optionally print it immediately.
    pub fn report(&mut self, error: CompileError) {
        if self.eprint {
            let rendered = format_compile_error_for_terminal(&error, self.diagnostic_locale); // Localized banner + body.
            let mut stderr_lock = std::io::stderr().lock(); // Avoid interleaving with other stderr users.
            let _ = writeln!(stderr_lock, "{rendered}"); // Primary diagnostic block.
            let _ = writeln!(stderr_lock); // Blank line before the next stderr message.
        }
        self.errors.push(error);
    }

    /// [`CompileError::at`] then [`Self::report`].
    pub fn report_at(&mut self, span: Span, payload: DiagnosticPayload) {
        self.report(CompileError::at(span, payload));
    }

    /// [`CompileError::at_with_hint`] then [`Self::report`].
    pub fn report_at_with_hint(
        &mut self,
        span: Span,
        payload: DiagnosticPayload,
        hint_id: DiagnosticId,
        hint_args: Vec<String>,
    ) {
        self.report(CompileError::at_with_hint(
            span, payload, hint_id, hint_args,
        ));
    }

    /// Surfaces a catalog warning (non-fatal) via [`CompileError::warning_at`].
    pub fn report_warning_at(&mut self, span: Span, payload: DiagnosticPayload) {
        self.report(CompileError::warning_at(span, payload));
    }

    /// Surfaces a catalog warning with structured hint, mirroring [`Self::report_at_with_hint`].
    pub fn report_warning_at_with_hint(
        &mut self,
        span: Span,
        payload: DiagnosticPayload,
        hint_id: DiagnosticId,
        hint_args: Vec<String>,
    ) {
        self.report(CompileError::warning_at_with_hint(
            span, payload, hint_id, hint_args,
        ));
    }

    /// [`CompileError::type_at`] (`-- TYPE`) then [`Self::report`].
    pub fn report_type_at(&mut self, span: Span, payload: DiagnosticPayload) {
        self.report(CompileError::type_at(span, payload));
    }

    /// [`CompileError::type_at_with_hint`] then [`Self::report`].
    pub fn report_type_at_with_hint(
        &mut self,
        span: Span,
        payload: DiagnosticPayload,
        hint_id: DiagnosticId,
        hint_args: Vec<String>,
    ) {
        self.report(CompileError::type_at_with_hint(
            span, payload, hint_id, hint_args,
        ));
    }

    /// [`CompileError::parse_at`] then [`Self::report`].
    pub fn report_parse_at(&mut self, span: Span, payload: DiagnosticPayload) {
        self.report(CompileError::parse_at(span, payload));
    }

    /// [`CompileError::parse_at_with_hint`] then [`Self::report`].
    pub fn report_parse_at_with_hint(
        &mut self,
        span: Span,
        payload: DiagnosticPayload,
        hint_id: DiagnosticId,
        hint_args: Vec<String>,
    ) {
        self.report(CompileError::parse_at_with_hint(
            span, payload, hint_id, hint_args,
        ));
    }

    /// [`CompileError::sql_at`] then [`Self::report`].
    pub fn report_sql_at(&mut self, span: Span, payload: DiagnosticPayload) {
        self.report(CompileError::sql_at(span, payload));
    }

    /// [`CompileError::sql_at_with_hint`] then [`Self::report`].
    pub fn report_sql_at_with_hint(
        &mut self,
        span: Span,
        payload: DiagnosticPayload,
        hint_id: DiagnosticId,
        hint_args: Vec<String>,
    ) {
        self.report(CompileError::sql_at_with_hint(
            span, payload, hint_id, hint_args,
        ));
    }

    /// [`CompileError::xml_at`] then [`Self::report`].
    pub fn report_xml_at(&mut self, span: Span, payload: DiagnosticPayload) {
        self.report(CompileError::xml_at(span, payload));
    }

    /// [`CompileError::xml_at_with_hint`] then [`Self::report`].
    pub fn report_xml_at_with_hint(
        &mut self,
        span: Span,
        payload: DiagnosticPayload,
        hint_id: DiagnosticId,
        hint_args: Vec<String>,
    ) {
        self.report(CompileError::xml_at_with_hint(
            span, payload, hint_id, hint_args,
        ));
    }
    /// `true` if any diagnostic has been collected (warnings count too).
    ///
    /// # Returns
    ///
    /// Whether [`ErrorReporter::errors`] is non-empty.
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// `true` when compilation should stop: at least one non-warning diagnostic was reported.
    ///
    /// # Returns
    ///
    /// Whether [`ErrorReporter::errors`] contains any entry other than [`CompileError::WarningAt`].
    pub fn has_hard_errors(&self) -> bool {
        self.errors
            .iter()
            .any(|entry| !matches!(entry, CompileError::WarningAt { .. }))
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
    use crate::diagnostics::{DiagnosticId, DiagnosticLocale, DiagnosticPayload};

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
        let mut r = ErrorReporter::new_silent();
        let span = Span::dummy();
        r.report_at(
            span,
            DiagnosticPayload::new(DiagnosticId::MutationTestingBadPlaceholder, vec![]),
        );
        assert!(r.has_errors());
    }

    #[test]
    fn error_reporter_report_type_at_produces_type_banner() {
        let mut reporter = ErrorReporter::new_silent();
        reporter.report_type_at(
            Span::dummy(),
            DiagnosticPayload::new(DiagnosticId::MutationTestingBadPlaceholder, vec![]),
        );
        let rendered = reporter.errors[0].to_string();
        assert!(
            rendered.contains("-- TYPE"),
            "expected TYPE category: {rendered}"
        );
    }

    #[test]
    fn error_reporter_report_parse_at_produces_parse_banner() {
        let mut reporter = ErrorReporter::new_silent();
        reporter.report_parse_at(
            Span::dummy(),
            DiagnosticPayload::new(DiagnosticId::MutationTestingBadPlaceholder, vec![]),
        );
        let rendered = reporter.errors[0].to_string();
        assert!(
            rendered.contains("-- PARSE"),
            "expected PARSE category: {rendered}"
        );
    }

    #[test]
    fn error_reporter_report_sql_at_produces_sql_banner() {
        let mut reporter = ErrorReporter::new_silent();
        reporter.report_sql_at(
            Span::dummy(),
            DiagnosticPayload::new(DiagnosticId::MutationTestingBadPlaceholder, vec![]),
        );
        assert!(reporter.errors[0].to_string().contains("-- SQL"));
    }

    #[test]
    fn error_reporter_report_xml_at_produces_xml_banner() {
        let mut reporter = ErrorReporter::new_silent();
        reporter.report_xml_at(
            Span::dummy(),
            DiagnosticPayload::new(DiagnosticId::MutationTestingBadPlaceholder, vec![]),
        );
        assert!(reporter.errors[0].to_string().contains("-- XML"));
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
    fn span_remap_after_lalrpop_parse_fixes_placeholder_line() {
        let pre = "hi\nyo";
        let mut s = Span::from_offsets("", 4, 5, &[]);
        s.remap_after_lalrpop_parse("f.ur", pre);
        assert_eq!(s.file, "f.ur");
        assert_eq!(s.first.line, 2);
        assert_eq!(s.last.line, 2);
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
        let mut r = ErrorReporter::new_silent();
        r.report(CompileError::Plain(DiagnosticPayload::new(
            DiagnosticId::MutationTestingBadPlaceholder,
            vec![],
        )));
        assert!(r.has_errors());
        r.reset();
        assert!(!r.has_errors());
    }

    #[test]
    fn error_reporter_warning_at_does_not_count_as_hard_error() {
        let mut reporter = ErrorReporter::new_silent();
        reporter.report(CompileError::warning_at(
            Span::dummy(),
            DiagnosticPayload::new(DiagnosticId::MutationTestingBadPlaceholder, vec![]),
        ));
        assert!(reporter.has_errors());
        assert!(
            !reporter.has_hard_errors(),
            "warnings alone must not trigger hard-error gates"
        );
    }

    #[test]
    fn compile_error_at_with_hint_renders_hint_section() {
        let span = Span {
            file: "Mod.ur".to_string(),
            first: Pos { line: 2, col: 1 },
            last: Pos { line: 2, col: 3 },
        };
        let e = CompileError::at_with_hint(
            span,
            DiagnosticPayload::new(
                DiagnosticId::LspUnusedValueNeverUsedFromEntry,
                vec!["Something is wrong here".into()],
            ),
            DiagnosticId::HintLspUnusedValueNeverUsedFromEntry,
            vec![],
        );
        let rendered = e.to_string();
        assert!(
            rendered.contains("-- ERROR"),
            "banner should identify generic errors: {rendered}"
        );
        assert!(rendered.contains("Something is wrong"));
        assert!(rendered.contains("Hint:"));
        assert!(rendered.contains("Delete it"));
        assert!(rendered.contains("Mod.ur"));
        assert!(rendered.contains("-->"));
        assert_eq!(
            e.span(),
            Some(&Span {
                file: "Mod.ur".to_string(),
                first: Pos { line: 2, col: 1 },
                last: Pos { line: 2, col: 3 },
            })
        );
    }

    #[test]
    fn compile_error_at_span_includes_location_arrow() {
        let span = Span {
            file: "test.ur".to_string(),
            first: Pos { line: 1, col: 0 },
            last: Pos { line: 1, col: 5 },
        };
        let e = CompileError::at(
            span.clone(),
            DiagnosticPayload::new(DiagnosticId::MutationTestingBadPlaceholder, vec![]),
        );
        let rendered = e.to_string();
        assert!(rendered.contains("bad"));
        assert!(rendered.contains("-- ERROR"));
        assert!(rendered.contains("-->"));
        assert_eq!(e.span(), Some(&span));
    }

    #[test]
    fn compile_error_type_variant_uses_type_banner() {
        let span = Span::dummy();
        let e = CompileError::TypeError {
            span,
            payload: DiagnosticPayload::new(DiagnosticId::MutationTestingBadPlaceholder, vec![]),
        };
        assert!(e.to_string().contains("-- TYPE"));
    }

    #[test]
    fn compile_error_parse_variant_uses_parse_banner() {
        let span = Span::dummy();
        let e = CompileError::ParseError {
            span,
            payload: DiagnosticPayload::new(DiagnosticId::MutationTestingBadPlaceholder, vec![]),
        };
        assert!(e.to_string().contains("-- PARSE"));
    }

    #[test]
    fn compile_error_sql_variant_uses_sql_banner() {
        let e = CompileError::sql_at(
            Span::dummy(),
            DiagnosticPayload::new(DiagnosticId::MutationTestingBadPlaceholder, vec![]),
        );
        let sql_text = e.to_string();
        assert!(
            sql_text.contains("-- SQL"),
            "expected SQL banner: {sql_text}"
        );
    }

    #[test]
    fn compile_error_xml_variant_uses_xml_banner() {
        let e = CompileError::xml_at(
            Span::dummy(),
            DiagnosticPayload::new(DiagnosticId::MutationTestingBadPlaceholder, vec![]),
        );
        assert!(e.to_string().contains("-- XML"));
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
        reporter.report_at_with_hint(
            Span::dummy(),
            DiagnosticPayload::new(DiagnosticId::MutationTestingBadPlaceholder, vec![]),
            DiagnosticId::HintParseUrSyntax,
            vec![],
        );
        assert_eq!(reporter.errors.len(), 1);
        let text = reporter.errors[0].to_string();
        assert!(text.contains("bad"));
        assert!(text.contains("Hint:"));
    }

    #[test]
    fn split_message_and_hint_recognizes_trailer() {
        let raw = format!("Main line.{HINT_TRAILER_PREFIX}Do this instead.");
        let (main, hint) = split_message_and_hint(&raw);
        assert_eq!(main, "Main line.");
        assert_eq!(hint, Some("Do this instead."));
    }

    #[test]
    fn format_compile_error_for_user_matches_forced_plain_terminal_path() {
        let e = CompileError::Plain(DiagnosticPayload::new(
            DiagnosticId::MutationTestingBadPlaceholder,
            vec![],
        ));
        let locale = crate::cli_common::diagnostic_locale_for_cli(None);
        assert_eq!(
            format_compile_error_for_user(&e, locale),
            format_compile_error_for_terminal_test(&e, false, locale),
            "`Display` may add ANSI when stderr is a TTY; plain TTY path must match LSP/user text"
        );
    }

    #[test]
    fn format_compile_error_for_terminal_plain_mode_matches_user_text() {
        let e = CompileError::type_at_with_hint(
            Span::dummy(),
            DiagnosticPayload::new(DiagnosticId::MutationTestingBadPlaceholder, vec![]),
            DiagnosticId::HintParseUrSyntax,
            vec![],
        );
        let locale = crate::cli_common::diagnostic_locale_for_cli(None);
        assert_eq!(
            format_compile_error_for_terminal_test(&e, false, locale),
            format_compile_error_for_user(&e, locale),
        );
    }

    /// [`CompileError`]'s [`std::fmt::Display`] must stay an alias for [`format_compile_error_for_terminal`].
    #[test]
    fn compile_error_display_matches_format_compile_error_for_terminal() {
        let e = CompileError::Plain(DiagnosticPayload::new(
            DiagnosticId::MutationTestingBadPlaceholder,
            vec![],
        ));
        let locale = crate::cli_common::diagnostic_locale_for_cli(None);
        assert_eq!(
            e.to_string(),
            format_compile_error_for_terminal(&e, locale),
            "`fmt::Display` delegates to `format_compile_error_for_terminal` with CLI locale"
        );
    }

    #[test]
    fn format_compile_error_for_terminal_forced_ansi_inserts_sgr() {
        let e = CompileError::warning_at(
            Span::dummy(),
            DiagnosticPayload::new(DiagnosticId::MutationTestingBadPlaceholder, vec![]),
        );
        let s = format_compile_error_for_terminal_test(&e, true, DiagnosticLocale::En);
        assert!(s.contains("\x1b["), "expected ANSI SGR sequences: {s:?}");
        assert!(s.contains("-- WARNING"));
    }

    #[test]
    fn format_tool_diagnostic_banner_matches_compiler_style() {
        let s = format_tool_diagnostic_banner_and_body("tool", "details");
        assert!(s.contains("-- tool"));
        assert!(s.contains("details"));
    }
}
