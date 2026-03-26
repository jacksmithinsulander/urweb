//! Ur/Web source normalization and layout for `ur-fmt` and LSP `textDocument/formatting`.
//!
//! Runs the same pre-parse rewrites as [`crate::parse::parse_ur`], requires a successful parse,
//! then applies stable whitespace rules (trailing space removal, blank-line collapse, EOF newline).

use crate::error_types::{CompileError, ErrorReporter};
use crate::parse::{parse_ur, parse_urs, preprocess_ur_for_parse};

/// Expand tab characters to spaces (column-aligned on `tab_width` boundaries).
fn expand_tabs(line: &str, tab_width: usize) -> String {
    if tab_width == 0 || !line.contains('\t') {
        return line.to_string();
    }
    let mut out = String::with_capacity(line.len());
    let mut col = 0usize;
    for ch in line.chars() {
        if ch == '\t' {
            let spaces = tab_width - (col % tab_width);
            for _ in 0..spaces {
                out.push(' ');
            }
            col += spaces;
        } else {
            out.push(ch);
            col = if ch == '\n' { 0 } else { col + 1 };
        }
    }
    out
}

/// Collapse trailing spaces, cap consecutive blank lines, ensure trailing newline.
fn layout_lines(preprocessed: &str, tab_width: usize) -> String {
    let lines: Vec<&str> = preprocessed.lines().collect();
    let mut out_lines: Vec<String> = Vec::with_capacity(lines.len());
    let mut blank_run = 0u32;
    for line in lines {
        let trimmed_end = line.trim_end();
        if trimmed_end.is_empty() {
            blank_run += 1;
            if blank_run <= 2 {
                out_lines.push(String::new());
            }
        } else {
            blank_run = 0;
            out_lines.push(expand_tabs(trimmed_end, tab_width));
        }
    }
    let mut s = out_lines.join("\n");
    if !s.ends_with('\n') {
        s.push('\n');
    }
    s
}

/// Format `.ur` source after pre-processing and parse validation.
pub fn format_ur(
    virtual_path: &str,
    source: &str,
    tab_width: usize,
) -> Result<String, Vec<CompileError>> {
    let pre = preprocess_ur_for_parse(source);
    let mut err = ErrorReporter::new_silent();
    if parse_ur(
        virtual_path,
        &pre,
        &mut err,
        crate::db::ProjectDb::default(),
    )
    .is_none()
    {
        return Err(err.errors);
    }
    Ok(layout_lines(&pre, tab_width))
}

/// Format `.urs` source (signature) after pre-processing and parse validation.
pub fn format_urs(
    virtual_path: &str,
    source: &str,
    tab_width: usize,
) -> Result<String, Vec<CompileError>> {
    use crate::parse::preprocess_urs;
    let pre = preprocess_urs(source);
    let mut err = ErrorReporter::new_silent();
    if parse_urs(virtual_path, &pre, &mut err).is_none() {
        return Err(err.errors);
    }
    Ok(layout_lines(&pre, tab_width))
}

/// Format either `.ur` or `.urs` based on `virtual_path` suffix.
pub fn format_source_path(
    virtual_path: &str,
    source: &str,
    tab_width: usize,
) -> Result<String, Vec<CompileError>> {
    if virtual_path.ends_with(".urs") {
        format_urs(virtual_path, source, tab_width)
    } else {
        format_ur(virtual_path, source, tab_width)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn layout_trims_trailing_and_caps_blanks() {
        let s = "a  \n\n\n\nb\t \n";
        let out = layout_lines(s, 4);
        assert_eq!(out, "a\n\n\nb\n");
    }

    #[test]
    fn layout_preserves_single_blank_lines() {
        let s = "x\n\ny\n";
        let out = layout_lines(s, 4);
        assert_eq!(out, "x\n\ny\n");
    }
}
