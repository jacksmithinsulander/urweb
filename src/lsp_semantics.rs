//! Language-server features built on elaborated sources: symbols, hover, completion, semantic highlighting.

use std::borrow::Cow;
use std::collections::HashSet;
use std::path::Path;

use lsp_types::{
    CompletionItem, CompletionItemKind, DocumentChanges, FoldingRange, FoldingRangeKind, InlayHint,
    InlayHintLabel, Location, MarkupContent, MarkupKind, OneOf,
    OptionalVersionedTextDocumentIdentifier, Position, Range, SelectionRange, SemanticToken,
    SemanticTokenType, SemanticTokens, TextDocumentEdit, TextEdit, Uri, WorkspaceEdit,
};

use crate::elaborated::type_display::format_constructor;
use crate::elaborated::{Declaration, File as ElabFile};
use crate::error_types::Span;
use crate::parse::lexical_analyzer::{tokenize_xml_aware, Token};

fn is_ident_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '\''
}

/// Extract a module-qualified identifier (`M.x.y`) or plain name at a zero-based line and column.
///
/// `col0` is a zero-based **character** index into the Unicode scalar sequence of that line (not a UTF-8 byte offset).
///
/// # Arguments
///
/// * `text` — Full document source.
/// * `line0` — Zero-based line index.
/// * `col0` — Zero-based column as character index within the line.
///
/// # Returns
///
/// Identifier string under/near the cursor, or `None` if the position is out of range or not on a word.
pub fn word_at_cursor(text: &str, line0: u32, col0: u32) -> Option<String> {
    let line_idx = line0 as usize;
    let l = text.lines().nth(line_idx)?;
    let col = col0 as usize;
    let chars: Vec<char> = l.chars().collect();
    if col > chars.len() {
        return None;
    }
    let mut start = col;
    for _ in 0..col {
        if start == 0 || !is_ident_char(chars[start - 1]) {
            break;
        }
        start -= 1;
    }
    let mut end = col;
    for _ in 0..chars.len() {
        if end >= chars.len() {
            break;
        }
        if is_ident_char(chars[end]) {
            end += 1;
            continue;
        }
        if chars[end] == '.'
            && end + 1 < chars.len()
            && (is_ident_char(chars[end + 1]) || chars[end + 1] == '_')
        {
            end += 1;
            continue;
        }
        break;
    }
    if start == end {
        return None;
    }
    debug_assert!(start <= end && end <= chars.len());
    Some(chars[start..end].iter().collect())
}

/// Map a compiler [`Span`] to a Language Server Protocol [`Range`] (zero-based lines).
///
/// # Arguments
///
/// * `span` — One-based lines and columns as stored in [`Span`].
///
/// # Returns
///
/// [`Range`] with lines decremented by one; columns copied as stored.
pub fn span_to_range(span: &Span) -> Range {
    Range {
        start: Position::new(span.first.line.saturating_sub(1), span.first.col),
        end: Position::new(span.last.line.saturating_sub(1), span.last.col),
    }
}

/// Whether a workspace-relative open key refers to the same file as an elaborated declaration path.
///
/// # Arguments
///
/// * `open_key` — Path from [`crate::lsp_workspace::file_key_relative_to_root`].
/// * `decl_file` — Path string stored on a declaration from elaboration.
///
/// # Returns
///
/// `true` when normalized strings denote the same file for navigation purposes.
pub fn compiler_paths_match(open_key: &str, decl_file: &str) -> bool {
    let o = slash_normalized_cow(open_key);
    paths_match_given_open_normalized(o.as_ref(), decl_file)
}

/// Slash-normalize a path key once, then compare to many `decl_file` values (avoids re-scanning `open_key`).
///
/// # Arguments
///
/// * `open_norm` — Return value from [`slash_normalized_cow`] for the workspace/open file key.
/// * `decl_file` — Path string from a declaration span (may use backslashes).
///
/// # Returns
///
/// Same as [`compiler_paths_match`] for this pair.
pub(crate) fn paths_match_given_open_normalized(open_norm: &str, decl_file: &str) -> bool {
    let d = slash_normalized_cow(decl_file);
    paths_match_normalized_pair(open_norm, d.as_ref())
}

/// Normalize backslashes to slashes when needed; borrows the input if it is already fine.
///
/// # Arguments
///
/// * `s` — A file path or workspace-relative key string.
///
/// # Returns
///
/// [`Cow::Borrowed`] when `s` contains no `\\`; otherwise an owned copy with slashes.
pub(crate) fn slash_normalized_cow(s: &str) -> Cow<'_, str> {
    if s.contains('\\') {
        Cow::Owned(s.replace('\\', "/"))
    } else {
        Cow::Borrowed(s)
    }
}

/// Compare two path keys that are already slash-normalized (internal helper).
fn paths_match_normalized_pair(oref: &str, dref: &str) -> bool {
    if dref == oref {
        return true;
    }
    let slash_then_o = !oref.is_empty()
        && dref.len() > oref.len()
        && dref.as_bytes()[dref.len() - oref.len() - 1] == b'/'
        && dref.ends_with(oref);
    let empty_o_slash_suffix = oref.is_empty() && dref.ends_with('/');
    if slash_then_o || empty_o_slash_suffix {
        return true;
    }
    oref.ends_with(dref)
}

/// Top-level value / rec binding in one source file (by `Span::file` path key).
#[derive(Clone, Debug, Default)]
pub struct ValBinding {
    pub name: String,
    pub type_str: String,
    pub name_span: Span,
}

/// Portable hover payload (`Default` exists so `cargo-mutants` can compile `Some(Default::default())` replacements).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SemanticsHoverMarkdown {
    /// When true, use [`MarkupKind::Markdown`]; otherwise plain text.
    pub markdown: bool,
    /// Body text shown in the editor hover widget.
    pub value: String,
}

impl SemanticsHoverMarkdown {
    /// Converts this value into an LSP [`MarkupContent`].
    pub fn into_lsp_markup(self) -> MarkupContent {
        MarkupContent {
            kind: if self.markdown {
                MarkupKind::Markdown
            } else {
                MarkupKind::PlainText
            },
            value: self.value,
        }
    }
}

/// File URI string plus range (`Default` supports mutation-test replacements for goto-definition-style results).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SemanticsLocation {
    /// Uniform resource identifier string (typically `file:`).
    pub uri_str: String,
    /// Editor range in LSP zero-based coordinates.
    pub range: Range,
}

impl SemanticsLocation {
    /// Builds an LSP [`Location`] when `uri_str` parses as a [`Uri`].
    pub fn try_lsp_location(self) -> Option<Location> {
        let uri: Uri = self.uri_str.parse().ok()?;
        Some(Location {
            uri,
            range: self.range,
        })
    }
}

/// One outline row for document symbols (converted to [`lsp_types::DocumentSymbol`] in the LSP binary).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SemanticsDocumentSymbol {
    /// Binding name shown in the symbol list.
    pub name: String,
    /// Optional detail line (pretty-printed type); empty means omit in LSP.
    pub detail: String,
    /// Whole-symbol span.
    pub range: Range,
    /// Name selection span (same as `range` for value bindings here).
    pub selection_range: Range,
}

/// One workspace-wide symbol with a resolvable `file:` URI string.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SemanticsWorkspaceSymbol {
    /// Binding name.
    pub name: String,
    /// Pretty-printed type string (shown as container/detail).
    pub type_str: String,
    /// `file:` URI as a string (must parse for client delivery).
    pub uri_str: String,
    /// Span within the declared file.
    pub range: Range,
}

/// Collect value and `val rec` bindings defined in `file_key` within an elaborated file list.
///
/// # Arguments
///
/// * `elab` — Elaborated top-level declarations.
/// * `file_key` — Workspace-relative path key to match against each declaration’s `span.file`.
///
/// # Returns
///
/// Bindings with name, pretty-printed type, and name span.
pub fn index_file_bindings(elab: &ElabFile, file_key: &str) -> Vec<ValBinding> {
    let mut out = Vec::new();
    let open_norm = slash_normalized_cow(file_key);
    let oref = open_norm.as_ref();
    for d in elab {
        if !paths_match_given_open_normalized(oref, &d.span.file) {
            continue;
        }
        match &d.node {
            Declaration::Val(name, _, ty, _) => {
                out.push(ValBinding {
                    name: name.clone(),
                    type_str: format_constructor(ty),
                    name_span: d.span.clone(),
                });
            }
            Declaration::ValRec(recs) => {
                for (name, _, ty, _) in recs {
                    out.push(ValBinding {
                        name: name.clone(),
                        type_str: format_constructor(ty),
                        name_span: d.span.clone(),
                    });
                }
            }
            _ => {}
        }
    }
    out
}

fn all_val_bindings(elab: &ElabFile) -> Vec<(String, String, Span, Span)> {
    let mut out = Vec::new();
    for d in elab {
        match &d.node {
            Declaration::Val(name, _, ty, _) => {
                out.push((
                    name.clone(),
                    format_constructor(ty),
                    d.span.clone(),
                    d.span.clone(),
                ));
            }
            Declaration::ValRec(recs) => {
                for (name, _, ty, _) in recs {
                    out.push((
                        name.clone(),
                        format_constructor(ty),
                        d.span.clone(),
                        d.span.clone(),
                    ));
                }
            }
            _ => {}
        }
    }
    out
}

/// Build Markdown hover content for the identifier at `(line, character)` when elaboration is available.
///
/// # Arguments
///
/// * `elab` — Optional elaborated program; hover needs `Some`.
/// * `file_key` — Current buffer’s path key.
/// * `text` — Buffer source for [`word_at_cursor`].
/// * `line` — Zero-based line.
/// * `character` — Zero-based column (character index into the line, same as [`word_at_cursor`]).
///
/// # Returns
///
/// Portable hover content, or `None` if nothing matches.
pub fn hover_markdown(
    elab: Option<&ElabFile>,
    file_key: &str,
    text: &str,
    line: u32,
    character: u32,
) -> Option<SemanticsHoverMarkdown> {
    let word = word_at_cursor(text, line, character)?;
    let simple = word.rsplit('.').next()?.to_string();
    let idx = index_file_bindings(elab?, file_key);
    for b in &idx {
        if b.name == simple {
            let md = format!("**`{}`** : `{}`", b.name, b.type_str);
            return Some(SemanticsHoverMarkdown {
                markdown: true,
                value: md,
            });
        }
    }
    None
}

/// Definition location for the identifier at `(line, character)` in the current file.
///
/// # Arguments
///
/// * `elab` — Elaborated program; required to resolve bindings.
/// * `file_key` — Workspace-relative path for the open buffer.
/// * `uri_str` — Same document as `text`, as a `file:` uniform resource identifier string.
/// * `text` — Buffer source.
/// * `line` / `character` — Zero-based cursor position (character column; see [`word_at_cursor`]).
///
/// # Returns
///
/// Location descriptor at the binding’s name span, or `None`.
pub fn goto_definition(
    elab: Option<&ElabFile>,
    file_key: &str,
    uri_str: &str,
    text: &str,
    line: u32,
    character: u32,
) -> Option<SemanticsLocation> {
    let word = word_at_cursor(text, line, character)?;
    let simple = word.rsplit('.').next()?.to_string();
    let idx = index_file_bindings(elab?, file_key);
    for b in &idx {
        if b.name == simple {
            uri_str.parse::<Uri>().ok()?;
            return Some(SemanticsLocation {
                uri_str: uri_str.to_string(),
                range: span_to_range(&b.name_span),
            });
        }
    }
    None
}

/// Completion items at `(line, character)` from local bindings and global values when elaboration exists.
///
/// # Arguments
///
/// * `elab` — Optional elaborated file list (empty completion when `None`).
/// * `file_key` — Current file path key.
/// * `text` — Buffer source.
/// * `line` / `character` — Zero-based cursor (see [`word_at_cursor`]).
///
/// # Returns
///
/// Completion items (wrap in [`lsp_types::CompletionResponse`] at the protocol edge).
pub fn completion_at_point(
    elab: Option<&ElabFile>,
    file_key: &str,
    text: &str,
    line: u32,
    character: u32,
) -> Vec<CompletionItem> {
    let prefix = word_at_cursor(text, line, character).unwrap_or_default();
    let mut items: Vec<CompletionItem> = Vec::new();
    if let Some(e) = elab {
        let local = index_file_bindings(e, file_key);
        for b in &local {
            if prefix.is_empty() || b.name.starts_with(&prefix) {
                items.push(CompletionItem {
                    label: b.name.clone(),
                    kind: Some(CompletionItemKind::VALUE),
                    detail: Some(b.type_str.clone()),
                    ..Default::default()
                });
            }
        }
        if prefix.contains('.') {
            // Module completion stub: suggest same local names after dot
            let after = prefix.rsplit('.').next().unwrap_or("");
            for b in &local {
                if after.is_empty() || b.name.starts_with(after) {
                    items.push(CompletionItem {
                        label: format!(
                            "{}.{}",
                            prefix.trim_end_matches(after).trim_end_matches('.'),
                            b.name
                        ),
                        kind: Some(CompletionItemKind::VALUE),
                        detail: Some(b.type_str.clone()),
                        ..Default::default()
                    });
                }
            }
        }
        // Globals from project (HashSet avoids O(n²) label scans over completion items).
        let mut global_labels: HashSet<String> =
            items.iter().map(|item| item.label.clone()).collect();
        for (name, ty, _, _) in all_val_bindings(e) {
            if global_labels.contains(&name) {
                continue;
            }
            if prefix.is_empty() || name.starts_with(&prefix) {
                global_labels.insert(name.clone());
                items.push(CompletionItem {
                    label: name,
                    kind: Some(CompletionItemKind::VALUE),
                    detail: Some(ty),
                    ..Default::default()
                });
            }
        }
    }
    items
}

/// Textual highlights of every occurrence of the word at `(line, character)` in `text`.
///
/// # Arguments
///
/// * `text` — Full buffer.
/// * `line` / `character` — Zero-based cursor (character column).
///
/// # Returns
///
/// Highlight ranges per match (may be empty); the LSP binary adds [`lsp_types::DocumentHighlightKind`].
pub fn document_highlights(text: &str, line: u32, character: u32) -> Vec<Range> {
    let Some(word) = word_at_cursor(text, line, character) else {
        return vec![];
    };
    let simple = word.rsplit('.').next().unwrap_or(&word).to_string();
    if simple.is_empty() {
        return vec![];
    }
    let mut ranges = Vec::new();
    for (i, l) in text.lines().enumerate() {
        let mut start = 0usize;
        let line_scan_budget = l.len().saturating_add(1);
        for _ in 0..line_scan_budget {
            let Some(pos) = find_word(l, &simple, start) else {
                break;
            };
            ranges.push(Range {
                start: Position::new(i as u32, pos as u32),
                end: Position::new(i as u32, (pos + simple.len()) as u32),
            });
            start = pos + simple.len();
        }
    }
    ranges
}

fn find_word(hay: &str, needle: &str, mut start_byte: usize) -> Option<usize> {
    if needle.is_empty() {
        return None;
    }
    let round_limit = hay.len().saturating_add(1);
    for _ in 0..round_limit {
        let h = hay.get(start_byte..)?;
        let idx = h.find(needle)?;
        let abs = start_byte + idx;
        if abs > 0 {
            let c = hay.as_bytes()[abs - 1] as char;
            if is_ident_char(c) {
                start_byte = abs + needle.len();
                continue;
            }
        }
        let after = abs + needle.len();
        if after < hay.len() {
            let c = hay.as_bytes()[after] as char;
            if is_ident_char(c) {
                start_byte = after;
                continue;
            }
        }
        return Some(abs);
    }
    debug_assert!(false, "find_word iteration bound exceeded");
    None
}

/// Document outline: value bindings in `file_key` when elaboration is present.
///
/// # Arguments
///
/// * `elab` — Optional elaborated program.
/// * `file_key` — File to list symbols for.
///
/// # Returns
///
/// Flat symbol rows (nested as [`lsp_types::DocumentSymbolResponse::Nested`] in the LSP binary).
pub fn document_symbols(elab: Option<&ElabFile>, file_key: &str) -> Vec<SemanticsDocumentSymbol> {
    let mut syms = Vec::new();
    let Some(e) = elab else {
        return syms;
    };
    for b in index_file_bindings(e, file_key) {
        let r = span_to_range(&b.name_span);
        syms.push(SemanticsDocumentSymbol {
            name: b.name,
            detail: b.type_str.clone(),
            range: r,
            selection_range: r,
        });
    }
    syms
}

fn file_uri_for_workspace_path(workspace_root: &Path, rel_decl_path: &str) -> Option<String> {
    let rel = rel_decl_path.replace('\\', "/");
    let p = workspace_root.join(rel);
    let p = p.canonicalize().unwrap_or(p);
    let s = p.to_string_lossy();
    #[cfg(windows)]
    {
        let rest = s.trim_start_matches('\\');
        let st = format!("file:///{}", rest.replace('\\', "/"));
        st.parse::<Uri>().ok()?;
        Some(st)
    }
    #[cfg(not(windows))]
    {
        let st = format!("file://{s}");
        st.parse::<Uri>().ok()?;
        Some(st)
    }
}

/// Workspace-wide symbols (all value bindings) with `file:` locations under `workspace_root`.
///
/// # Arguments
///
/// * `elab` — Optional elaborated program.
/// * `workspace_root` — Absolute workspace path for building `file:` URIs.
///
/// # Returns
///
/// Workspace symbol rows (map to [`lsp_types::SymbolInformation`] in the LSP binary).
pub fn workspace_symbol(
    elab: Option<&ElabFile>,
    workspace_root: &Path,
) -> Vec<SemanticsWorkspaceSymbol> {
    let mut out = Vec::new();
    let Some(e) = elab else {
        return out;
    };
    for (name, ty, span, _) in all_val_bindings(e) {
        let Some(uri_str) = file_uri_for_workspace_path(workspace_root, &span.file) else {
            continue;
        };
        out.push(SemanticsWorkspaceSymbol {
            name,
            type_str: ty,
            uri_str,
            range: span_to_range(&span),
        });
    }
    out
}

/// Same-buffer reference locations as [`document_highlights`], packaged as [`Location`] with `uri_str`.
///
/// # Arguments
///
/// * `text`, `line`, `character` — Same as [`document_highlights`].
/// * `uri_str` — Parseable [`Uri`] string for this document.
///
/// # Returns
///
/// One [`SemanticsLocation`] per highlight range (same `uri_str` repeated).
pub fn references_in_file(
    text: &str,
    line: u32,
    character: u32,
    uri_str: &str,
) -> Vec<SemanticsLocation> {
    if uri_str.parse::<Uri>().is_err() {
        return Vec::new();
    }
    document_highlights(text, line, character)
        .into_iter()
        .map(|range| SemanticsLocation {
            uri_str: uri_str.to_string(),
            range,
        })
        .collect()
}

/// Build a single-file rename [`WorkspaceEdit`] replacing `range` with `new_name`.
///
/// # Arguments
///
/// * `uri_str` — Target document uniform resource identifier.
/// * `range` — Span to overwrite.
/// * `new_name` — Replacement identifier text.
///
/// # Returns
///
/// `Some(edit)` when `uri_str` parses; unknown schemes yield `None`.
pub fn workspace_edit_rename(uri_str: &str, range: Range, new_name: &str) -> Option<WorkspaceEdit> {
    let uri: Uri = uri_str.parse().ok()?;
    Some(WorkspaceEdit {
        changes: None,
        document_changes: Some(DocumentChanges::Edits(vec![TextDocumentEdit {
            text_document: OptionalVersionedTextDocumentIdentifier { uri, version: None },
            edits: vec![OneOf::Left(TextEdit {
                range,
                new_text: new_name.to_string(),
            })],
        }])),
        change_annotations: None,
    })
}

/// Selection range hierarchy (stub: one level) from [`prepare_rename`].
///
/// # Arguments
///
/// * `text`, `line`, `character` — Buffer and zero-based cursor.
///
/// # Returns
///
/// [`SelectionRange`] or `None` when rename preparation fails.
pub fn selection_range_at(text: &str, line: u32, character: u32) -> Option<SelectionRange> {
    let r = prepare_rename(text, line, character)?;
    Some(SelectionRange {
        range: r,
        parent: None,
    })
}

/// Valid rename range for the identifier at the cursor, if it matches the parsed word.
///
/// # Arguments
///
/// * `text` — Buffer source.
/// * `line` / `character` — Zero-based position (character column).
///
/// # Returns
///
/// [`Range`] covering the simple name, or `None`.
pub fn prepare_rename(text: &str, line: u32, character: u32) -> Option<Range> {
    let w = word_at_cursor(text, line, character)?;
    let simple = w.rsplit('.').next()?.to_string();
    let l = text.lines().nth(line as usize)?;
    let chars: Vec<char> = l.chars().collect();
    let col = character as usize;
    let mut start = col;
    for _ in 0..col {
        if start == 0 || !is_ident_char(chars[start - 1]) {
            break;
        }
        start -= 1;
    }
    let mut end = col;
    for _ in 0..chars.len() {
        if end >= chars.len() || !is_ident_char(chars[end]) {
            break;
        }
        end += 1;
    }
    if chars.get(start..end).map(|s| s.iter().collect::<String>()) != Some(simple.clone()) {
        return None;
    }
    Some(Range {
        start: Position::new(line, start as u32),
        end: Position::new(line, end as u32),
    })
}

/// Best-effort signature help when the cursor is immediately after `(` on a callee name.
///
/// # Arguments
///
/// * `elab` — Elaborated bindings (required).
/// * `file_key` — Current file path key.
/// * `text` — Buffer lines.
/// * `line` / `character` — Zero-based cursor after the opening parenthesis.
///
/// # Returns
///
/// Signature label lines (typically one: `name : type`); the LSP binary wraps them in [`lsp_types::SignatureHelp`].
pub fn signature_help(
    elab: Option<&ElabFile>,
    file_key: &str,
    text: &str,
    line: u32,
    character: u32,
) -> Option<Vec<String>> {
    let l = text.lines().nth(line as usize)?;
    let col = character as usize;
    if col == 0
        || !l
            .as_bytes()
            .get(col - 1)
            .map(|b| *b == b'(')
            .unwrap_or(false)
    {
        return None;
    }
    let prefix = l.get(..col - 1)?;
    let chars: Vec<char> = prefix.chars().collect();
    let mut pos = chars.len();
    for _ in 0..chars.len() {
        if pos == 0 || !chars[pos - 1].is_ascii_whitespace() {
            break;
        }
        pos -= 1;
    }
    let mut start = pos;
    for _ in 0..pos {
        if start == 0 || !is_ident_char(chars[start - 1]) {
            break;
        }
        start -= 1;
    }
    let fname: String = chars[start..pos].iter().collect();
    let simple = fname.rsplit('.').next()?;
    let idx = index_file_bindings(elab?, file_key);
    for b in idx {
        if b.name == simple {
            return Some(vec![format!("{} : {}", b.name, b.type_str)]);
        }
    }
    None
}

/// Inlay hints: print inferred types after `val` binding names in `file_key` (same file, best-effort).
///
/// # Arguments
///
/// * `elab` — Optional elaborated program.
/// * `file_key` — Path key for filtering bindings.
/// * `_text` — Reserved for future context-aware placement.
///
/// # Returns
///
/// Zero or more [`InlayHint`] values.
pub fn inlay_hints(elab: Option<&ElabFile>, file_key: &str, _text: &str) -> Vec<InlayHint> {
    let mut hints = Vec::new();
    let Some(e) = elab else {
        return hints;
    };
    for b in index_file_bindings(e, file_key) {
        let line0 = b.name_span.first.line.saturating_sub(1);
        let col = b
            .name_span
            .first
            .col
            .saturating_add(b.name.chars().count() as u32);
        hints.push(InlayHint {
            position: Position::new(line0, col),
            label: InlayHintLabel::String(format!(": {}", b.type_str)),
            kind: None,
            text_edits: None,
            tooltip: None,
            padding_left: None,
            padding_right: Some(true),
            data: None,
        });
    }
    hints
}

/// Legend indices must match this order when encoding [`SemanticToken::token_type`].
pub const SEMANTIC_TOKEN_TYPES: &[SemanticTokenType] = &[
    SemanticTokenType::KEYWORD,
    SemanticTokenType::NAMESPACE,
    SemanticTokenType::FUNCTION,
    SemanticTokenType::VARIABLE,
    SemanticTokenType::STRING,
    SemanticTokenType::NUMBER,
    SemanticTokenType::OPERATOR,
];

fn token_type_index(tok: &Token) -> Option<u32> {
    use Token::*;
    Some(match tok {
        And | Andalso | Case | Class | Con | Constraint | Constraints | Cookie | Datatype
        | Else | End | Export | False | Ffi | Fn | Fun | Functor | If | In | Include | Let
        | Map | Of | Orelse | Open | Policy | Rec | Sequence | Sig | Signature | Struct
        | Structure | Style | Table | Task | Then | True | Type | Val | View | Where
        | SgnSubwhere | Name | KindType | KindUnit | WildAnnot | Action | All | Cconstraint
        | Cif | Cthen | Celse | Cwhere => 0,
        Ident(_) => 3,
        UpperIdent(_) | BacktickPath(_) => 1,
        Int(_) | Float(_) => 5,
        String(_) | Char(_) | Notags(_) => 4,
        Unit => 5,
        _ => 6,
    })
}

/// Build semantic tokens from the document buffer (editor coordinates).
///
/// If lexing fails on exotic input, returns token data with an empty `data` vec.
///
/// # Arguments
///
/// * `text` — Full source to tokenize.
///
/// # Returns
///
/// Always `Some`; inner `data` may be empty on lex failure.
pub fn semantic_tokens(text: &str) -> Option<SemanticTokens> {
    let tokens = match tokenize_xml_aware(text) {
        Ok(t) => t,
        Err(_) => {
            return Some(SemanticTokens {
                result_id: None,
                data: vec![],
            });
        }
    };
    let line_starts: Vec<usize> = text
        .char_indices()
        .filter(|(_, c)| *c == '\n')
        .map(|(i, _)| i)
        .collect();
    let mut out: Vec<SemanticToken> = Vec::new();
    let mut prev_line = 0u32;
    let mut prev_start = 0u32;
    for (lo, tok, hi) in tokens {
        let ty = token_type_index(&tok)?;
        if ty == 6
            && matches!(
                tok,
                Token::Lparen | Token::Rparen | Token::Semi | Token::Comma
            )
        {
            // include punctuation as operator
        }
        let (l0, c0) = byte_offset_to_lsp(&line_starts, lo);
        let len = (hi - lo) as u32;
        let dline = l0.saturating_sub(prev_line);
        let dstart = if dline == 0 {
            c0.saturating_sub(prev_start)
        } else {
            c0
        };
        out.push(SemanticToken {
            delta_line: dline,
            delta_start: dstart,
            length: len,
            token_type: ty,
            token_modifiers_bitset: 0,
        });
        prev_line = l0;
        prev_start = c0;
    }
    Some(SemanticTokens {
        result_id: None,
        data: out,
    })
}

/// Folding regions from elaborated top-level `val` / `val rec` spans that live in `file_key`.
///
/// # Arguments
///
/// * `elab` — Elaborated declarations.
/// * `file_key` — Workspace-relative path key.
///
/// # Returns
///
/// Ranges for multi-line bindings (may be empty).
pub fn folding_ranges_from_elab(elab: &ElabFile, file_key: &str) -> Vec<FoldingRange> {
    let mut out = Vec::new();
    let open_norm = slash_normalized_cow(file_key);
    let oref = open_norm.as_ref();
    for d in elab {
        if !paths_match_given_open_normalized(oref, &d.span.file) {
            continue;
        }
        match &d.node {
            Declaration::Val(_, _, _, _) | Declaration::ValRec(_) => {
                let start_line = d.span.first.line.saturating_sub(1);
                let end_line = d.span.last.line.saturating_sub(1);
                if end_line > start_line {
                    out.push(FoldingRange {
                        start_line,
                        start_character: None,
                        end_line,
                        end_character: None,
                        kind: Some(FoldingRangeKind::Region),
                        collapsed_text: None,
                    });
                }
            }
            _ => {}
        }
    }
    out
}

/// Prefer elaboration-based [`folding_ranges_from_elab`]; fall back to [`folding_ranges`] when missing or empty.
///
/// # Arguments
///
/// * `elab` — Optional elaborated file list.
/// * `file_key` — Current file key when `elab` is `Some`.
/// * `text` — Raw source for the heuristic fallback.
///
/// # Returns
///
/// [`FoldingRange`] list.
pub fn folding_ranges_with_analysis(
    elab: Option<&ElabFile>,
    file_key: Option<&str>,
    text: &str,
) -> Vec<FoldingRange> {
    if let (Some(e), Some(k)) = (elab, file_key) {
        let from_elab = folding_ranges_from_elab(e, k);
        if !from_elab.is_empty() {
            return from_elab;
        }
    }
    folding_ranges(text)
}

/// Heuristic folding: one region per top-level `fun` / `val` block (no elaboration).
///
/// # Arguments
///
/// * `text` — Full buffer source lines.
///
/// # Returns
///
/// Best-effort [`FoldingRange`] list.
pub fn folding_ranges(text: &str) -> Vec<FoldingRange> {
    let mut out = Vec::new();
    let lines: Vec<&str> = text.lines().collect();
    let line_count = lines.len();
    let mut i = 0usize;
    for _ in 0..line_count {
        if i >= lines.len() {
            break;
        }
        let t = lines[i].trim_start();
        if t.starts_with("fun ") || t.starts_with("val ") {
            let start_line = i as u32;
            let mut j = i + 1;
            for _ in 0..line_count {
                if j >= lines.len() {
                    break;
                }
                let t2 = lines[j].trim_start();
                if t2.starts_with("fun ") || t2.starts_with("val ") {
                    break;
                }
                j += 1;
            }
            let end_line = (j as u32).saturating_sub(1);
            if end_line > start_line {
                out.push(FoldingRange {
                    start_line,
                    start_character: None,
                    end_line,
                    end_character: None,
                    kind: Some(FoldingRangeKind::Region),
                    collapsed_text: None,
                });
            }
            i = j;
        } else {
            i += 1;
        }
    }
    out
}

fn byte_offset_to_lsp(line_starts: &[usize], offset: usize) -> (u32, u32) {
    match line_starts.binary_search(&offset) {
        Ok(i) => (i as u32 + 1, 0),
        Err(i) => {
            let line = i as u32;
            let line_start = if i == 0 { 0 } else { line_starts[i - 1] + 1 };
            (line, (offset - line_start) as u32)
        }
    }
}

#[cfg(test)]
mod folding_tests {
    use super::*;
    use crate::elaborated::{Constructor, Expression};
    use crate::error_types::{Located, Pos, Span};

    fn dummy_val_decl(span: Span) -> crate::elaborated::LocatedDeclaration {
        let ty = Located::dummy(Constructor::Error);
        let ex = Located::dummy(Expression::Error);
        Located::new(Declaration::Val("x".into(), 0, ty, ex), span)
    }

    #[test]
    fn folding_from_elab_maps_span_to_lsp_lines() {
        let span = Span {
            file: "lib.ur".into(),
            first: Pos { line: 2, col: 0 },
            last: Pos { line: 5, col: 0 },
        };
        let elab: ElabFile = vec![dummy_val_decl(span)];
        let folds = folding_ranges_from_elab(&elab, "lib.ur");
        assert_eq!(folds.len(), 1);
        assert_eq!(folds[0].start_line, 1);
        assert_eq!(folds[0].end_line, 4);
    }

    #[test]
    fn folding_with_analysis_uses_heuristic_without_elab() {
        let text = "val a = 1\n\nval b =\n  2\n";
        let h = folding_ranges(text);
        let w = folding_ranges_with_analysis(None, None, text);
        assert_eq!(w, h);
        assert!(!w.is_empty());
    }

    #[test]
    fn folding_with_analysis_prefers_elab_when_non_empty() {
        let span = Span {
            file: "m.ur".into(),
            first: Pos { line: 1, col: 0 },
            last: Pos { line: 4, col: 0 },
        };
        let elab: ElabFile = vec![dummy_val_decl(span)];
        // Heuristic would not match: no "val " at line start after trim in the same way
        let text = "(* no val here *)\nfoo\nbar\nbaz\n";
        let h = folding_ranges(text);
        let w = folding_ranges_with_analysis(Some(&elab), Some("m.ur"), text);
        assert!(
            h.is_empty(),
            "heuristic should not see a top-level val/fun block"
        );
        assert_eq!(w.len(), 1);
    }
}

/// Fast checks for language-server helpers listed in `mutants.out/timeout.txt` (`word_at_cursor`, `completion_at_point`, …).
#[cfg(test)]
mod semantic_api_mutation_guards {
    use super::*;
    use crate::elaborated::{Constructor, Expression};
    use crate::error_types::{Located, Pos, Span};
    use lsp_types::DocumentChanges;

    fn loc_span(file: &str) -> Span {
        Span {
            file: file.into(),
            first: Pos { line: 1, col: 0 },
            last: Pos { line: 1, col: 3 },
        }
    }

    fn val_binding(name: &str, file: &str) -> crate::elaborated::LocatedDeclaration {
        let ty = Located::dummy(Constructor::Error);
        let ex = Located::dummy(Expression::Error);
        Located::new(Declaration::Val(name.into(), 0, ty, ex), loc_span(file))
    }

    #[test]
    fn word_at_cursor_extracts_identifiers() {
        assert_eq!(word_at_cursor("val abc = 1", 0, 4).as_deref(), Some("abc"));
        assert_eq!(
            word_at_cursor("open Mod.Sub\n", 0, 7).as_deref(),
            Some("Mod.Sub")
        );
        assert_eq!(word_at_cursor("val x' = 1", 0, 5).as_deref(), Some("x'"));
        assert!(word_at_cursor("   \n", 0, 1).is_none());
        assert!(word_at_cursor("a", 0, 5).is_none());
    }

    #[test]
    fn span_to_range_shifts_compiler_lines_to_lsp() {
        let span = Span {
            file: "f.ur".into(),
            first: Pos { line: 2, col: 1 },
            last: Pos { line: 3, col: 5 },
        };
        let r = span_to_range(&span);
        assert_eq!(r.start.line, 1);
        assert_eq!(r.end.line, 2);
        assert_eq!(r.start.character, 1);
    }

    #[test]
    fn compiler_paths_match_accepts_suffix_and_backslash() {
        assert!(compiler_paths_match("lib/M.ur", "lib/M.ur"));
        assert!(compiler_paths_match("M.ur", "nested/lib/M.ur"));
        assert!(compiler_paths_match(r"a\b.ur", "a/b.ur"));
        assert!(!compiler_paths_match("A.ur", "B.ur"));
    }

    #[test]
    fn index_file_bindings_scopes_to_path_key() {
        let elab: ElabFile = vec![
            val_binding("in_file", "here.ur"),
            val_binding("other", "there.ur"),
        ];
        let local = index_file_bindings(&elab, "here.ur");
        assert_eq!(local.len(), 1);
        assert_eq!(local[0].name, "in_file");
        let merged = super::all_val_bindings(&elab);
        assert!(merged.iter().any(|(n, _, _, _)| n == "in_file"));
        assert!(merged.iter().any(|(n, _, _, _)| n == "other"));
    }

    #[test]
    fn hover_markdown_and_goto_definition_resolve_local_val() {
        let elab: ElabFile = vec![val_binding("fooey", "buf.ur")];
        let ho = hover_markdown(Some(&elab), "buf.ur", "val fooey = 1\n", 0, 4);
        assert!(ho.is_some());
        assert!(ho.unwrap().value.contains("fooey"));
        let uri = format!("file://{}", std::env::temp_dir().to_string_lossy());
        let go = goto_definition(Some(&elab), "buf.ur", &uri, "val fooey = 1\n", 0, 4);
        assert!(go.is_some());
    }

    #[test]
    fn completion_response_includes_typed_fields() {
        let elab: ElabFile = vec![val_binding("foobar", "z.ur")];
        let items = completion_at_point(Some(&elab), "z.ur", "foo", 0, 0);
        let item = items
            .iter()
            .find(|i| i.label == "foobar")
            .expect("local val");
        assert!(item.kind.is_some());
        assert!(item.detail.as_ref().is_some_and(|d| !d.is_empty()));
    }

    #[test]
    fn document_highlights_two_occurrences() {
        let buf = "val alpha = 1\nval beta = alpha\n";
        let hi = document_highlights(buf, 0, 4);
        assert!(
            hi.len() >= 2,
            "expected repeated identifier to produce multiple highlight ranges"
        );
    }

    #[test]
    fn workspace_symbol_returns_named_location() {
        let tmp = tempfile::tempdir().unwrap();
        let elab: ElabFile = vec![val_binding("globSym", "one.ur")];
        let syms = workspace_symbol(Some(&elab), tmp.path());
        assert_eq!(syms.len(), 1);
        assert_eq!(syms[0].name, "globSym");
        assert!(syms[0].uri_str.starts_with("file://"));
    }

    #[test]
    fn references_in_file_packs_locations() {
        let locs = references_in_file("val k = 1\nk\n", 0, 4, "file:///tmp/x.ur");
        assert!(!locs.is_empty());
    }

    #[test]
    fn file_uri_for_workspace_path_is_file_scheme() {
        let tmp = tempfile::tempdir().unwrap();
        std::fs::write(tmp.path().join("only.ur"), "").unwrap();
        let uri = super::file_uri_for_workspace_path(tmp.path(), "only.ur").expect("uri");
        assert!(uri.starts_with("file://"), "None mutant loses file: URI");
    }

    #[test]
    fn workspace_edit_rename_carries_text_change() {
        let range = Range {
            start: Position::new(0, 0),
            end: Position::new(0, 3),
        };
        let edit = workspace_edit_rename("file:///tmp/r.ur", range, "new").expect("edit");
        let DocumentChanges::Edits(edits) = edit.document_changes.expect("changes") else {
            panic!("expected text edits");
        };
        assert!(!edits.is_empty());
    }

    #[test]
    fn selection_range_and_prepare_rename_align_on_word() {
        let buf = "val renamed =\n  0\n";
        let sr = selection_range_at(buf, 0, 4).expect("range");
        assert_eq!(sr.range.start.line, 0);
        let pr = prepare_rename(buf, 0, 4).expect("rename");
        assert!(pr.end.character > pr.start.character);
    }

    #[test]
    fn signature_help_identifies_callee_before_paren() {
        let elab: ElabFile = vec![val_binding("callee", "c.ur")];
        let line = "callee(";
        let labels = signature_help(Some(&elab), "c.ur", line, 0, line.len() as u32)
            .expect("signature help");
        assert!(!labels.is_empty());
        assert!(labels[0].contains("callee"));
    }
}
