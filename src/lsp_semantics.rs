//! Semantic LSP helpers: symbols, hover, completion, and token highlighting.

use std::collections::HashMap;
use std::path::Path;

use lsp_types::{
    CompletionItem, CompletionItemKind, CompletionResponse, DocumentHighlight,
    DocumentHighlightKind, DocumentSymbol, DocumentSymbolResponse, FoldingRange, FoldingRangeKind,
    InlayHint, InlayHintLabel, Location, MarkupContent, MarkupKind, Position, Range,
    SelectionRange, SemanticToken, SemanticTokenType, SemanticTokens, SignatureHelp,
    SignatureInformation, SymbolKind, TextEdit, Uri, WorkspaceEdit,
};

use crate::elaborated::type_display::format_constructor;
use crate::elaborated::{Declaration, File as ElabFile};
use crate::error_types::Span;
use crate::parse::lexical_analyzer::{tokenize_xml_aware, Token};

fn is_ident_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '\''
}

/// Extract identifier or `M.x.y` at LSP position (0-based line; UTF-16/byte OK for ASCII Ur).
pub fn word_at_cursor(text: &str, line0: u32, col0: u32) -> Option<String> {
    let lines: Vec<&str> = text.lines().collect();
    let line_idx = line0 as usize;
    let l = *lines.get(line_idx)?;
    let col = col0 as usize;
    let chars: Vec<char> = l.chars().collect();
    if col > chars.len() {
        return None;
    }
    let mut start = col;
    while start > 0 && is_ident_char(chars[start - 1]) {
        start -= 1;
    }
    let mut end = col;
    while end < chars.len() {
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
    Some(chars[start..end].iter().collect())
}

pub fn span_to_range(span: &Span) -> Range {
    Range {
        start: Position::new(span.first.line.saturating_sub(1), span.first.col),
        end: Position::new(span.last.line.saturating_sub(1), span.last.col),
    }
}

pub fn compiler_paths_match(open_key: &str, decl_file: &str) -> bool {
    let o = open_key.replace('\\', "/");
    let d = decl_file.replace('\\', "/");
    d == o || d.ends_with(&format!("/{o}")) || o.ends_with(&d)
}

/// Top-level value / rec binding in one source file (by `Span::file` path key).
#[derive(Clone, Debug)]
pub struct ValBinding {
    pub name: String,
    pub type_str: String,
    pub name_span: Span,
}

pub fn index_file_bindings(elab: &ElabFile, file_key: &str) -> Vec<ValBinding> {
    let mut out = Vec::new();
    for d in elab {
        if !compiler_paths_match(file_key, &d.span.file) {
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

pub fn hover_markdown(
    elab: Option<&ElabFile>,
    file_key: &str,
    text: &str,
    line: u32,
    character: u32,
) -> Option<MarkupContent> {
    let word = word_at_cursor(text, line, character)?;
    let simple = word.rsplit('.').next()?.to_string();
    let idx = index_file_bindings(elab?, file_key);
    for b in &idx {
        if b.name == simple {
            let md = format!("**`{}`** : `{}`", b.name, b.type_str);
            return Some(MarkupContent {
                kind: MarkupKind::Markdown,
                value: md,
            });
        }
    }
    None
}

pub fn goto_definition(
    elab: Option<&ElabFile>,
    file_key: &str,
    uri_str: &str,
    text: &str,
    line: u32,
    character: u32,
) -> Option<Location> {
    let word = word_at_cursor(text, line, character)?;
    let simple = word.rsplit('.').next()?.to_string();
    let idx = index_file_bindings(elab?, file_key);
    for b in &idx {
        if b.name == simple {
            let uri: lsp_types::Uri = uri_str.parse().ok()?;
            return Some(Location {
                uri,
                range: span_to_range(&b.name_span),
            });
        }
    }
    None
}

pub fn completion_at_point(
    elab: Option<&ElabFile>,
    file_key: &str,
    text: &str,
    line: u32,
    character: u32,
) -> CompletionResponse {
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
        // Globals from project
        for (name, ty, _, _) in all_val_bindings(e) {
            if items.iter().any(|i| i.label == name) {
                continue;
            }
            if prefix.is_empty() || name.starts_with(&prefix) {
                items.push(CompletionItem {
                    label: name,
                    kind: Some(CompletionItemKind::VALUE),
                    detail: Some(ty),
                    ..Default::default()
                });
            }
        }
    }
    CompletionResponse::Array(items)
}

pub fn document_highlights(text: &str, line: u32, character: u32) -> Vec<DocumentHighlight> {
    let Some(word) = word_at_cursor(text, line, character) else {
        return vec![];
    };
    let simple = word.rsplit('.').next().unwrap_or(&word).to_string();
    if simple.is_empty() {
        return vec![];
    }
    let mut hi = Vec::new();
    for (i, l) in text.lines().enumerate() {
        let mut start = 0usize;
        while let Some(pos) = find_word(l, &simple, start) {
            hi.push(DocumentHighlight {
                range: Range {
                    start: Position::new(i as u32, pos as u32),
                    end: Position::new(i as u32, (pos + simple.len()) as u32),
                },
                kind: Some(DocumentHighlightKind::TEXT),
            });
            start = pos + simple.len();
        }
    }
    hi
}

fn find_word(hay: &str, needle: &str, start_byte: usize) -> Option<usize> {
    let h = hay.get(start_byte..)?;
    let idx = h.find(needle)?;
    let abs = start_byte + idx;
    // word boundary: char before not ident
    if abs > 0 {
        let c = hay.as_bytes()[abs - 1] as char;
        if is_ident_char(c) {
            return find_word(hay, needle, abs + needle.len());
        }
    }
    let after = abs + needle.len();
    if after < hay.len() {
        let c = hay.as_bytes()[after] as char;
        if is_ident_char(c) {
            return find_word(hay, needle, after);
        }
    }
    Some(abs)
}

#[allow(deprecated)]
pub fn document_symbols(elab: Option<&ElabFile>, file_key: &str) -> DocumentSymbolResponse {
    let mut syms = Vec::new();
    let Some(e) = elab else {
        return DocumentSymbolResponse::Nested(syms);
    };
    for b in index_file_bindings(e, file_key) {
        syms.push(DocumentSymbol {
            name: b.name,
            detail: Some(b.type_str.clone()),
            kind: SymbolKind::FUNCTION,
            tags: None,
            deprecated: None,
            range: span_to_range(&b.name_span),
            selection_range: span_to_range(&b.name_span),
            children: None,
        });
    }
    DocumentSymbolResponse::Nested(syms)
}

fn file_uri_for_workspace_path(workspace_root: &Path, rel_decl_path: &str) -> Option<Uri> {
    let rel = rel_decl_path.replace('\\', "/");
    let p = workspace_root.join(rel);
    let p = p.canonicalize().unwrap_or(p);
    let s = p.to_string_lossy();
    #[cfg(windows)]
    {
        let rest = s.trim_start_matches('\\');
        format!("file:///{}", rest.replace('\\', "/")).parse().ok()
    }
    #[cfg(not(windows))]
    {
        format!("file://{s}").parse().ok()
    }
}

#[allow(deprecated)]
pub fn workspace_symbol(
    elab: Option<&ElabFile>,
    workspace_root: &Path,
) -> Vec<lsp_types::SymbolInformation> {
    let mut out = Vec::new();
    let Some(e) = elab else {
        return out;
    };
    for (name, ty, span, _) in all_val_bindings(e) {
        let Some(uri) = file_uri_for_workspace_path(workspace_root, &span.file) else {
            continue;
        };
        out.push(lsp_types::SymbolInformation {
            name,
            kind: SymbolKind::FUNCTION,
            tags: None,
            deprecated: None,
            location: Location {
                uri,
                range: span_to_range(&span),
            },
            container_name: Some(ty),
        });
    }
    out
}

pub fn references_in_file(text: &str, line: u32, character: u32, uri_str: &str) -> Vec<Location> {
    document_highlights(text, line, character)
        .into_iter()
        .filter_map(|h| {
            let uri: lsp_types::Uri = uri_str.parse().ok()?;
            Some(Location {
                uri,
                range: h.range,
            })
        })
        .collect()
}

pub fn workspace_edit_rename(uri_str: &str, range: Range, new_name: &str) -> Option<WorkspaceEdit> {
    let uri: Uri = uri_str.parse().ok()?;
    let mut changes = HashMap::new();
    changes.insert(
        uri,
        vec![TextEdit {
            range,
            new_text: new_name.to_string(),
        }],
    );
    Some(WorkspaceEdit {
        changes: Some(changes),
        document_changes: None,
        change_annotations: None,
    })
}

pub fn selection_range_at(text: &str, line: u32, character: u32) -> Option<SelectionRange> {
    let r = prepare_rename(text, line, character)?;
    Some(SelectionRange {
        range: r,
        parent: None,
    })
}

pub fn prepare_rename(text: &str, line: u32, character: u32) -> Option<Range> {
    let w = word_at_cursor(text, line, character)?;
    let simple = w.rsplit('.').next()?.to_string();
    let lines: Vec<&str> = text.lines().collect();
    let l = *lines.get(line as usize)?;
    let chars: Vec<char> = l.chars().collect();
    let col = character as usize;
    let mut start = col;
    while start > 0 && is_ident_char(chars[start - 1]) {
        start -= 1;
    }
    let mut end = col;
    while end < chars.len() && is_ident_char(chars[end]) {
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

pub fn signature_help(
    elab: Option<&ElabFile>,
    file_key: &str,
    text: &str,
    line: u32,
    character: u32,
) -> Option<SignatureHelp> {
    let lines: Vec<&str> = text.lines().collect();
    let l = *lines.get(line as usize)?;
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
    while pos > 0 && chars[pos - 1].is_ascii_whitespace() {
        pos -= 1;
    }
    let mut start = pos;
    while start > 0 && is_ident_char(chars[start - 1]) {
        start -= 1;
    }
    let fname: String = chars[start..pos].iter().collect();
    let simple = fname.rsplit('.').next()?;
    let idx = index_file_bindings(elab?, file_key);
    for b in idx {
        if b.name == simple {
            return Some(SignatureHelp {
                signatures: vec![SignatureInformation {
                    label: format!("{} : {}", b.name, b.type_str),
                    documentation: None,
                    parameters: None,
                    active_parameter: Some(0),
                }],
                active_signature: Some(0),
                active_parameter: Some(0),
            });
        }
    }
    None
}

/// Inlay hints: type as suffix on lines with `val` bindings (best-effort, same file).
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

/// Build semantic tokens from the **document buffer** (same coordinates as the editor).
/// If lexing fails (rare constructs), returns empty token data.
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

/// Folding regions from elaborated top-level `val` / `val rec` spans (compiler path keys).
pub fn folding_ranges_from_elab(elab: &ElabFile, file_key: &str) -> Vec<FoldingRange> {
    let mut out = Vec::new();
    for d in elab {
        if !compiler_paths_match(file_key, &d.span.file) {
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

/// Prefer elaborated [`Declaration::Val`] / [`Declaration::ValRec`] folding when analysis is available;
/// otherwise [`folding_ranges`]. If elaboration yields no multi-line regions, falls back to the heuristic.
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

/// Heuristic folding: one region per top-level `fun` / `val` block.
pub fn folding_ranges(text: &str) -> Vec<FoldingRange> {
    let mut out = Vec::new();
    let lines: Vec<&str> = text.lines().collect();
    let mut i = 0usize;
    while i < lines.len() {
        let t = lines[i].trim_start();
        if t.starts_with("fun ") || t.starts_with("val ") {
            let start_line = i as u32;
            let mut j = i + 1;
            while j < lines.len() {
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
