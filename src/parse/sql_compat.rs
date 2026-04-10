use crate::db::ProjectDb;
use crate::diagnostics::{DiagnosticId, DiagnosticPayload};
use crate::error_types::{ErrorReporter, Located, Span};
use crate::parse::grammar_helpers::{
    desugar_sql_delete_expression, desugar_sql_insert_expression, desugar_sql_select_query,
    desugar_sql_update_expression, sql_default_table_field_expression,
    sql_dynamic_field_expression, sql_field_expression, sql_join_expression,
    sql_select_dynamic_fields_item, sql_select_expression_item, sql_select_single_field_item,
    sql_table_reference_with_alias, sql_true_expression, SqlJoinKind, SqlSelectSpec,
};
use crate::primitives::{Prim, StringMode};
use crate::source::{Con, Decl, Exp, File, Inference, Kind, LocCon, LocExp, Pat};

const SQL_PLACEHOLDER_NAME: &str = "sql_demo_placeholder_compat";
const SYNTHETIC_SQL_EXPR_FILE: &str = "<sql-compat-expr>";
const SYNTHETIC_SQL_CON_FILE: &str = "<sql-compat-con>";
const SYNTHETIC_SQL_EXPR_BINDER: &str = "sqlcompatvalue";
const SYNTHETIC_SQL_CON_BINDER: &str = "sqlcompatcon";

fn skip_ml_comment_bytes(bytes: &[u8], mut index: usize, byte_length: usize) -> usize {
    let mut depth = 1usize;
    let scan_budget = byte_length.saturating_mul(2).saturating_add(1);
    for _ in 0..scan_budget {
        if index >= byte_length || depth == 0 {
            break;
        }
        match (
            index + 1 < byte_length,
            bytes.get(index).copied(),
            bytes.get(index + 1).copied(),
        ) {
            (true, Some(b'('), Some(b'*')) => {
                index += 2;
                depth = depth.saturating_add(1);
            }
            (true, Some(b'*'), Some(b')')) => {
                index += 2;
                depth = depth.saturating_sub(1);
            }
            _ => {
                index += 1;
            }
        }
    }
    index
}

fn skip_string_bytes(bytes: &[u8], mut index: usize, byte_length: usize) -> usize {
    let scan_budget = byte_length.saturating_sub(index).saturating_add(1);
    for _ in 0..scan_budget {
        if index >= byte_length {
            break;
        }
        match bytes.get(index).copied() {
            Some(b'"') => return index.saturating_add(1),
            Some(b'\\') if index + 1 < byte_length => {
                index += 2;
            }
            Some(_) => {
                index += 1;
            }
            None => break,
        }
    }
    byte_length
}

fn quote_string_literal(source_text: &str) -> String {
    let mut output_text = String::with_capacity(source_text.len().saturating_add(8));
    output_text.push('"');
    for ch in source_text.chars() {
        match ch {
            '\\' => output_text.push_str("\\\\"),
            '"' => output_text.push_str("\\\""),
            '\n' => output_text.push_str("\\n"),
            '\r' => output_text.push_str("\\r"),
            '\t' => output_text.push_str("\\t"),
            _ => output_text.push(ch),
        }
    }
    output_text.push('"');
    output_text
}

fn is_identifier_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'\''
}

fn starts_with_keyword(bytes: &[u8], index: usize, keyword: &[u8]) -> bool {
    if index + keyword.len() > bytes.len() {
        return false;
    }
    if &bytes[index..index + keyword.len()] != keyword {
        return false;
    }
    if index > 0 && is_identifier_byte(bytes[index - 1]) {
        return false;
    }
    if index + keyword.len() < bytes.len() && is_identifier_byte(bytes[index + keyword.len()]) {
        return false;
    }
    true
}

fn find_matching_rparen(
    source_text: &str,
    bytes: &[u8],
    open_paren_index: usize,
    byte_length: usize,
) -> Option<usize> {
    let mut depth = 1usize;
    let mut index = open_paren_index.saturating_add(1);
    let scan_budget = byte_length.saturating_mul(2).saturating_add(1);
    for _ in 0..scan_budget {
        if index >= byte_length {
            return None;
        }
        match (
            index + 1 < byte_length,
            bytes.get(index).copied(),
            bytes.get(index + 1).copied(),
        ) {
            (true, Some(b'('), Some(b'*')) => {
                index = skip_ml_comment_bytes(bytes, index + 2, byte_length);
            }
            (_, Some(b'"'), _) => {
                index = skip_string_bytes(bytes, index + 1, byte_length);
            }
            (_, Some(b'('), _) => {
                depth = depth.saturating_add(1);
                index += 1;
            }
            (_, Some(b')'), _) => {
                depth = depth.saturating_sub(1);
                index += 1;
                if depth == 0 {
                    return Some(index);
                }
            }
            _ => {
                let next_char = source_text[index..].chars().next().unwrap_or('\0');
                index += next_char.len_utf8();
            }
        }
    }
    None
}

fn placeholder_expression_text(payload: &str) -> String {
    format!("{SQL_PLACEHOLDER_NAME} {}", quote_string_literal(payload))
}

fn rewrite_parenthesized_sql_forms(source_text: &str) -> String {
    let bytes = source_text.as_bytes();
    let byte_length = bytes.len();
    let mut output_text = String::with_capacity(byte_length);
    let mut index = 0usize;
    let scan_budget = byte_length.saturating_add(1);
    for _ in 0..scan_budget {
        if index >= byte_length {
            break;
        }
        match (
            index + 1 < byte_length,
            bytes.get(index).copied(),
            bytes.get(index + 1).copied(),
        ) {
            (true, Some(b'('), Some(b'*')) => {
                let start = index;
                index = skip_ml_comment_bytes(bytes, index + 2, byte_length);
                output_text.push_str(&source_text[start..index]);
            }
            (_, Some(b'"'), _) => {
                let start = index;
                index = skip_string_bytes(bytes, index + 1, byte_length);
                output_text.push_str(&source_text[start..index]);
            }
            (_, Some(b'('), _) => {
                let mut lookahead = index + 1;
                let ws_budget = byte_length.saturating_add(1);
                for _ in 0..ws_budget {
                    if lookahead >= byte_length
                        || !matches!(bytes[lookahead], b' ' | b'\t' | b'\n' | b'\r')
                    {
                        break;
                    }
                    lookahead += 1;
                }
                let is_sql_form = starts_with_keyword(bytes, lookahead, b"SELECT")
                    || starts_with_keyword(bytes, lookahead, b"INSERT")
                    || starts_with_keyword(bytes, lookahead, b"DELETE")
                    || starts_with_keyword(bytes, lookahead, b"UPDATE")
                    || starts_with_keyword(bytes, lookahead, b"WHERE")
                    || starts_with_keyword(bytes, lookahead, b"SQL");
                match (
                    is_sql_form,
                    find_matching_rparen(source_text, bytes, index, byte_length),
                ) {
                    (true, Some(close_index)) => {
                        let payload = source_text[lookahead..close_index - 1].trim();
                        output_text.push('(');
                        output_text.push_str(&placeholder_expression_text(payload));
                        output_text.push(')');
                        index = close_index;
                    }
                    _ => {
                        output_text.push('(');
                        index += 1;
                    }
                }
            }
            _ => {
                let next_char = source_text[index..].chars().next().unwrap_or('\0');
                output_text.push(next_char);
                index += next_char.len_utf8();
            }
        }
    }
    output_text
}

fn rewrite_view_select_forms(source_text: &str) -> String {
    let mut output_text = String::with_capacity(source_text.len());
    for line in source_text.split_inclusive('\n') {
        let trimmed_line = line.trim_start();
        if !trimmed_line.starts_with("view ") || !trimmed_line.contains("= SELECT ") {
            output_text.push_str(line);
            continue;
        }
        let leading_ws_len = line.len().saturating_sub(trimmed_line.len());
        let line_without_newline = line.trim_end_matches('\n');
        let newline_suffix = if line_without_newline.len() < line.len() {
            "\n"
        } else {
            ""
        };
        match line_without_newline.find("= SELECT ") {
            Some(equal_index) => {
                let prefix = &line_without_newline[..equal_index + 2];
                let payload = line_without_newline[equal_index + 2..].trim();
                output_text.push_str(&line[..leading_ws_len]);
                output_text.push_str(prefix.trim_start());
                output_text.push(' ');
                output_text.push_str(&placeholder_expression_text(payload));
                output_text.push_str(newline_suffix);
            }
            None => output_text.push_str(line),
        }
    }
    output_text
}

pub fn rewrite_legacy_sql_placeholders(source_text: &str) -> String {
    rewrite_view_select_forms(&rewrite_parenthesized_sql_forms(source_text))
}

fn parse_expression_fragment(source_text: &str) -> Result<LocExp, DiagnosticPayload> {
    let mut errors = ErrorReporter::new_silent(); // Silent reporter: errors collected in Vec, not printed.
    let wrapped = format!("val {SYNTHETIC_SQL_EXPR_BINDER} = {source_text}\n"); // Wrap fragment as a val declaration for the full parser.
    let Some(file) = crate::parse::parse_ur(
        SYNTHETIC_SQL_EXPR_FILE,
        &wrapped,
        &mut errors,
        ProjectDb::default(),
    ) else {
        return Err(DiagnosticPayload::new(
            DiagnosticId::SqlCompatExprFragmentParseFailed,
            vec![format!("{errors:?}")], // Parser error details substituted into {0}.
        ));
    };
    match &file[0].node {
        Decl::Val(pattern, expression) => match &pattern.node {
            Pat::Var(name) if name == SYNTHETIC_SQL_EXPR_BINDER => Ok(expression.clone()), // Happy path: extracted expression.
            _ => Err(DiagnosticPayload::new(
                DiagnosticId::SqlCompatExprFragmentPatternMismatch,
                vec![], // No template arguments needed for this invariant failure.
            )),
        },
        _ => Err(DiagnosticPayload::new(
            DiagnosticId::SqlCompatExprFragmentDeclMismatch,
            vec![], // No template arguments needed for this invariant failure.
        )),
    }
}

fn parse_constructor_fragment(source_text: &str) -> Result<LocCon, DiagnosticPayload> {
    let mut errors = ErrorReporter::new_silent(); // Silent reporter: errors collected in Vec, not printed.
    let wrapped = format!("con {SYNTHETIC_SQL_CON_BINDER} = {source_text}\n"); // Wrap fragment as a con declaration for the full parser.
    let Some(file) = crate::parse::parse_ur(
        SYNTHETIC_SQL_CON_FILE,
        &wrapped,
        &mut errors,
        ProjectDb::default(),
    ) else {
        return Err(DiagnosticPayload::new(
            DiagnosticId::SqlCompatConFragmentParseFailed,
            vec![format!("{errors:?}")], // Parser error details substituted into {0}.
        ));
    };
    match &file[0].node {
        Decl::Con(name, _, constructor) if name == SYNTHETIC_SQL_CON_BINDER => {
            Ok(constructor.clone()) // Happy path: extracted constructor.
        }
        _ => Err(DiagnosticPayload::new(
            DiagnosticId::SqlCompatConFragmentDeclMismatch,
            vec![], // No template arguments needed for this invariant failure.
        )),
    }
}

fn basis_var_expression(name: &str, inference: Inference, span: &Span) -> LocExp {
    Located::new(
        Exp::Var(vec!["Basis".into()], name.to_string(), inference),
        span.clone(),
    )
}

fn basis_name_constructor(name: &str, span: &Span) -> LocCon {
    Located::new(Con::Name(name.to_string()), span.clone())
}

fn wildcard_type_constructor(span: &Span) -> LocCon {
    Located::new(
        Con::Wild(Box::new(Located::new(Kind::Type, span.clone()))),
        span.clone(),
    )
}

fn record_constructor(fields: Vec<(LocCon, LocCon)>, span: &Span) -> LocCon {
    Located::new(Con::Record(fields), span.clone())
}

fn record_expression(fields: Vec<(LocCon, LocExp)>, span: &Span) -> LocExp {
    Located::new(Exp::Record(fields, false), span.clone())
}

fn apply_expression(function: LocExp, argument: LocExp, span: &Span) -> LocExp {
    Located::new(
        Exp::App(Box::new(function), Box::new(argument)),
        span.clone(),
    )
}

fn constructor_apply_expression(function: LocExp, argument: LocCon, span: &Span) -> LocExp {
    Located::new(Exp::CApp(Box::new(function), argument), span.clone())
}

fn disjoint_apply_expression(expression: LocExp, span: &Span) -> LocExp {
    Located::new(Exp::DisjointApp(Box::new(expression)), span.clone())
}

fn strip_optional_trailing_comma(source_text: &str) -> &str {
    source_text.trim().trim_end_matches(',').trim_end()
}

fn parse_table_name_constructor(
    source_text: &str,
    span: &Span,
) -> Result<LocCon, DiagnosticPayload> {
    let trimmed = source_text.trim();
    if trimmed.starts_with('{') && trimmed.ends_with('}') {
        return parse_constructor_fragment(&trimmed[1..trimmed.len() - 1]);
    }
    Ok(basis_name_constructor(trimmed, span))
}

fn parse_table_name_list(source_text: &str, span: &Span) -> Result<Vec<LocCon>, DiagnosticPayload> {
    let trimmed = source_text.trim();
    let inner = if trimmed.starts_with('(') && trimmed.ends_with(')') {
        &trimmed[1..trimmed.len() - 1]
    } else {
        trimmed
    };
    split_top_level_commas(inner)
        .into_iter()
        .map(|part| parse_table_name_constructor(&part, span))
        .collect()
}

fn default_no_primary_key_expression(span: &Span) -> LocExp {
    basis_var_expression("no_primary_key", Inference::Infer, span)
}

fn default_no_constraint_expression(span: &Span) -> LocExp {
    basis_var_expression("no_constraint", Inference::Infer, span)
}

fn build_primary_key_expression(
    names: &[LocCon],
    span: &Span,
) -> Result<LocExp, DiagnosticPayload> {
    let Some(first_name) = names.first().cloned() else {
        return Err(DiagnosticPayload::new(
            DiagnosticId::SqlCompatUnsupportedPlaceholder,
            vec!["PRIMARY KEY clause is missing its column names".to_string()],
        ));
    };
    let rest_names = names
        .iter()
        .skip(1)
        .cloned()
        .map(|name| (name, wildcard_type_constructor(span)))
        .collect();
    let witness_fields = names
        .iter()
        .cloned()
        .map(|name| (name, Located::new(Exp::Wild, span.clone())))
        .collect();
    let mut expression = basis_var_expression("primary_key", Inference::TypesOnly, span);
    expression = constructor_apply_expression(expression, first_name, span);
    expression =
        constructor_apply_expression(expression, record_constructor(rest_names, span), span);
    expression = disjoint_apply_expression(expression, span);
    expression = disjoint_apply_expression(expression, span);
    Ok(apply_expression(
        expression,
        record_expression(witness_fields, span),
        span,
    ))
}

fn build_unique_constraint_expression(
    names: &[LocCon],
    span: &Span,
) -> Result<LocExp, DiagnosticPayload> {
    let Some(first_name) = names.first().cloned() else {
        return Err(DiagnosticPayload::new(
            DiagnosticId::SqlCompatUnsupportedPlaceholder,
            vec!["UNIQUE clause is missing its column names".to_string()],
        ));
    };
    let rest_names = names
        .iter()
        .skip(1)
        .cloned()
        .map(|name| (name, wildcard_type_constructor(span)))
        .collect();
    let mut expression = basis_var_expression("unique", Inference::Infer, span);
    expression = constructor_apply_expression(expression, first_name, span);
    Ok(constructor_apply_expression(
        expression,
        record_constructor(rest_names, span),
        span,
    ))
}

fn build_foreign_key_matching_expression(
    source_names: &[LocCon],
    referenced_names: &[LocCon],
    span: &Span,
) -> Result<LocExp, DiagnosticPayload> {
    if source_names.len() != referenced_names.len() {
        return Err(DiagnosticPayload::new(
            DiagnosticId::SqlCompatUnsupportedPlaceholder,
            vec![format!(
                "FOREIGN KEY column list length mismatch: {} vs {}",
                source_names.len(),
                referenced_names.len()
            )],
        ));
    }
    let mut matching = basis_var_expression("mat_nil", Inference::Infer, span);
    for (source_name, referenced_name) in source_names
        .iter()
        .cloned()
        .zip(referenced_names.iter().cloned())
        .rev()
    {
        let mut cons = basis_var_expression("mat_cons", Inference::Infer, span);
        cons = constructor_apply_expression(cons, source_name, span);
        cons = constructor_apply_expression(cons, referenced_name, span);
        matching = apply_expression(cons, matching, span);
    }
    Ok(matching)
}

fn parse_reference_table_expression(
    source_text: &str,
    span: &Span,
) -> Result<LocExp, DiagnosticPayload> {
    let trimmed = source_text.trim();
    if trimmed.starts_with("{{") && trimmed.ends_with("}}") {
        return parse_expression_fragment(&trimmed[2..trimmed.len() - 2]);
    }
    Ok(Located::new(
        Exp::Var(vec![], trimmed.to_string(), Inference::Infer),
        span.clone(),
    ))
}

fn parse_propagation_rule(source_text: &str, span: &Span) -> Result<LocExp, DiagnosticPayload> {
    match source_text.trim() {
        "NO ACTION" => Ok(basis_var_expression("no_action", Inference::Infer, span)),
        "RESTRICT" => Ok(basis_var_expression("restrict", Inference::Infer, span)),
        "CASCADE" => Ok(basis_var_expression("cascade", Inference::Infer, span)),
        "SET NULL" => Ok(basis_var_expression("set_null", Inference::Infer, span)),
        other => Err(DiagnosticPayload::new(
            DiagnosticId::SqlCompatUnsupportedPlaceholder,
            vec![format!(
                "Unsupported propagation rule in FOREIGN KEY clause: {other}"
            )],
        )),
    }
}

fn parse_foreign_key_modes(
    source_text: &str,
    span: &Span,
) -> Result<(LocExp, LocExp), DiagnosticPayload> {
    let mut on_delete = basis_var_expression("no_action", Inference::Infer, span);
    let mut on_update = basis_var_expression("no_action", Inference::Infer, span);
    let trimmed = source_text.trim();
    if trimmed.is_empty() {
        return Ok((on_delete, on_update));
    }

    let tokens: Vec<&str> = trimmed.split_whitespace().collect();
    let mut index = 0usize;
    while index < tokens.len() {
        if tokens.get(index) != Some(&"ON") {
            return Err(DiagnosticPayload::new(
                DiagnosticId::SqlCompatUnsupportedPlaceholder,
                vec![format!("Unsupported FOREIGN KEY mode syntax: {trimmed}")],
            ));
        }
        let kind = tokens.get(index + 1).copied().ok_or_else(|| {
            DiagnosticPayload::new(
                DiagnosticId::SqlCompatUnsupportedPlaceholder,
                vec![format!("Incomplete FOREIGN KEY mode syntax: {trimmed}")],
            )
        })?;
        let rule_start = index + 2;
        let rule_text = if tokens.get(rule_start) == Some(&"NO")
            && tokens.get(rule_start + 1) == Some(&"ACTION")
        {
            index += 4;
            "NO ACTION".to_string()
        } else if tokens.get(rule_start) == Some(&"SET")
            && tokens.get(rule_start + 1) == Some(&"NULL")
        {
            index += 4;
            "SET NULL".to_string()
        } else {
            let rule = tokens.get(rule_start).copied().ok_or_else(|| {
                DiagnosticPayload::new(
                    DiagnosticId::SqlCompatUnsupportedPlaceholder,
                    vec![format!("Incomplete FOREIGN KEY mode syntax: {trimmed}")],
                )
            })?;
            index += 3;
            rule.to_string()
        };
        let parsed_rule = parse_propagation_rule(&rule_text, span)?;
        match kind {
            "DELETE" => on_delete = parsed_rule,
            "UPDATE" => on_update = parsed_rule,
            _ => {
                return Err(DiagnosticPayload::new(
                    DiagnosticId::SqlCompatUnsupportedPlaceholder,
                    vec![format!(
                        "Unsupported FOREIGN KEY mode kind `{kind}` in: {trimmed}"
                    )],
                ))
            }
        }
    }

    Ok((on_delete, on_update))
}

fn build_foreign_key_constraint_expression(
    source_names: &[LocCon],
    reference_table: LocExp,
    referenced_names: &[LocCon],
    mode_text: &str,
    span: &Span,
) -> Result<LocExp, DiagnosticPayload> {
    let matching = build_foreign_key_matching_expression(source_names, referenced_names, span)?;
    let (on_delete, on_update) = parse_foreign_key_modes(mode_text, span)?;
    let propagation = record_expression(
        vec![
            (basis_name_constructor("OnDelete", span), on_delete),
            (basis_name_constructor("OnUpdate", span), on_update),
        ],
        span,
    );
    let with_matching = apply_expression(
        basis_var_expression("foreign_key", Inference::Infer, span),
        matching,
        span,
    );
    let with_table = apply_expression(with_matching, reference_table, span);
    Ok(apply_expression(with_table, propagation, span))
}

fn parse_single_constraint_expression(
    source_text: &str,
    span: &Span,
) -> Result<LocExp, DiagnosticPayload> {
    let trimmed = strip_optional_trailing_comma(source_text);
    if let Some(rest) = trimmed.strip_prefix("UNIQUE ") {
        let names = parse_table_name_list(rest, span)?;
        return build_unique_constraint_expression(&names, span);
    }
    if let Some(rest) = trimmed.strip_prefix("CHECK ") {
        let parsed_check_expression = parse_sql_value(rest, span).map_err(|inner| {
            DiagnosticPayload::new(
                DiagnosticId::SqlCompatUnsupportedPlaceholder,
                vec![format!(
                    "CHECK clause `{trimmed}` could not be parsed ({inner:?})"
                )],
            )
        })?;
        return Ok(apply_expression(
            basis_var_expression("check", Inference::Infer, span),
            parsed_check_expression,
            span,
        ));
    }
    if let Some(rest) = trimmed.strip_prefix("FOREIGN KEY ") {
        let (source_name_text, reference_text) =
            split_top_level(rest, "REFERENCES").ok_or_else(|| {
                DiagnosticPayload::new(
                    DiagnosticId::SqlCompatUnsupportedPlaceholder,
                    vec![format!(
                        "FOREIGN KEY clause is missing REFERENCES: {trimmed}"
                    )],
                )
            })?;
        let source_names = parse_table_name_list(&source_name_text, span)?;
        let open_paren_index = reference_text.find('(').ok_or_else(|| {
            DiagnosticPayload::new(
                DiagnosticId::SqlCompatUnsupportedPlaceholder,
                vec![format!(
                    "FOREIGN KEY REFERENCES clause is missing its referenced column list: {trimmed}"
                )],
            )
        })?;
        let close_paren_index = find_matching_rparen(
            &reference_text,
            reference_text.as_bytes(),
            open_paren_index,
            reference_text.len(),
        )
        .ok_or_else(|| {
            DiagnosticPayload::new(
                DiagnosticId::SqlCompatUnsupportedPlaceholder,
                vec![format!(
                    "FOREIGN KEY REFERENCES clause is missing its closing parenthesis: {trimmed}"
                )],
            )
        })?;
        let reference_table =
            parse_reference_table_expression(&reference_text[..open_paren_index], span)?;
        let referenced_names = parse_table_name_list(
            &reference_text[open_paren_index + 1..close_paren_index - 1],
            span,
        )?;
        let mode_text = reference_text[close_paren_index..].trim();
        return build_foreign_key_constraint_expression(
            &source_names,
            reference_table,
            &referenced_names,
            mode_text,
            span,
        );
    }
    if trimmed.starts_with("{{") && trimmed.ends_with("}}") {
        return parse_expression_fragment(&trimmed[2..trimmed.len() - 2]);
    }
    Err(DiagnosticPayload::new(
        DiagnosticId::SqlCompatUnsupportedPlaceholder,
        vec![format!("Unsupported table constraint clause: {trimmed}")],
    ))
}

fn wrap_named_constraint(
    constraint_name: LocCon,
    constraint_expression: LocExp,
    span: &Span,
) -> LocExp {
    let with_name = constructor_apply_expression(
        basis_var_expression("one_constraint", Inference::Infer, span),
        constraint_name,
        span,
    );
    apply_expression(with_name, constraint_expression, span)
}

fn join_constraint_expressions(left: LocExp, right: LocExp, span: &Span) -> LocExp {
    let with_left = apply_expression(
        basis_var_expression("join_constraints", Inference::Infer, span),
        left,
        span,
    );
    apply_expression(with_left, right, span)
}

fn parse_table_constraint_lines(
    constraint_lines: &[&str],
    span: &Span,
) -> Result<(LocExp, LocExp), DiagnosticPayload> {
    let mut primary_key_expression = default_no_primary_key_expression(span);
    let mut constraint_expression = default_no_constraint_expression(span);
    let mut saw_constraint = false;

    for line in constraint_lines {
        let trimmed = strip_optional_trailing_comma(line.trim_start());
        if let Some(rest) = trimmed.strip_prefix("PRIMARY KEY ") {
            primary_key_expression = if rest.starts_with("{{") && rest.ends_with("}}") {
                parse_expression_fragment(&rest[2..rest.len() - 2])?
            } else {
                build_primary_key_expression(&parse_table_name_list(rest, span)?, span)?
            };
            continue;
        }
        if let Some(rest) = trimmed.strip_prefix("CONSTRAINT ") {
            let Some(space_index) = rest.find(char::is_whitespace) else {
                return Err(DiagnosticPayload::new(
                    DiagnosticId::SqlCompatUnsupportedPlaceholder,
                    vec![format!("Malformed CONSTRAINT clause: {trimmed}")],
                ));
            };
            let constraint_name = parse_table_name_constructor(&rest[..space_index], span)?;
            let inner_expression =
                parse_single_constraint_expression(rest[space_index..].trim_start(), span)?;
            let named_constraint = wrap_named_constraint(constraint_name, inner_expression, span);
            constraint_expression = if saw_constraint {
                join_constraint_expressions(constraint_expression, named_constraint, span)
            } else {
                named_constraint
            };
            saw_constraint = true;
            continue;
        }
        return Err(DiagnosticPayload::new(
            DiagnosticId::SqlCompatUnsupportedPlaceholder,
            vec![format!("Unsupported table constraint line: {trimmed}")],
        ));
    }

    Ok((primary_key_expression, constraint_expression))
}

fn is_table_constraint_line(trimmed: &str) -> bool {
    trimmed.starts_with("PRIMARY ")
        || trimmed.starts_with("PRIMARY\t")
        || trimmed.starts_with("CONSTRAINT ")
        || trimmed.starts_with("CONSTRAINT\t")
        || trimmed.starts_with("UNIQUE ")
        || trimmed.starts_with("UNIQUE\t")
        || trimmed.starts_with("CHECK ")
        || trimmed.starts_with("CHECK\t")
}

fn repair_table_constraints_in_structure(
    source_lines: &[&str],
    structure_expression: &mut crate::source::LocStr,
) -> Result<(), DiagnosticPayload> {
    match &mut structure_expression.node {
        crate::source::Str::Const(declarations) => {
            repair_table_constraints_in_file(source_lines, declarations)
        }
        crate::source::Str::Proj(inner, _) => {
            repair_table_constraints_in_structure(source_lines, inner)
        }
        crate::source::Str::Fun(_, _, _, body) => {
            repair_table_constraints_in_structure(source_lines, body)
        }
        crate::source::Str::App(left, right) => {
            repair_table_constraints_in_structure(source_lines, left)?;
            repair_table_constraints_in_structure(source_lines, right)
        }
        crate::source::Str::Var(_) => Ok(()),
    }
}

pub fn repair_table_constraints_in_file(
    source_lines: &[&str],
    file: &mut File,
) -> Result<(), DiagnosticPayload> {
    for declaration in file {
        match &mut declaration.node {
            Decl::Table(_, _, primary_key_expression, constraint_expression) => {
                let first_constraint_line = declaration.span.last.line as usize;
                let collected_lines: Vec<&str> = source_lines
                    .iter()
                    .skip(first_constraint_line)
                    .take_while(|line| is_table_constraint_line(line.trim_start()))
                    .copied()
                    .collect();
                let (parsed_primary_key, parsed_constraints) =
                    parse_table_constraint_lines(&collected_lines, &declaration.span)?;
                *primary_key_expression = parsed_primary_key;
                *constraint_expression = parsed_constraints;
            }
            Decl::Export(structure_expression) => {
                repair_table_constraints_in_structure(source_lines, structure_expression)?
            }
            Decl::Str(_, _, _, structure_expression, _) | Decl::OpenStr(structure_expression) => {
                repair_table_constraints_in_structure(source_lines, structure_expression)?
            }
            Decl::Val(_, _)
            | Decl::ValRec(_)
            | Decl::View(_, _)
            | Decl::Policy(_)
            | Decl::Con(_, _, _)
            | Decl::Datatype(_)
            | Decl::DatatypeImp(_, _, _)
            | Decl::Sgn(_, _)
            | Decl::FfiStr(_, _, _)
            | Decl::Open(_, _)
            | Decl::Constraint(_, _)
            | Decl::OpenConstraints(_, _)
            | Decl::Sequence(_)
            | Decl::Index(_, _, _)
            | Decl::Task(_, _)
            | Decl::Database(_)
            | Decl::Cookie(_, _)
            | Decl::Style(_)
            | Decl::OnError(_, _, _)
            | Decl::Ffi(_, _, _) => {}
        }
    }
    Ok(())
}

fn trim_wrapping_parens(source_text: &str) -> &str {
    let trimmed = source_text.trim();
    if !(trimmed.starts_with('(') && trimmed.ends_with(')')) {
        return trimmed;
    }
    let bytes = trimmed.as_bytes();
    let byte_length = bytes.len();
    let Some(close_index) = find_matching_rparen(trimmed, bytes, 0, byte_length) else {
        return trimmed;
    };
    if close_index == byte_length {
        return trim_wrapping_parens(&trimmed[1..byte_length - 1]);
    }
    trimmed
}

fn is_simple_sql_atom(source_text: &str) -> bool {
    !source_text.chars().any(|ch| {
        ch.is_whitespace()
            || matches!(
                ch,
                '(' | ')' | '\'' | '"' | '+' | '-' | '*' | '/' | '=' | '>' | '<'
            )
    })
}

fn split_top_level(source_text: &str, separator: &str) -> Option<(String, String)> {
    let trimmed = source_text.trim();
    let bytes = trimmed.as_bytes();
    let byte_length = bytes.len();
    let mut index = 0usize;
    let mut paren_depth = 0i32;
    let mut brace_depth = 0i32;
    let scan_budget = byte_length.saturating_mul(2).saturating_add(1);
    for _ in 0..scan_budget {
        if index >= byte_length {
            break;
        }
        match (
            index + 1 < byte_length,
            bytes.get(index).copied(),
            bytes.get(index + 1).copied(),
        ) {
            (true, Some(b'('), Some(b'*')) => {
                index = skip_ml_comment_bytes(bytes, index + 2, byte_length);
            }
            (_, Some(b'"'), _) => {
                index = skip_string_bytes(bytes, index + 1, byte_length);
            }
            (_, Some(b'('), _) => {
                paren_depth += 1;
                index += 1;
            }
            (_, Some(b')'), _) => {
                paren_depth -= 1;
                index += 1;
            }
            (_, Some(b'{'), _) => {
                brace_depth += 1;
                index += 1;
            }
            (_, Some(b'}'), _) => {
                brace_depth -= 1;
                index += 1;
            }
            _ if paren_depth == 0
                && brace_depth == 0
                && starts_with_keyword(bytes, index, separator.as_bytes()) =>
            {
                let left = trimmed[..index].trim().to_string();
                let right = trimmed[index + separator.len()..].trim().to_string();
                return Some((left, right));
            }
            _ => {
                let next_char = trimmed[index..].chars().next().unwrap_or('\0');
                index += next_char.len_utf8();
            }
        }
    }
    None
}

fn split_top_level_commas(source_text: &str) -> Vec<String> {
    let trimmed = source_text.trim();
    let bytes = trimmed.as_bytes();
    let byte_length = bytes.len();
    let mut parts: Vec<String> = Vec::new();
    let mut part_start = 0usize;
    let mut index = 0usize;
    let mut paren_depth = 0i32;
    let mut brace_depth = 0i32;
    let scan_budget = byte_length.saturating_mul(2).saturating_add(1);
    for _ in 0..scan_budget {
        if index >= byte_length {
            break;
        }
        match (
            index + 1 < byte_length,
            bytes.get(index).copied(),
            bytes.get(index + 1).copied(),
        ) {
            (true, Some(b'('), Some(b'*')) => {
                index = skip_ml_comment_bytes(bytes, index + 2, byte_length);
            }
            (_, Some(b'"'), _) => {
                index = skip_string_bytes(bytes, index + 1, byte_length);
            }
            (_, Some(b'('), _) => {
                paren_depth += 1;
                index += 1;
            }
            (_, Some(b')'), _) => {
                paren_depth -= 1;
                index += 1;
            }
            (_, Some(b'{'), _) => {
                brace_depth += 1;
                index += 1;
            }
            (_, Some(b'}'), _) => {
                brace_depth -= 1;
                index += 1;
            }
            (_, Some(b','), _) if paren_depth == 0 && brace_depth == 0 => {
                parts.push(trimmed[part_start..index].trim().to_string());
                index += 1;
                part_start = index;
            }
            _ => {
                let next_char = trimmed[index..].chars().next().unwrap_or('\0');
                index += next_char.len_utf8();
            }
        }
    }
    parts.push(trimmed[part_start..].trim().to_string());
    parts
}

fn parse_sql_value(source_text: &str, span: &Span) -> Result<LocExp, DiagnosticPayload> {
    let trimmed = trim_wrapping_parens(source_text);
    if let Some((left, right)) = split_top_level(trimmed, "OR") {
        let left_expression = parse_sql_value(&left, span)?;
        let right_expression = parse_sql_value(&right, span)?;
        return Ok(Located::new(
            crate::parse::grammar_helpers::sql_binary_expression(
                "or",
                left_expression,
                right_expression,
                span,
            )
            .node,
            span.clone(),
        ));
    }
    if let Some((left, right)) = split_top_level(trimmed, "AND") {
        let left_expression = parse_sql_value(&left, span)?;
        let right_expression = parse_sql_value(&right, span)?;
        return Ok(Located::new(
            crate::parse::grammar_helpers::sql_binary_expression(
                "and",
                left_expression,
                right_expression,
                span,
            )
            .node,
            span.clone(),
        ));
    }
    if let Some((left, right)) = split_top_level(trimmed, "<>") {
        let left_expression = parse_sql_value(&left, span)?;
        let right_expression = parse_sql_value(&right, span)?;
        return Ok(crate::parse::grammar_helpers::sql_binary_expression(
            "ne",
            left_expression,
            right_expression,
            span,
        ));
    }
    if let Some((left, right)) = split_top_level(trimmed, ">=") {
        let left_expression = parse_sql_value(&left, span)?;
        let right_expression = parse_sql_value(&right, span)?;
        return Ok(crate::parse::grammar_helpers::sql_binary_expression(
            "ge",
            left_expression,
            right_expression,
            span,
        ));
    }
    if let Some((left, right)) = split_top_level(trimmed, "=") {
        let left_expression = parse_sql_value(&left, span)?;
        let right_expression = parse_sql_value(&right, span)?;
        return Ok(crate::parse::grammar_helpers::sql_binary_expression(
            "eq",
            left_expression,
            right_expression,
            span,
        ));
    }
    if let Some((left, right)) = split_top_level(trimmed, "<=") {
        let left_expression = parse_sql_value(&left, span)?;
        let right_expression = parse_sql_value(&right, span)?;
        return Ok(crate::parse::grammar_helpers::sql_binary_expression(
            "le",
            left_expression,
            right_expression,
            span,
        ));
    }
    if let Some((left, right)) = split_top_level(trimmed, ">") {
        let left_expression = parse_sql_value(&left, span)?;
        let right_expression = parse_sql_value(&right, span)?;
        return Ok(crate::parse::grammar_helpers::sql_binary_expression(
            "gt",
            left_expression,
            right_expression,
            span,
        ));
    }
    if let Some((left, right)) = split_top_level(trimmed, "<") {
        let left_expression = parse_sql_value(&left, span)?;
        let right_expression = parse_sql_value(&right, span)?;
        return Ok(crate::parse::grammar_helpers::sql_binary_expression(
            "lt",
            left_expression,
            right_expression,
            span,
        ));
    }
    if let Some(prefix) = trimmed.strip_suffix("IS NULL") {
        let value_expression = parse_sql_value(prefix.trim(), span)?;
        return Ok(crate::parse::grammar_helpers::sql_is_null_expression(
            value_expression,
            span,
        ));
    }
    if trimmed == "CURRENT_TIMESTAMP" {
        return Ok(crate::parse::grammar_helpers::sql_current_timestamp_expression(span));
    }
    if trimmed == "COUNT(sql_star)"
        || trimmed == "COUNT( sql_star )"
        || trimmed == "COUNT(*)"
        || trimmed == "COUNT( * )"
    {
        return Ok(crate::parse::grammar_helpers::sql_count_all_expression(
            span,
        ));
    }
    if let Ok(integer_value) = trimmed.parse::<i64>() {
        return Ok(crate::parse::grammar_helpers::sql_integer_expression(
            integer_value,
            span,
        ));
    }
    if trimmed.starts_with("{[") && trimmed.ends_with("]}") {
        let inner_expression = parse_expression_fragment(&trimmed[2..trimmed.len() - 2])?;
        return Ok(crate::parse::grammar_helpers::sql_inject_expression(
            inner_expression,
            span,
        ));
    }
    if trimmed.starts_with('{') && trimmed.ends_with('}') {
        return parse_expression_fragment(&trimmed[1..trimmed.len() - 1]);
    }
    if is_simple_sql_atom(trimmed) {
        if let Some((table_name_text, field_text)) = trimmed.split_once(".{{") {
            let con_text = field_text
                .strip_suffix("}}")
                .ok_or_else(|| {
                    DiagnosticPayload::new(
                        DiagnosticId::SqlCompatDynamicFieldMissingBraces,
                        vec![trimmed.to_string()], // Offending field text substituted into {0}.
                    )
                })?
                .trim();
            let field_constructor = parse_constructor_fragment(con_text)?;
            return Ok(sql_dynamic_field_expression(
                table_name_text.trim().to_string(),
                field_constructor,
                span,
            ));
        }
        if let Some((table_name_text, field_text)) = trimmed.split_once(".{") {
            let con_text = field_text
                .strip_suffix('}')
                .ok_or_else(|| {
                    DiagnosticPayload::new(
                        DiagnosticId::SqlCompatFieldMissingBrace,
                        vec![trimmed.to_string()], // Offending field text substituted into {0}.
                    )
                })?
                .trim();
            let field_constructor = parse_constructor_fragment(con_text)?;
            return Ok(sql_dynamic_field_expression(
                table_name_text.trim().to_string(),
                field_constructor,
                span,
            ));
        }
        if let Some(dot_index) = trimmed.find('.') {
            let table_name = trimmed[..dot_index].trim().to_string();
            let field_name = trimmed[dot_index + 1..].trim().to_string();
            return Ok(sql_field_expression(table_name, field_name, span));
        }
        if trimmed
            .chars()
            .next()
            .map(|first_char| first_char.is_ascii_alphabetic())
            .unwrap_or(false)
        {
            return Ok(sql_default_table_field_expression(
                trimmed.to_string(),
                span,
            ));
        }
    }
    if let Ok(expression) = parse_expression_fragment(trimmed) {
        return Ok(expression);
    }
    Err(DiagnosticPayload::new(
        DiagnosticId::SqlCompatUnsupportedExpression,
        vec![trimmed.to_string()], // Unsupported expression text substituted into {0}.
    ))
}

fn parse_select_spec(source_text: &str, span: &Span) -> Result<SqlSelectSpec, DiagnosticPayload> {
    let trimmed = source_text.trim();
    if trimmed == "*" {
        return Ok(SqlSelectSpec::Star);
    }
    let mut items = Vec::new();
    for item_text in split_top_level_commas(trimmed) {
        if let Some((left, alias_name)) = split_top_level(&item_text, "AS") {
            let expression = parse_sql_value(&left, span)?;
            items.push(sql_select_expression_item(alias_name, expression));
            continue;
        }
        if let Some((table_name_text, field_text)) = item_text.split_once(".{{") {
            let con_text = field_text
                .strip_suffix("}}")
                .ok_or_else(|| {
                    DiagnosticPayload::new(
                        DiagnosticId::SqlCompatDynamicSelectFieldMissingBraces,
                        vec![item_text.clone()], // Offending SELECT item text substituted into {0}.
                    )
                })?
                .trim();
            let field_constructor = parse_constructor_fragment(con_text)?;
            items.push(sql_select_dynamic_fields_item(
                table_name_text.trim().to_string(),
                field_constructor,
            ));
            continue;
        }
        if let Some(dot_index) = item_text.find('.') {
            let table_name = item_text[..dot_index].trim().to_string();
            let field_name = item_text[dot_index + 1..].trim().to_string();
            items.push(sql_select_single_field_item(table_name, field_name, span));
            continue;
        }
        return Err(DiagnosticPayload::new(
            DiagnosticId::SqlCompatUnsupportedSelectItem,
            vec![item_text], // Unsupported SELECT item text substituted into {0}.
        ));
    }
    Ok(SqlSelectSpec::Items(items))
}

fn parse_from_clause(
    source_text: &str,
    span: &Span,
) -> Result<(Vec<String>, LocExp), DiagnosticPayload> {
    if let Some((left, right)) = split_top_level(source_text, "LEFT JOIN") {
        let left_from = parse_from_clause(&left, span)?;
        let (right_source, on_clause) = split_top_level(&right, "ON").ok_or_else(|| {
            DiagnosticPayload::new(DiagnosticId::SqlCompatLeftJoinMissingOn, vec![])
        })?; // No template arguments for this structural error.
        let right_from = parse_from_clause(&right_source, span)?;
        let predicate = parse_sql_value(&on_clause, span)?;
        return Ok(sql_join_expression(
            SqlJoinKind::Left,
            left_from,
            right_from,
            predicate,
            span,
        ));
    }
    if let Some((left, right)) = split_top_level(source_text, "JOIN") {
        let left_from = parse_from_clause(&left, span)?;
        let (right_source, on_clause) = split_top_level(&right, "ON")
            .ok_or_else(|| DiagnosticPayload::new(DiagnosticId::SqlCompatJoinMissingOn, vec![]))?; // No template arguments for this structural error.
        let right_from = parse_from_clause(&right_source, span)?;
        let predicate = parse_sql_value(&on_clause, span)?;
        return Ok(sql_join_expression(
            SqlJoinKind::Inner,
            left_from,
            right_from,
            predicate,
            span,
        ));
    }
    if let Some((left, right)) = split_top_level(source_text, ",") {
        let left_from = parse_from_clause(&left, span)?;
        let right_from = parse_from_clause(&right, span)?;
        return Ok(crate::parse::grammar_helpers::sql_from_comma_expression(
            left_from, right_from, span,
        ));
    }
    let trimmed = source_text.trim();
    let alias_parse = split_top_level(trimmed, "AS");
    match alias_parse {
        Some((table_name, alias_name)) => Ok(sql_table_reference_with_alias(
            table_name,
            Some(alias_name),
            span,
        )),
        None => Ok(sql_table_reference_with_alias(
            trimmed.to_string(),
            None,
            span,
        )),
    }
}

fn parse_select_payload(source_text: &str, span: &Span) -> Result<Exp, DiagnosticPayload> {
    let (select_text, from_and_where) = split_top_level(source_text, "FROM")
        .ok_or_else(|| DiagnosticPayload::new(DiagnosticId::SqlCompatSelectMissingFrom, vec![]))?; // No template arguments for this structural error.
    let (from_text, where_text) = match split_top_level(&from_and_where, "WHERE") {
        Some((from_clause, where_clause)) => (from_clause, Some(where_clause)),
        None => (from_and_where, None),
    };
    let select_spec = parse_select_spec(select_text.trim_start_matches("SELECT").trim(), span)?;
    let from_clause = parse_from_clause(&from_text, span)?;
    let where_expression = match where_text {
        Some(predicate_text) => parse_sql_value(&predicate_text, span)?,
        None => sql_true_expression(span),
    };
    Ok(desugar_sql_select_query(
        select_spec,
        from_clause.0,
        from_clause.1,
        where_expression,
        span,
    ))
}

fn parse_insert_payload(source_text: &str, span: &Span) -> Result<Exp, DiagnosticPayload> {
    let after_into = source_text
        .trim_start_matches("INSERT")
        .trim()
        .strip_prefix("INTO")
        .ok_or_else(|| DiagnosticPayload::new(DiagnosticId::SqlCompatInsertMissingInto, vec![]))? // No template arguments for this structural error.
        .trim();
    let open_fields = after_into.find('(').ok_or_else(|| {
        DiagnosticPayload::new(DiagnosticId::SqlCompatInsertMissingFieldList, vec![])
    })?; // No template arguments for this structural error.
    let table_name = after_into[..open_fields].trim().to_string();
    let close_fields = find_matching_rparen(
        after_into,
        after_into.as_bytes(),
        open_fields,
        after_into.len(),
    )
    .ok_or_else(|| {
        DiagnosticPayload::new(DiagnosticId::SqlCompatInsertFieldListMissingParen, vec![])
    })?; // No template arguments for this structural error.
    let field_text = &after_into[open_fields + 1..close_fields - 1];
    let after_fields = after_into[close_fields..].trim();
    let values_payload = after_fields
        .strip_prefix("VALUES")
        .ok_or_else(|| DiagnosticPayload::new(DiagnosticId::SqlCompatInsertMissingValues, vec![]))? // No template arguments for this structural error.
        .trim();
    if !values_payload.starts_with('(') {
        return Err(DiagnosticPayload::new(
            DiagnosticId::SqlCompatInsertValuesMissingOpenParen,
            vec![], // No template arguments for this structural error.
        ));
    }
    let close_values = find_matching_rparen(
        values_payload,
        values_payload.as_bytes(),
        0,
        values_payload.len(),
    )
    .ok_or_else(|| {
        DiagnosticPayload::new(DiagnosticId::SqlCompatInsertValuesMissingCloseParen, vec![])
    })?; // No template arguments for this structural error.
    let value_text = &values_payload[1..close_values - 1];
    let fields = split_top_level_commas(field_text);
    let mut values = Vec::new();
    for value_part in split_top_level_commas(value_text) {
        values.push(parse_sql_value(&value_part, span)?);
    }
    Ok(desugar_sql_insert_expression(
        table_name, fields, values, span,
    ))
}

fn parse_delete_payload(source_text: &str, span: &Span) -> Result<Exp, DiagnosticPayload> {
    let after_delete = source_text
        .trim_start_matches("DELETE")
        .trim()
        .strip_prefix("FROM")
        .ok_or_else(|| DiagnosticPayload::new(DiagnosticId::SqlCompatDeleteMissingFrom, vec![]))? // No template arguments for this structural error.
        .trim();
    let (table_name, predicate_text) = split_top_level(after_delete, "WHERE")
        .ok_or_else(|| DiagnosticPayload::new(DiagnosticId::SqlCompatDeleteMissingWhere, vec![]))?; // No template arguments for this structural error.
    let predicate = parse_sql_value(&predicate_text, span)?;
    Ok(desugar_sql_delete_expression(table_name, predicate, span))
}

fn parse_update_payload(source_text: &str, span: &Span) -> Result<Exp, DiagnosticPayload> {
    let after_update = source_text.trim_start_matches("UPDATE").trim();
    let (table_name, set_and_where) = split_top_level(after_update, "SET")
        .ok_or_else(|| DiagnosticPayload::new(DiagnosticId::SqlCompatUpdateMissingSet, vec![]))?; // No template arguments for this structural error.
    let (assignment_text, predicate_text) = split_top_level(&set_and_where, "WHERE")
        .ok_or_else(|| DiagnosticPayload::new(DiagnosticId::SqlCompatUpdateMissingWhere, vec![]))?; // No template arguments for this structural error.
    let mut assignments = Vec::new();
    for assignment in split_top_level_commas(&assignment_text) {
        let (field_name, value_text) = split_top_level(&assignment, "=").ok_or_else(|| {
            DiagnosticPayload::new(DiagnosticId::SqlCompatUpdateAssignmentMissingEquals, vec![])
        })?; // No template arguments for this structural error.
        assignments.push((field_name, parse_sql_value(&value_text, span)?));
    }
    let predicate = parse_sql_value(&predicate_text, span)?;
    Ok(desugar_sql_update_expression(
        table_name,
        assignments,
        predicate,
        span,
    ))
}

fn parse_sql_payload(payload: &str, span: &Span) -> Result<Exp, DiagnosticPayload> {
    let trimmed = payload.trim();
    if trimmed.starts_with("SELECT ") {
        return parse_select_payload(trimmed, span);
    }
    if trimmed.starts_with("INSERT ") {
        return parse_insert_payload(trimmed, span);
    }
    if trimmed.starts_with("DELETE ") {
        return parse_delete_payload(trimmed, span);
    }
    if trimmed.starts_with("UPDATE ") {
        return parse_update_payload(trimmed, span);
    }
    if let Some(where_body) = trimmed.strip_prefix("WHERE") {
        return Ok(parse_sql_value(where_body.trim(), span)?.node);
    }
    if let Some(sql_body) = trimmed.strip_prefix("SQL") {
        return Ok(parse_sql_value(sql_body.trim(), span)?.node);
    }
    Err(DiagnosticPayload::new(
        DiagnosticId::SqlCompatUnsupportedPlaceholder,
        vec![trimmed.to_string()], // Unsupported placeholder text substituted into {0}.
    ))
}

fn decode_sql_placeholder(expression: &Exp) -> Option<(String, Span)> {
    match expression {
        Exp::App(function_expression, argument_expression) => {
            match (&function_expression.node, &argument_expression.node) {
                (
                    Exp::Var(module_path, function_name, Inference::Infer),
                    Exp::Prim(Prim::String(StringMode::Normal, payload)),
                ) if module_path.is_empty() && function_name == SQL_PLACEHOLDER_NAME => {
                    Some((payload.clone(), argument_expression.span.clone()))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn repair_expression(expression: &mut LocExp) -> Result<(), DiagnosticPayload> {
    match &mut expression.node {
        Exp::Annot(inner, _) => repair_expression(inner)?,
        Exp::App(function_expression, argument_expression) => {
            repair_expression(function_expression)?;
            repair_expression(argument_expression)?;
        }
        Exp::Abs(_, _, body) => repair_expression(body)?,
        Exp::CApp(inner, _) => repair_expression(inner)?,
        Exp::CAbs(_, _, _, body) => repair_expression(body)?,
        Exp::Disjoint(_, _, body) => repair_expression(body)?,
        Exp::DisjointApp(inner) => repair_expression(inner)?,
        Exp::KAbs(_, body) => repair_expression(body)?,
        Exp::Record(fields, _) => {
            for (_, field_expression) in fields {
                repair_expression(field_expression)?;
            }
        }
        Exp::Field(inner, _) | Exp::Cut(inner, _) | Exp::CutMulti(inner, _) => {
            repair_expression(inner)?
        }
        Exp::Concat(left, right) | Exp::Infix(_, left, right) => {
            repair_expression(left)?;
            repair_expression(right)?;
        }
        Exp::Case(scrutinee, branches) => {
            repair_expression(scrutinee)?;
            for (_, branch_expression) in branches {
                repair_expression(branch_expression)?;
            }
        }
        Exp::Let(declarations, body) => {
            for declaration in declarations {
                match &mut declaration.node {
                    crate::source::EDecl::Val(_, bound_expression) => {
                        repair_expression(bound_expression)?
                    }
                    crate::source::EDecl::ValRec(bindings) => {
                        for (_, _, bound_expression) in bindings {
                            repair_expression(bound_expression)?;
                        }
                    }
                }
            }
            repair_expression(body)?;
        }
        Exp::Prim(_) | Exp::Var(_, _, _) | Exp::Wild | Exp::Hole => {}
    }
    if let Some((payload, span)) = decode_sql_placeholder(&expression.node) {
        expression.node = parse_sql_payload(&payload, &span)?;
    }
    Ok(())
}

pub fn repair_sql_placeholders_in_file(file: &mut File) -> Result<(), DiagnosticPayload> {
    for declaration in file {
        match &mut declaration.node {
            Decl::Val(_, expression) | Decl::View(_, expression) | Decl::Policy(expression) => {
                repair_expression(expression)?;
            }
            Decl::ValRec(bindings) => {
                for (_, _, expression) in bindings {
                    repair_expression(expression)?;
                }
            }
            Decl::Table(_, _, first_expression, second_expression) => {
                repair_expression(first_expression)?;
                repair_expression(second_expression)?;
            }
            Decl::Index(first_expression, second_expression, _)
            | Decl::Task(first_expression, second_expression) => {
                repair_expression(first_expression)?;
                repair_expression(second_expression)?;
            }
            Decl::Export(structure_expression) => repair_structure(structure_expression)?,
            Decl::Str(_, _, _, structure_expression, _) => repair_structure(structure_expression)?,
            Decl::OpenStr(structure_expression) => repair_structure(structure_expression)?,
            Decl::Con(_, _, _)
            | Decl::Datatype(_)
            | Decl::DatatypeImp(_, _, _)
            | Decl::Sgn(_, _)
            | Decl::FfiStr(_, _, _)
            | Decl::Open(_, _)
            | Decl::Constraint(_, _)
            | Decl::OpenConstraints(_, _)
            | Decl::Sequence(_)
            | Decl::Database(_)
            | Decl::Cookie(_, _)
            | Decl::Style(_)
            | Decl::OnError(_, _, _)
            | Decl::Ffi(_, _, _) => {}
        }
    }
    Ok(())
}

fn repair_structure(
    structure_expression: &mut crate::source::LocStr,
) -> Result<(), DiagnosticPayload> {
    match &mut structure_expression.node {
        crate::source::Str::Const(declarations) => repair_sql_placeholders_in_file(declarations),
        crate::source::Str::Proj(inner, _) => repair_structure(inner),
        crate::source::Str::Fun(_, _, _, body) => repair_structure(body),
        crate::source::Str::App(left, right) => {
            repair_structure(left)?;
            repair_structure(right)
        }
        crate::source::Str::Var(_) => Ok(()),
    }
}
