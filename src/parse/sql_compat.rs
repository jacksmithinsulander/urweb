use crate::db::ProjectDb;
use crate::error_types::{ErrorReporter, Located, Span};
use crate::parse::grammar_helpers::{
    desugar_sql_delete_expression, desugar_sql_insert_expression, desugar_sql_select_query,
    desugar_sql_update_expression, sql_default_table_field_expression,
    sql_dynamic_field_expression, sql_field_expression, sql_join_expression,
    sql_select_dynamic_fields_item, sql_select_expression_item, sql_select_single_field_item,
    sql_table_reference_with_alias, sql_true_expression, SqlJoinKind, SqlSelectSpec,
};
use crate::primitives::{Prim, StringMode};
use crate::source::{Decl, Exp, File, Inference, LocCon, LocExp, Pat};

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
                match (is_sql_form, find_matching_rparen(source_text, bytes, index, byte_length)) {
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

fn parse_expression_fragment(source_text: &str) -> Result<LocExp, String> {
    let mut errors = ErrorReporter::new_silent();
    let wrapped = format!("val {SYNTHETIC_SQL_EXPR_BINDER} = {source_text}\n");
    let Some(file) = crate::parse::parse_ur(
        SYNTHETIC_SQL_EXPR_FILE,
        &wrapped,
        &mut errors,
        ProjectDb::default(),
    ) else {
        return Err(format!("expression fragment parse failed: {errors:?}"));
    };
    match &file[0].node {
        Decl::Val(pattern, expression) => match &pattern.node {
            Pat::Var(name) if name == SYNTHETIC_SQL_EXPR_BINDER => Ok(expression.clone()),
            _ => Err("expression fragment wrapper pattern mismatch".to_string()),
        },
        _ => Err("expression fragment wrapper declaration mismatch".to_string()),
    }
}

fn parse_constructor_fragment(source_text: &str) -> Result<LocCon, String> {
    let mut errors = ErrorReporter::new_silent();
    let wrapped = format!("con {SYNTHETIC_SQL_CON_BINDER} = {source_text}\n");
    let Some(file) = crate::parse::parse_ur(
        SYNTHETIC_SQL_CON_FILE,
        &wrapped,
        &mut errors,
        ProjectDb::default(),
    ) else {
        return Err(format!("constructor fragment parse failed: {errors:?}"));
    };
    match &file[0].node {
        Decl::Con(name, _, constructor) if name == SYNTHETIC_SQL_CON_BINDER => Ok(constructor.clone()),
        _ => Err("constructor fragment wrapper declaration mismatch".to_string()),
    }
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
            || matches!(ch, '(' | ')' | '\'' | '"' | '+' | '-' | '*' | '/' | '=' | '>' | '<')
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
            _ if paren_depth == 0 && brace_depth == 0 && starts_with_keyword(bytes, index, separator.as_bytes()) => {
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

fn parse_sql_value(source_text: &str, span: &Span) -> Result<LocExp, String> {
    let trimmed = trim_wrapping_parens(source_text);
    if let Some((left, right)) = split_top_level(trimmed, "OR") {
        let left_expression = parse_sql_value(&left, span)?;
        let right_expression = parse_sql_value(&right, span)?;
        return Ok(Located::new(
            crate::parse::grammar_helpers::sql_binary_expression("or", left_expression, right_expression, span).node,
            span.clone(),
        ));
    }
    if let Some((left, right)) = split_top_level(trimmed, "AND") {
        let left_expression = parse_sql_value(&left, span)?;
        let right_expression = parse_sql_value(&right, span)?;
        return Ok(Located::new(
            crate::parse::grammar_helpers::sql_binary_expression("and", left_expression, right_expression, span).node,
            span.clone(),
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
    if let Some(prefix) = trimmed.strip_suffix("IS NULL") {
        let value_expression = parse_sql_value(prefix.trim(), span)?;
        return Ok(crate::parse::grammar_helpers::sql_is_null_expression(
            value_expression,
            span,
        ));
    }
    if trimmed == "CURRENT_TIMESTAMP" {
        return Ok(crate::parse::grammar_helpers::sql_current_timestamp_expression(
            span,
        ));
    }
    if trimmed == "COUNT(sql_star)" || trimmed == "COUNT( sql_star )" || trimmed == "COUNT(*)" || trimmed == "COUNT( * )" {
        return Ok(crate::parse::grammar_helpers::sql_count_all_expression(span));
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
                .ok_or_else(|| format!("dynamic SQL field missing closing braces: {trimmed}"))?
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
                .ok_or_else(|| format!("SQL field missing closing brace: {trimmed}"))?
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
            return Ok(sql_default_table_field_expression(trimmed.to_string(), span));
        }
    }
    if let Ok(expression) = parse_expression_fragment(trimmed) {
        return Ok(expression);
    }
    Err(format!("unsupported SQL expression: {trimmed}"))
}

fn parse_select_spec(source_text: &str, span: &Span) -> Result<SqlSelectSpec, String> {
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
                .ok_or_else(|| format!("dynamic SELECT field missing closing braces: {item_text}"))?
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
        return Err(format!("unsupported select item: {item_text}"));
    }
    Ok(SqlSelectSpec::Items(items))
}

fn parse_from_clause(source_text: &str, span: &Span) -> Result<(Vec<String>, LocExp), String> {
    if let Some((left, right)) = split_top_level(source_text, "LEFT JOIN") {
        let left_from = parse_from_clause(&left, span)?;
        let (right_source, on_clause) = split_top_level(&right, "ON")
            .ok_or_else(|| "LEFT JOIN missing ON clause".to_string())?;
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
        let (right_source, on_clause) =
            split_top_level(&right, "ON").ok_or_else(|| "JOIN missing ON clause".to_string())?;
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
        Some((table_name, alias_name)) => {
            Ok(sql_table_reference_with_alias(table_name, Some(alias_name), span))
        }
        None => Ok(sql_table_reference_with_alias(
            trimmed.to_string(),
            None,
            span,
        )),
    }
}

fn parse_select_payload(source_text: &str, span: &Span) -> Result<Exp, String> {
    let (select_text, from_and_where) =
        split_top_level(source_text, "FROM").ok_or_else(|| "SELECT missing FROM".to_string())?;
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

fn parse_insert_payload(source_text: &str, span: &Span) -> Result<Exp, String> {
    let after_into = source_text
        .trim_start_matches("INSERT")
        .trim()
        .strip_prefix("INTO")
        .ok_or_else(|| "INSERT missing INTO".to_string())?
        .trim();
    let open_fields = after_into
        .find('(')
        .ok_or_else(|| "INSERT missing field list".to_string())?;
    let table_name = after_into[..open_fields].trim().to_string();
    let close_fields = find_matching_rparen(
        after_into,
        after_into.as_bytes(),
        open_fields,
        after_into.len(),
    )
    .ok_or_else(|| "INSERT field list missing closing paren".to_string())?;
    let field_text = &after_into[open_fields + 1..close_fields - 1];
    let after_fields = after_into[close_fields..].trim();
    let values_payload = after_fields
        .strip_prefix("VALUES")
        .ok_or_else(|| "INSERT missing VALUES".to_string())?
        .trim();
    if !values_payload.starts_with('(') {
        return Err("INSERT values missing opening paren".to_string());
    }
    let close_values = find_matching_rparen(
        values_payload,
        values_payload.as_bytes(),
        0,
        values_payload.len(),
    )
    .ok_or_else(|| "INSERT values missing closing paren".to_string())?;
    let value_text = &values_payload[1..close_values - 1];
    let fields = split_top_level_commas(field_text);
    let mut values = Vec::new();
    for value_part in split_top_level_commas(value_text) {
        values.push(parse_sql_value(&value_part, span)?);
    }
    Ok(desugar_sql_insert_expression(table_name, fields, values, span))
}

fn parse_delete_payload(source_text: &str, span: &Span) -> Result<Exp, String> {
    let after_delete = source_text
        .trim_start_matches("DELETE")
        .trim()
        .strip_prefix("FROM")
        .ok_or_else(|| "DELETE missing FROM".to_string())?
        .trim();
    let (table_name, predicate_text) =
        split_top_level(after_delete, "WHERE").ok_or_else(|| "DELETE missing WHERE".to_string())?;
    let predicate = parse_sql_value(&predicate_text, span)?;
    Ok(desugar_sql_delete_expression(table_name, predicate, span))
}

fn parse_update_payload(source_text: &str, span: &Span) -> Result<Exp, String> {
    let after_update = source_text.trim_start_matches("UPDATE").trim();
    let (table_name, set_and_where) =
        split_top_level(after_update, "SET").ok_or_else(|| "UPDATE missing SET".to_string())?;
    let (assignment_text, predicate_text) = split_top_level(&set_and_where, "WHERE")
        .ok_or_else(|| "UPDATE missing WHERE".to_string())?;
    let mut assignments = Vec::new();
    for assignment in split_top_level_commas(&assignment_text) {
        let (field_name, value_text) = split_top_level(&assignment, "=")
            .ok_or_else(|| "UPDATE assignment missing =".to_string())?;
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

fn parse_sql_payload(payload: &str, span: &Span) -> Result<Exp, String> {
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
    Err(format!("unsupported SQL placeholder payload: {trimmed}"))
}

fn decode_sql_placeholder(expression: &Exp) -> Option<(String, Span)> {
    match expression {
        Exp::App(function_expression, argument_expression) => match (&function_expression.node, &argument_expression.node) {
            (Exp::Var(module_path, function_name, Inference::Infer), Exp::Prim(Prim::String(StringMode::Normal, payload)))
                if module_path.is_empty() && function_name == SQL_PLACEHOLDER_NAME =>
            {
                Some((payload.clone(), argument_expression.span.clone()))
            }
            _ => None,
        },
        _ => None,
    }
}

fn repair_expression(expression: &mut LocExp) -> Result<(), String> {
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
        Exp::Field(inner, _)
        | Exp::Cut(inner, _)
        | Exp::CutMulti(inner, _) => repair_expression(inner)?,
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
                    crate::source::EDecl::Val(_, bound_expression) => repair_expression(bound_expression)?,
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

pub fn repair_sql_placeholders_in_file(file: &mut File) -> Result<(), String> {
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
            Decl::Index(first_expression, second_expression, _) | Decl::Task(first_expression, second_expression) => {
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

fn repair_structure(structure_expression: &mut crate::source::LocStr) -> Result<(), String> {
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
