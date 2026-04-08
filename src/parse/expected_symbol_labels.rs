//! Friendly descriptions for LALRPOP “expected” terminal lists (parse error hints).
//!
//! Terminals are emitted as **double-quoted** spellings matching `grammar.lalrpop`
//! (`"fun"`, `"INT"`, `"("`, …). See generated `____TERMINAL` in `OUT_DIR/parse/grammar.rs`.

/// Strip the outer `"…"` wrapper LALRPOP uses when serializing a terminal name.
///
/// # Arguments
///
/// * `label` — Raw entry from LALRPOP’s `expected` vector.
///
/// # Returns
///
/// Inner slice without the surrounding quote characters, or `label` if not double-quoted.
fn unquote_terminal_label(label: &str) -> &str {
    label
        .strip_prefix('"')
        .and_then(|inner| inner.strip_suffix('"'))
        .unwrap_or(label)
}

/// Turn one LALRPOP expected-terminal string into a short, helpful phrase.
///
/// # Arguments
///
/// * `quoted_terminal` — Element from [`lalrpop_util::ParseError`]'s `expected` vector.
///
/// # Returns
///
/// English fragment suitable inside “expected one of: …”.
pub fn friendly_expected_terminal_label(quoted_terminal: &str) -> String {
    let inner = unquote_terminal_label(quoted_terminal);
    match inner {
        // Lexical classes
        "INT" => "an integer literal (like `42`)".to_string(),
        "FLOAT" => "a floating-point literal (like `3.14`)".to_string(),
        "STRING" => "a double-quoted string literal".to_string(),
        "CHAR" => "a character literal (`#\"a\"`)".to_string(),
        "IDENT" => "a name (starts with lower-case or `_`)".to_string(),
        "UIDENT" => "a capitalized name (module or datatype constructor)".to_string(),
        "BACKTICK_PATH" => "a backtick path (`` `Module.val` ``)".to_string(),
        "SYMBOL" => "a policy/cookie symbol".to_string(),
        // Kind keywords in surface syntax
        "Name" => "the kind name `Name`".to_string(),
        "Type" => "the kind name `Type`".to_string(),
        "Unit" => "the kind name `Unit`".to_string(),
        // XML / markup
        "BEGIN_TAG" => "the start of an XML tag (`<tag`)".to_string(),
        "END_TAG" => "a closing XML tag (`</tag>`)".to_string(),
        "XML_BEGIN_END" => "a self-closing XML tag (`/>`)".to_string(),
        "NOTAGS" => "plain text inside XML (no `<` or `{` here)".to_string(),
        "XML_ATTR_NAME_EQ" => "an XML attribute name before `=`".to_string(),
        "XML_ATTR_NAME_BARE" => "a boolean XML attribute name".to_string(),
        // Preprocessor / grammar infrastructure (still seen by users when things go wrong)
        "WILDANNOT" => "a wildcard kind annotation (`_ :: …`)".to_string(),
        "case_bar" => "optional `|` right after `case` … `of`".to_string(),
        "arm_sep" => "`|` between `case` arms".to_string(),
        "case_end" => "end of the `case` arm list (inserted by the parser)".to_string(),
        "dtype_of" => "`of` in a datatype constructor branch".to_string(),
        "dt_con0" => "a datatype constructor slot (nullary branch)".to_string(),
        "dt_bar" => "`|` between datatype constructors".to_string(),
        "dt_done" => "end of a datatype constructor list".to_string(),
        "sgn_where" => "`where` in a signature (top level)".to_string(),
        "sgn_subwhere" => "`where` inside nested parentheses in a signature".to_string(),
        // Punctuation & operators — keep the actual glyph in backticks
        "()" => "unit `()`".to_string(),
        "(" => "opening `(`".to_string(),
        ")" => "closing `)`".to_string(),
        "{" => "opening `{`".to_string(),
        "}" => "closing `}`".to_string(),
        "[" => "opening `[`".to_string(),
        "]" => "closing `]`".to_string(),
        "," => "comma `,`".to_string(),
        ";" => "semicolon `;`".to_string(),
        ":" => "colon `:`".to_string(),
        "::" => "double colon `::` (type/kind annotation)".to_string(),
        ":::" => "triple colon `:::` (implicit argument)".to_string(),
        "::::" => "`::::`".to_string(),
        "." => "dot `.`".to_string(),
        "..." => "ellipsis `...`".to_string(),
        "_" => "underscore `_`".to_string(),
        "__" => "`__`".to_string(),
        "___" => "`___`".to_string(),
        "|" => "vertical bar `|`".to_string(),
        "#" => "hash `#`".to_string(),
        "$" => "dollar `$`".to_string(),
        "^" => "caret `^`".to_string(),
        "~" => "tilde `~`".to_string(),
        "@" => "at `@`".to_string(),
        "AT_TSO_PATH" => "`@` qualified path (types only)".to_string(),
        "AT_DI_PATH" => "`@@` qualified path (no type inference)".to_string(),
        "!" => "bang `!`".to_string(),
        "+" => "plus `+`".to_string(),
        "-" => "minus `-`".to_string(),
        "*" => "star `*`".to_string(),
        "/" => "slash `/`".to_string(),
        "%" => "percent `%`".to_string(),
        "<" => "less-than `<`".to_string(),
        ">" => "greater-than `>`".to_string(),
        "=" => "equals `=`".to_string(),
        "<>" => "not-equal `<>`".to_string(),
        "<=" => "less-or-equal `<=`".to_string(),
        ">=" => "greater-or-equal `>=`".to_string(),
        "->" => "arrow `->` (function or kind arrow)".to_string(),
        "=>" => "fat arrow `=>` (case arm or functor)".to_string(),
        "==>" => "thick arrow `==>`".to_string(),
        "-->" => "kind arrow `-->`".to_string(),
        "<-" => "bind arrow `<-`".to_string(),
        "++" => "plus-plus `++`".to_string(),
        "--" => "minus-minus `--`".to_string(),
        "---" => "triple minus `---`".to_string(),
        "|>" => "forward pipe `|>`".to_string(),
        "<|" => "backward pipe `<|`".to_string(),
        // Reserved words — name the keyword explicitly
        "and" => "keyword `and`".to_string(),
        "andalso" => "keyword `andalso`".to_string(),
        "case" => "keyword `case`".to_string(),
        "class" => "keyword `class`".to_string(),
        "con" => "keyword `con`".to_string(),
        "constraint" => "keyword `constraint`".to_string(),
        "constraints" => "keyword `constraints`".to_string(),
        "cookie" => "keyword `cookie`".to_string(),
        "datatype" => "keyword `datatype`".to_string(),
        "else" => "keyword `else`".to_string(),
        "end" => "keyword `end`".to_string(),
        "export" => "keyword `export`".to_string(),
        "false" => "keyword `false`".to_string(),
        "ffi" => "keyword `ffi`".to_string(),
        "fn" => "keyword `fn`".to_string(),
        "fun" => "keyword `fun`".to_string(),
        "functor" => "keyword `functor`".to_string(),
        "if" => "keyword `if`".to_string(),
        "in" => "keyword `in`".to_string(),
        "include" => "keyword `include`".to_string(),
        "let" => "keyword `let`".to_string(),
        "map" => "keyword `map`".to_string(),
        "of" => "keyword `of`".to_string(),
        "open" => "keyword `open`".to_string(),
        "orelse" => "keyword `orelse`".to_string(),
        "policy" => "keyword `policy`".to_string(),
        "rec" => "keyword `rec`".to_string(),
        "sequence" => "keyword `sequence`".to_string(),
        "sig" => "keyword `sig`".to_string(),
        "signature" => "keyword `signature`".to_string(),
        "struct" => "keyword `struct`".to_string(),
        "structure" => "keyword `structure`".to_string(),
        "style" => "keyword `style`".to_string(),
        "table" => "keyword `table`".to_string(),
        "task" => "keyword `task`".to_string(),
        "then" => "keyword `then`".to_string(),
        "true" => "keyword `true`".to_string(),
        "type" => "keyword `type`".to_string(),
        "val" => "keyword `val`".to_string(),
        "view" => "keyword `view`".to_string(),
        "SQL" => "keyword `SQL`".to_string(),
        "SELECT" => "keyword `SELECT`".to_string(),
        "FROM" => "keyword `FROM`".to_string(),
        "AS" => "keyword `AS`".to_string(),
        "COUNT" => "keyword `COUNT`".to_string(),
        "CURRENT_TIMESTAMP" => "keyword `CURRENT_TIMESTAMP`".to_string(),
        "DELETE" => "keyword `DELETE`".to_string(),
        "IS" => "keyword `IS`".to_string(),
        "INSERT" => "keyword `INSERT`".to_string(),
        "INTO" => "keyword `INTO`".to_string(),
        "JOIN" => "keyword `JOIN`".to_string(),
        "LEFT" => "keyword `LEFT`".to_string(),
        "NULL" => "keyword `NULL`".to_string(),
        "ON" => "keyword `ON`".to_string(),
        "AND" => "keyword `AND`".to_string(),
        "OR" => "keyword `OR`".to_string(),
        "SET" => "keyword `SET`".to_string(),
        "SQL_STAR" => "SQL wildcard placeholder `sql_star`".to_string(),
        "UPDATE" => "keyword `UPDATE`".to_string(),
        "VALUES" => "keyword `VALUES`".to_string(),
        "WHERE" => "keyword `WHERE`".to_string(),
        "urweb_put" => "keyword `urweb_put`".to_string(),
        "urweb_get" => "keyword `urweb_get`".to_string(),
        "urweb_tb_transfer" => "keyword `urweb_tb_transfer`".to_string(),
        other => fallback_terminal_label(other),
    }
}

/// Last-resort wording when a new terminal was added to the grammar but not this table yet.
fn fallback_terminal_label(inner: &str) -> String {
    if inner.is_empty() {
        return "an empty token label (please report this)".to_string();
    }
    format!("`{inner}` (if this looks cryptic, it may be a parser-internal name — please report)")
}

/// Join mapped “expected” hints with truncation and light deduplication.
///
/// # Arguments
///
/// * `expected` — Raw list from LALRPOP.
///
/// # Returns
///
/// Human-oriented list separated by `; ` for readability when phrases contain commas.
pub fn join_friendly_expected_labels(expected: &[String]) -> String {
    use std::collections::HashSet;
    const MAX_LABELS: usize = 12;
    let mut seen: HashSet<String> = HashSet::new();
    let mut unique_ordered: Vec<String> = Vec::new();
    for raw in expected {
        let friendly = friendly_expected_terminal_label(raw);
        if seen.insert(friendly.clone()) {
            unique_ordered.push(friendly);
        }
    }
    if unique_ordered.len() <= MAX_LABELS {
        return unique_ordered.join("; ");
    }
    let rest = unique_ordered.len() - MAX_LABELS;
    unique_ordered.truncate(MAX_LABELS);
    format!(
        "{}; … (+{rest} more kinds of token)",
        unique_ordered.join("; ")
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn int_terminal_maps_to_literal_hint() {
        let label = friendly_expected_terminal_label("\"INT\"");
        assert!(label.contains("integer"), "unexpected mapping: {label}");
    }

    #[test]
    fn fun_keyword_is_explained() {
        let label = friendly_expected_terminal_label("\"fun\"");
        assert!(label.contains('`') && label.contains("fun"), "{label}");
    }

    #[test]
    fn dedup_join_skips_duplicate_friendly_strings() {
        let list = vec![
            "\"INT\"".to_string(),
            "\"INT\"".to_string(),
            "\"FLOAT\"".to_string(),
        ];
        let joined = join_friendly_expected_labels(&list);
        let int_count = joined.matches("integer").count();
        assert!(
            int_count <= 1,
            "dedup should collapse repeated INT: {joined}"
        );
    }

    #[test]
    fn join_uses_semicolons_between_hints() {
        let joined = join_friendly_expected_labels(&["\"INT\"".into(), "\"(\"".into()]);
        assert!(
            joined.contains(';'),
            "expected `; ` separation for scanability: {joined}"
        );
    }
}
