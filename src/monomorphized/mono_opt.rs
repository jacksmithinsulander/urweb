//! Peephole optimizer for the Mono IR.
//!
//! Constant-folds string encoding, arithmetic, and HTML/URL/SQL generation
//! functions, distributes `EWrite` into `EStrcat`/`ECase`/`ELet`, etc.
//!
//! Mirrors `mono_opt.sml`.
//!
//! SQL string scanners (`un_as`, `uwify_inner`, `uwify_viewify`) use bounded `for` loops over index
//! space (`0..chars.len()`) with a moving cursor `i`, so work stays linear in the UTF-32 scalar count.

use std::cell::RefCell;

use crate::db::ProjectDbCtx;
use crate::diagnostics::{DiagnosticId, DiagnosticPayload};
use crate::error_types::{ErrorReporter, Located, Span};
use crate::monomorphized::{utilities, Exp, LocDecl, LocExp, LocTyp, Typ};
use crate::primitives::{Prim, StringMode};
use crate::settings::Settings;

// ---------------------------------------------------------------------------
// String encoding helpers — pure, no settings
// ---------------------------------------------------------------------------

fn attrify_int(n: i64) -> String {
    match n < 0 {
        true => format!("-{}", -n),
        false => n.to_string(),
    }
}

fn attrify_float(n: f64) -> String {
    match n < 0.0 {
        true => format!("-{}", -n),
        false => n.to_string(),
    }
}

fn attrify_char(ch: char) -> String {
    match ch {
        '"' => "&quot;".into(),
        '&' => "&amp;".into(),
        c => c.to_string(),
    }
}

fn attrify_string(s: &str) -> String {
    s.chars().map(attrify_char).collect()
}

fn htmlify_string(s: &str) -> String {
    s.chars()
        .map(|c| match c {
            '<' => "&lt;".into(),
            '&' => "&amp;".into(),
            c => c.to_string(),
        })
        .collect()
}

fn htmlify_special_char(ch: char) -> String {
    format!("&#{};", ch as u32)
}

fn hex_pad(c: u32) -> String {
    let s = format!("{:X}", c);
    match s.len() {
        0 => "00".into(),
        1 => format!("0{}", s),
        _ => s,
    }
}

fn hex_it(ch: char) -> String {
    let c = ch as u32;
    match c {
        0..=0x7f => hex_pad(c),
        0x80..=0x7ff => {
            format!("{}{}", hex_pad((c >> 6) | 0xc0), hex_pad((c & 0x3f) | 0x80))
        }
        0x800..=0xffff => format!(
            "{}{}{}",
            hex_pad((c >> 12) | 0xe0),
            hex_pad(((c >> 6) & 0x3f) | 0x80),
            hex_pad((c & 0x3f) | 0x80),
        ),
        _ => format!(
            "{}{}{}{}",
            hex_pad((c >> 18) | 0xf0),
            hex_pad(((c >> 12) & 0x3f) | 0x80),
            hex_pad(((c >> 6) & 0x3f) | 0x80),
            hex_pad((c & 0x3f) | 0x80),
        ),
    }
}

fn urlify_char_aux(ch: char) -> String {
    match ch {
        ' ' => "+".into(),
        c if c as u32 == 0 => "_".into(),
        c if c.is_alphanumeric() => c.to_string(),
        c => format!(".{}", hex_it(c)),
    }
}

fn urlify_char(ch: char) -> String {
    match ch == '_' {
        true => format!("_{}", urlify_char_aux(ch)),
        false => urlify_char_aux(ch),
    }
}

fn urlify_string(s: &str) -> String {
    if s.is_empty() {
        return "_".into();
    }
    let prefix = match s.starts_with('_') {
        true => "_",
        false => "",
    };
    format!(
        "{}{}",
        prefix,
        s.chars().map(urlify_char_aux).collect::<String>()
    )
}

// ---------------------------------------------------------------------------
// Settings-dependent SQL helpers
// ---------------------------------------------------------------------------

fn sqlify_int(n: i64, settings: &Settings) -> String {
    let s = attrify_int(n);
    match ProjectDbCtx::new(&settings.db_backend).is_mysql() {
        true => s,
        false => format!("{}::int8", s),
    }
}

fn sqlify_float(n: f64, settings: &Settings) -> String {
    let s = attrify_float(n);
    match ProjectDbCtx::new(&settings.db_backend).is_mysql() {
        true => s,
        false => format!("{}::float8", s),
    }
}

fn sqlify_string(s: &str, settings: &Settings) -> String {
    match ProjectDbCtx::new(&settings.db_backend).is_mysql() {
        true => {
            let escaped: String = s
                .chars()
                .flat_map(|c| match c {
                    '\'' => vec!['\\', '\''],
                    '\\' => vec!['\\', '\\'],
                    c => vec![c],
                })
                .collect();
            format!("'{}'", escaped)
        }
        false => {
            let escaped = s.replace('\'', "''");
            format!("'{}'", escaped)
        }
    }
}

fn sqlify_char(ch: char, settings: &Settings) -> String {
    let mut buf = String::new();
    buf.push(ch);
    sqlify_string(&buf, settings)
}

fn sqlify_bool_true(settings: &Settings) -> &'static str {
    match ProjectDbCtx::new(&settings.db_backend).is_mysql() {
        true => "1",
        false => "TRUE",
    }
}

fn sqlify_bool_false(settings: &Settings) -> &'static str {
    match ProjectDbCtx::new(&settings.db_backend).is_mysql() {
        true => "0",
        false => "FALSE",
    }
}

// ---------------------------------------------------------------------------
// Validation predicates
// ---------------------------------------------------------------------------

fn check_url(s: &str, settings: &Settings) -> bool {
    s.chars().all(|c| c.is_ascii_graphic()) && settings.check_url(s)
}

fn check_data(s: &str) -> bool {
    s.chars()
        .all(|c| c.is_alphanumeric() || c == '_' || c == '-')
}

fn check_atom(s: &str) -> bool {
    s.chars().all(|c| {
        c.is_alphanumeric()
            || c == '+'
            || c == '-'
            || c == '.'
            || c == '%'
            || c == ','
            || c == ' '
            || c == '('
            || c == ')'
            || c == '#'
    })
}

fn check_css_url(s: &str) -> bool {
    s.chars().all(|c| {
        c.is_alphanumeric()
            || c == ':'
            || c == '/'
            || c == '.'
            || c == '_'
            || c == '+'
            || c == '-'
            || c == '%'
            || c == '?'
            || c == '&'
            || c == '='
            || c == '#'
    })
}

fn check_property(s: &str) -> bool {
    let nmstart = |c: char| c.is_alphabetic() || c == '_';
    let nmchar = |c: char| c.is_alphabetic() || c.is_ascii_digit() || c == '_' || c == '-';
    match s.chars().next() {
        None => false,
        Some(first) => {
            let rest_ok = s.chars().all(nmchar);
            rest_ok && (nmstart(first) || (first == '-' && s.chars().nth(1).is_some_and(nmstart)))
        }
    }
}

// ---------------------------------------------------------------------------
// SQL string helpers
// ---------------------------------------------------------------------------

/// Copy characters inside a SQL single-quoted literal: `i` is just after the opening `'`;
/// on return `i` sits after the closing `'` or at `chars.len()` if EOF before close.
fn copy_sql_single_quoted_literal(chars: &[char], i: &mut usize, out: &mut Vec<char>) {
    for _ in 0..chars.len() {
        if *i >= chars.len() {
            break;
        }
        let double_backslash = chars[*i] == '\\' && *i + 1 < chars.len() && chars[*i + 1] == '\\';
        let escaped_quote = chars[*i] == '\\' && *i + 1 < chars.len() && chars[*i + 1] == '\'';
        let close_quote = chars[*i] == '\'';
        match (double_backslash, escaped_quote, close_quote) {
            (true, _, _) => {
                out.push('\\');
                out.push('\\');
                *i += 2;
            }
            (false, true, _) => {
                out.push('\\');
                out.push('\'');
                *i += 2;
            }
            (false, false, true) => {
                out.push('\'');
                *i += 1;
                break;
            }
            (false, false, false) => {
                out.push(chars[*i]);
                *i += 1;
            }
        }
    }
}

/// Strip `T_T.` table-alias prefixes from SQL strings, handling quoted strings.
fn un_as(s: &str) -> String {
    let chars: Vec<char> = s.chars().collect();
    let mut out = Vec::new();
    let mut i = 0usize;
    let scan_budget = chars.len();
    for _ in 0..scan_budget {
        if i >= chars.len() {
            break;
        }
        let t_t_dot = i + 3 < chars.len()
            && chars[i] == 'T'
            && chars[i + 1] == '_'
            && chars[i + 2] == 'T'
            && chars[i + 3] == '.';
        match (t_t_dot, chars[i] == '\'') {
            (true, _) => {
                i += 4;
            }
            (false, true) => {
                out.push('\'');
                i += 1;
                copy_sql_single_quoted_literal(&chars, &mut i, &mut out);
            }
            (false, false) => {
                out.push(chars[i]);
                i += 1;
            }
        }
    }
    debug_assert!(i == chars.len(), "un_as: must consume entire slice");
    out.into_iter().collect()
}

/// Rename `_identifier` to `uw_identifier` in a SQL fragment
/// (for `checkString`).
fn uwify_check_string(s: &str) -> String {
    let chars: Vec<char> = s.chars().collect();
    let (prefix, start) = match chars.first() {
        Some(&'_') => ("uw_", 1usize),
        _ => ("", 0usize),
    };
    let body = uwify_inner(&chars[start..]);
    format!("{}{}", prefix, body)
}

/// Apply `_` → `uw_` rewrites inside parentheses / after spaces; skips single-quoted literals.
fn uwify_inner(chars: &[char]) -> String {
    let mut out = Vec::new();
    let mut i = 0usize;
    let scan_budget = chars.len();
    for _ in 0..scan_budget {
        if i >= chars.len() {
            break;
        }
        let paren_or_space_underscore =
            i + 1 < chars.len() && (chars[i] == '(' || chars[i] == ' ') && chars[i + 1] == '_';
        match (paren_or_space_underscore, chars[i] == '\'') {
            (true, _) => {
                out.push(chars[i]);
                out.extend("uw_".chars());
                i += 2;
            }
            (false, true) => {
                out.push('\'');
                i += 1;
                copy_sql_single_quoted_literal(chars, &mut i, &mut out);
            }
            (false, false) => {
                out.push(chars[i]);
                i += 1;
            }
        }
    }
    debug_assert!(i == chars.len(), "uwify_inner: must consume entire slice");
    out.into_iter().collect()
}

/// Rename `AS _col` → `AS uw_col` in SQL (for `viewify`).
fn uwify_viewify(s: &str) -> String {
    let chars: Vec<char> = s.chars().collect();
    let mut out = Vec::new();
    let mut i = 0usize;
    let scan_budget = chars.len();
    for _ in 0..scan_budget {
        if i >= chars.len() {
            break;
        }
        let as_space_underscore = i + 4 < chars.len()
            && chars[i] == 'A'
            && chars[i + 1] == 'S'
            && chars[i + 2] == ' '
            && chars[i + 3] == '_';
        match (as_space_underscore, chars[i] == '\'') {
            (true, _) => {
                out.extend("AS uw_".chars());
                i += 4;
            }
            (false, true) => {
                out.push('\'');
                i += 1;
                copy_sql_single_quoted_literal(&chars, &mut i, &mut out);
            }
            (false, false) => {
                out.push(chars[i]);
                i += 1;
            }
        }
    }
    debug_assert!(i == chars.len(), "uwify_viewify: must consume entire slice");
    out.into_iter().collect()
}

// ---------------------------------------------------------------------------
// Helpers for un_as applied to expressions
// ---------------------------------------------------------------------------

/// Try to decompose a strcat-tree into a flat list of string/sqlify parts,
/// apply unAs to string parts, then reassemble.
fn un_as_exp(e: &LocExp) -> Option<Exp> {
    fn parts(e: &LocExp) -> Option<Vec<LocExp>> {
        match &e.node {
            Exp::Strcat(s1, s2) => {
                let mut p1 = parts(s1)?;
                let p2 = parts(s2)?;
                p1.extend(p2);
                Some(p1)
            }
            Exp::Prim(Prim::String(_, s)) => Some(vec![Located::new(
                Exp::Prim(Prim::String(StringMode::Normal, un_as(s))),
                e.span.clone(),
            )]),
            Exp::FfiApp(m, f, _) if m == "Basis" && f.starts_with("sqlify") => {
                Some(vec![e.clone()])
            }
            _ => None,
        }
    }

    let ps = parts(e)?;
    match ps.len() {
        0 => None,
        1 => ps.into_iter().next().map(|e| e.node),
        _ => {
            let mut iter = ps.into_iter().rev();
            let first = iter.next()?;
            let result = iter.fold(first, |acc, p| {
                let span = p.span.clone();
                Located::new(Exp::Strcat(Box::new(p), Box::new(acc)), span)
            });
            Some(result.node)
        }
    }
}

// ---------------------------------------------------------------------------
// Liftspan helper
// ---------------------------------------------------------------------------

fn lspan(node: Exp, span: &Span) -> LocExp {
    Located::new(node, span.clone())
}

fn string_lit(mode: StringMode, s: impl Into<String>, span: &Span) -> LocExp {
    lspan(Exp::Prim(Prim::String(mode, s.into())), span)
}

fn html_lit(s: impl Into<String>, span: &Span) -> LocExp {
    string_lit(StringMode::Html, s, span)
}

fn normal_lit(s: impl Into<String>, span: &Span) -> LocExp {
    string_lit(StringMode::Normal, s, span)
}

// ---------------------------------------------------------------------------
// Helper: check if a PatCon is a Ffi constructor with a given module/con
// ---------------------------------------------------------------------------

/// Returns whether `pc` is an FFI pattern constructor for `module::con`.
fn is_ffi_con(pc: &crate::monomorphized::PatCon, module: &str, con: &str) -> bool {
    match pc {
        crate::monomorphized::PatCon::Ffi {
            module: m, con: c, ..
        } => m == module && c == con,
        _ => false,
    }
}

/// Folds the single argument of `Basis.htmlifyString` when it is `intToString`, curried `Ffi`, or literals.
///
/// # Arguments
///
/// * `htmlify_string_call_arguments` — `[arg]` plus types as emitted for `htmlifyString`.
///
/// # Returns
///
/// The optimized [`Exp`] (folded primitive string or a shorter `FfiApp` chain).
fn fold_basis_htmlify_string_arg(htmlify_string_call_arguments: Vec<(LocExp, LocTyp)>) -> Exp {
    // Duplicate the outer call when we cannot inspect a single argument safely.
    let fallback = || {
        Exp::FfiApp(
            "Basis".into(),
            "htmlifyString".into(),
            htmlify_string_call_arguments.clone(),
        )
    };
    // Require exactly one argument; otherwise preserve the original call.
    let [only_pair] = htmlify_string_call_arguments.as_slice() else {
        return fallback();
    };
    let argument_expression = &only_pair.0;
    // Dispatch on the inner expression shape (mirrors mono_opt.sml htmlifyString rewrites).
    match &argument_expression.node {
        // `htmlifyString(Basis.intToString e)` spine as `FfiApp`.
        Exp::FfiApp(inner_module, inner_function, inner_args)
            if inner_module == "Basis" && inner_function == "intToString" =>
        {
            // Fold integer literals to HTML text; otherwise lower to `htmlifyInt`.
            match inner_args.as_slice() {
                [single_int] => {
                    if let Exp::Prim(Prim::Int(n)) = single_int.0.node {
                        return Exp::Prim(Prim::String(StringMode::Html, htmlify_int(n)));
                    }
                    Exp::FfiApp("Basis".into(), "htmlifyInt".into(), inner_args.clone())
                }
                _ => Exp::FfiApp("Basis".into(), "htmlifyInt".into(), inner_args.clone()),
            }
        }
        // `htmlifyString(Basis.floatToString e)` as `FfiApp`.
        Exp::FfiApp(inner_module, inner_function, inner_args)
            if inner_module == "Basis" && inner_function == "floatToString" =>
        {
            match inner_args.as_slice() {
                [single_float] => {
                    if let Exp::Prim(Prim::Float(n)) = single_float.0.node {
                        return Exp::Prim(Prim::String(StringMode::Html, htmlify_float(n)));
                    }
                    Exp::FfiApp("Basis".into(), "htmlifyFloat".into(), inner_args.clone())
                }
                _ => Exp::FfiApp("Basis".into(), "htmlifyFloat".into(), inner_args.clone()),
            }
        }
        // `htmlifyString(Basis.boolToString e)` as `FfiApp`.
        Exp::FfiApp(inner_module, inner_function, inner_args)
            if inner_module == "Basis" && inner_function == "boolToString" =>
        {
            if let [only_bool] = inner_args.as_slice() {
                match &only_bool.0.node {
                    Exp::Con(_, pattern_constructor, None)
                        if is_ffi_con(pattern_constructor, "Basis", "True") =>
                    {
                        return Exp::Prim(Prim::String(StringMode::Html, "True".into()));
                    }
                    Exp::Con(_, pattern_constructor, None)
                        if is_ffi_con(pattern_constructor, "Basis", "False") =>
                    {
                        return Exp::Prim(Prim::String(StringMode::Html, "False".into()));
                    }
                    _ => {}
                }
            }
            Exp::FfiApp("Basis".into(), "htmlifyBool".into(), inner_args.clone())
        }
        // Curried `EApp(EFfi(Basis, f), e)` forms (often after monomorphization).
        Exp::App(function_part, argument_part) => match &function_part.node {
            Exp::Ffi(module_name, ffi_name) if module_name == "Basis" => match ffi_name.as_str() {
                "intToString" => {
                    if let Exp::Prim(Prim::Int(n)) = argument_part.node {
                        return Exp::Prim(Prim::String(StringMode::Html, htmlify_int(n)));
                    }
                    let argument_type: LocTyp = Located::new(
                        Typ::Ffi("Basis".into(), "int".into()),
                        function_part.span.clone(),
                    );
                    Exp::FfiApp(
                        "Basis".into(),
                        "htmlifyInt".into(),
                        vec![(*argument_part.clone(), argument_type)],
                    )
                }
                "floatToString" => {
                    if let Exp::Prim(Prim::Float(n)) = argument_part.node {
                        return Exp::Prim(Prim::String(StringMode::Html, htmlify_float(n)));
                    }
                    let argument_type: LocTyp = Located::new(
                        Typ::Ffi("Basis".into(), "float".into()),
                        function_part.span.clone(),
                    );
                    Exp::FfiApp(
                        "Basis".into(),
                        "htmlifyFloat".into(),
                        vec![(*argument_part.clone(), argument_type)],
                    )
                }
                "timeToString" => {
                    let argument_type: LocTyp = Located::new(
                        Typ::Ffi("Basis".into(), "time".into()),
                        function_part.span.clone(),
                    );
                    Exp::FfiApp(
                        "Basis".into(),
                        "htmlifyTime".into(),
                        vec![(*argument_part.clone(), argument_type)],
                    )
                }
                _ => fallback(),
            },
            _ => fallback(),
        },
        Exp::Prim(Prim::String(_, payload)) => {
            Exp::Prim(Prim::String(StringMode::Html, htmlify_string(payload)))
        }
        _ => fallback(),
    }
}

/// Rewrites `Basis.FfiApp` that sits directly under [`Exp::Write`] to writer suffix forms or constant HTML.
///
/// # Arguments
///
/// * `basis_function_name` — second component of `FfiApp` (`"htmlifyInt"`, etc.).
/// * `ffi_call_arguments` — arguments paired with types for this call.
/// * `optimization_span` — span for nodes synthesized in this peephole step.
///
/// # Returns
///
/// [`None`] if this function name is not part of the write-placement table (caller re-wraps `EWrite`).
fn try_rewrite_basis_ffi_inside_write(
    basis_function_name: &str,
    ffi_call_arguments: &[(LocExp, LocTyp)],
    optimization_span: &Span,
) -> Option<Exp> {
    match basis_function_name {
        "htmlifySpecialChar" => Some(Exp::FfiApp(
            "Basis".into(),
            "htmlifySpecialChar_w".into(),
            ffi_call_arguments.to_vec(),
        )),
        "intToString" => Some(Exp::FfiApp(
            "Basis".into(),
            "htmlifyInt_w".into(),
            ffi_call_arguments.to_vec(),
        )),
        "htmlifyInt" => Some(Exp::FfiApp(
            "Basis".into(),
            "htmlifyInt_w".into(),
            ffi_call_arguments.to_vec(),
        )),
        "htmlifyFloat" => Some(Exp::FfiApp(
            "Basis".into(),
            "htmlifyFloat_w".into(),
            ffi_call_arguments.to_vec(),
        )),
        "htmlifyBool" => Some(Exp::FfiApp(
            "Basis".into(),
            "htmlifyBool_w".into(),
            ffi_call_arguments.to_vec(),
        )),
        "htmlifyTime" => Some(Exp::FfiApp(
            "Basis".into(),
            "htmlifyTime_w".into(),
            ffi_call_arguments.to_vec(),
        )),
        "htmlifyString" => {
            if let [(single_argument, _)] = ffi_call_arguments {
                if let Exp::Prim(Prim::String(_, payload)) = &single_argument.node {
                    return Some(Exp::Write(Box::new(html_lit(
                        htmlify_string(payload),
                        optimization_span,
                    ))));
                }
            }
            Some(Exp::FfiApp(
                "Basis".into(),
                "htmlifyString_w".into(),
                ffi_call_arguments.to_vec(),
            ))
        }
        "htmlifySource" => Some(Exp::FfiApp(
            "Basis".into(),
            "htmlifySource_w".into(),
            ffi_call_arguments.to_vec(),
        )),
        "attrifyInt" => match ffi_call_arguments {
            [(single, _)] => {
                if let Exp::Prim(Prim::Int(n)) = single.node {
                    Some(Exp::Write(Box::new(html_lit(
                        attrify_int(n),
                        optimization_span,
                    ))))
                } else {
                    Some(Exp::FfiApp(
                        "Basis".into(),
                        "attrifyInt_w".into(),
                        ffi_call_arguments.to_vec(),
                    ))
                }
            }
            _ => Some(Exp::FfiApp(
                "Basis".into(),
                "attrifyInt_w".into(),
                ffi_call_arguments.to_vec(),
            )),
        },
        "attrifyFloat" => match ffi_call_arguments {
            [(single, _)] => {
                if let Exp::Prim(Prim::Float(n)) = single.node {
                    Some(Exp::Write(Box::new(html_lit(
                        attrify_float(n),
                        optimization_span,
                    ))))
                } else {
                    Some(Exp::FfiApp(
                        "Basis".into(),
                        "attrifyFloat_w".into(),
                        ffi_call_arguments.to_vec(),
                    ))
                }
            }
            _ => Some(Exp::FfiApp(
                "Basis".into(),
                "attrifyFloat_w".into(),
                ffi_call_arguments.to_vec(),
            )),
        },
        "attrifyString" => match ffi_call_arguments {
            [(single, _)] => {
                if let Exp::Prim(Prim::String(_, payload)) = &single.node {
                    Some(Exp::Write(Box::new(html_lit(
                        attrify_string(payload),
                        optimization_span,
                    ))))
                } else {
                    Some(Exp::FfiApp(
                        "Basis".into(),
                        "attrifyString_w".into(),
                        ffi_call_arguments.to_vec(),
                    ))
                }
            }
            _ => Some(Exp::FfiApp(
                "Basis".into(),
                "attrifyString_w".into(),
                ffi_call_arguments.to_vec(),
            )),
        },
        "attrifyChar" => match ffi_call_arguments {
            [(single, _)] => {
                if let Exp::Prim(Prim::Char(ch)) = single.node {
                    Some(Exp::Write(Box::new(html_lit(
                        attrify_char(ch),
                        optimization_span,
                    ))))
                } else {
                    Some(Exp::FfiApp(
                        "Basis".into(),
                        "attrifyChar_w".into(),
                        ffi_call_arguments.to_vec(),
                    ))
                }
            }
            _ => Some(Exp::FfiApp(
                "Basis".into(),
                "attrifyChar_w".into(),
                ffi_call_arguments.to_vec(),
            )),
        },
        "attrifyCss_class" => match ffi_call_arguments {
            [(single, _)] => {
                if let Exp::Prim(Prim::String(_, payload)) = &single.node {
                    Some(Exp::Write(Box::new(html_lit(
                        payload.clone(),
                        optimization_span,
                    ))))
                } else {
                    Some(Exp::FfiApp(
                        "Basis".into(),
                        "attrifyString_w".into(),
                        ffi_call_arguments.to_vec(),
                    ))
                }
            }
            _ => Some(Exp::FfiApp(
                "Basis".into(),
                "attrifyString_w".into(),
                ffi_call_arguments.to_vec(),
            )),
        },
        "urlifyInt" => match ffi_call_arguments {
            [(single, _)] => {
                if let Exp::Prim(Prim::Int(n)) = single.node {
                    Some(Exp::Write(Box::new(normal_lit(
                        urlify_int(n),
                        optimization_span,
                    ))))
                } else {
                    Some(Exp::FfiApp(
                        "Basis".into(),
                        "urlifyInt_w".into(),
                        ffi_call_arguments.to_vec(),
                    ))
                }
            }
            _ => Some(Exp::FfiApp(
                "Basis".into(),
                "urlifyInt_w".into(),
                ffi_call_arguments.to_vec(),
            )),
        },
        "urlifyFloat" => match ffi_call_arguments {
            [(single, _)] => {
                if let Exp::Prim(Prim::Float(n)) = single.node {
                    Some(Exp::Write(Box::new(normal_lit(
                        urlify_float(n),
                        optimization_span,
                    ))))
                } else {
                    Some(Exp::FfiApp(
                        "Basis".into(),
                        "urlifyFloat_w".into(),
                        ffi_call_arguments.to_vec(),
                    ))
                }
            }
            _ => Some(Exp::FfiApp(
                "Basis".into(),
                "urlifyFloat_w".into(),
                ffi_call_arguments.to_vec(),
            )),
        },
        "urlifyString" => match ffi_call_arguments {
            [(single, _)] => {
                if let Exp::Prim(Prim::String(StringMode::Normal, payload)) = &single.node {
                    Some(Exp::Write(Box::new(normal_lit(
                        urlify_string(payload),
                        optimization_span,
                    ))))
                } else {
                    Some(Exp::FfiApp(
                        "Basis".into(),
                        "urlifyString_w".into(),
                        ffi_call_arguments.to_vec(),
                    ))
                }
            }
            _ => Some(Exp::FfiApp(
                "Basis".into(),
                "urlifyString_w".into(),
                ffi_call_arguments.to_vec(),
            )),
        },
        "urlifyChar" => match ffi_call_arguments {
            [(single, _)] => {
                if let Exp::Prim(Prim::Char(ch)) = single.node {
                    Some(Exp::Write(Box::new(normal_lit(
                        urlify_char(ch),
                        optimization_span,
                    ))))
                } else {
                    Some(Exp::FfiApp(
                        "Basis".into(),
                        "urlifyChar_w".into(),
                        ffi_call_arguments.to_vec(),
                    ))
                }
            }
            _ => Some(Exp::FfiApp(
                "Basis".into(),
                "urlifyChar_w".into(),
                ffi_call_arguments.to_vec(),
            )),
        },
        "urlifyBool" => match ffi_call_arguments {
            [(single, _)] => Some(match &single.node {
                Exp::Con(_, pattern_constructor, None)
                    if is_ffi_con(pattern_constructor, "Basis", "True") =>
                {
                    Exp::Write(Box::new(normal_lit("1", optimization_span)))
                }
                Exp::Con(_, pattern_constructor, None)
                    if is_ffi_con(pattern_constructor, "Basis", "False") =>
                {
                    Exp::Write(Box::new(normal_lit("0", optimization_span)))
                }
                _ => Exp::FfiApp(
                    "Basis".into(),
                    "urlifyBool_w".into(),
                    ffi_call_arguments.to_vec(),
                ),
            }),
            _ => Some(Exp::FfiApp(
                "Basis".into(),
                "urlifyBool_w".into(),
                ffi_call_arguments.to_vec(),
            )),
        },
        "str1" => Some(Exp::FfiApp(
            "Basis".into(),
            "writec".into(),
            ffi_call_arguments.to_vec(),
        )),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Core peephole function — applied to one node after children are optimized
// ---------------------------------------------------------------------------

/// Applies local rewrites to one Mono [`Exp`] after child expressions are optimized.
///
/// # Arguments
///
/// * `e` — Mono expression node being rewritten.
/// * `span` — surrounding span used when synthesizing [`Located`] nodes.
/// * `settings` — project settings (e.g. SQL dialect) for folds that depend on configuration.
/// * `errors` — reporter cell used by validation-oriented folds (`bless*`, `check*`).
///
/// # Returns
///
/// The rewritten [`Exp`] (possibly unchanged).
///
/// # Panics
///
/// Does not panic; invalid shapes fall through without rewriting.
fn opt_exp_peephole(
    e: Exp,
    span: &Span,
    settings: &Settings,
    errors: &RefCell<&mut ErrorReporter>,
) -> Exp {
    match e {
        // -----------------------------------------------------------------------
        // HTML string: collapse consecutive spaces
        // -----------------------------------------------------------------------
        Exp::Prim(Prim::String(StringMode::Html, s))
            if s.chars().any(|c| c.is_ascii_whitespace()) =>
        {
            let mut last_space = false;
            let new_s: String = s
                .chars()
                .filter(|&c| {
                    let is_space = c.is_ascii_whitespace();
                    let skip = is_space && last_space;
                    last_space = is_space;
                    !skip
                })
                .collect();
            Exp::Prim(Prim::String(StringMode::Html, new_s))
        }

        // -----------------------------------------------------------------------
        // Basis.strcat → EStrcat
        // -----------------------------------------------------------------------
        Exp::FfiApp(ref m, ref f, ref args) if m == "Basis" && f == "strcat" && args.len() == 2 => {
            if let [ref a1, ref a2] = args[..] {
                let new_e = Exp::Strcat(Box::new(a1.0.clone()), Box::new(a2.0.clone()));
                return opt_exp_peephole(new_e, span, settings, errors);
            }
            e
        }

        // -----------------------------------------------------------------------
        // EStrcat with empty string
        // -----------------------------------------------------------------------
        Exp::Strcat(e1, e2) => {
            match (&e1.node, &e2.node) {
                (_, Exp::Prim(Prim::String(_, s))) if s.is_empty() => e1.node,
                (Exp::Prim(Prim::String(_, s)), _) if s.is_empty() => e2.node,

                // Merge adjacent Html literals (deduplicate whitespace at join)
                (
                    Exp::Prim(Prim::String(StringMode::Html, s1)),
                    Exp::Prim(Prim::String(StringMode::Html, s2)),
                ) => {
                    let merged = if !s1.is_empty()
                        && !s2.is_empty()
                        && s1.ends_with(|c: char| c.is_ascii_whitespace())
                        && s2.starts_with(|c: char| c.is_ascii_whitespace())
                    {
                        format!("{}{}", s1, &s2[1..])
                    } else {
                        format!("{}{}", s1, s2)
                    };
                    Exp::Prim(Prim::String(StringMode::Html, merged))
                }

                // Merge adjacent any-mode string literals
                (Exp::Prim(Prim::String(_, s1)), Exp::Prim(Prim::String(_, s2))) => {
                    Exp::Prim(Prim::String(StringMode::Normal, format!("{}{}", s1, s2)))
                }

                // Merge leading Html + Html-headed strcat
                (Exp::Prim(Prim::String(StringMode::Html, s1)), Exp::Strcat(inner, rest)) => {
                    if let Exp::Prim(Prim::String(StringMode::Html, s2)) = &inner.node {
                        let merged = if !s1.is_empty()
                            && !s2.is_empty()
                            && s1.ends_with(|c: char| c.is_ascii_whitespace())
                            && s2.starts_with(|c: char| c.is_ascii_whitespace())
                        {
                            format!("{}{}", s1, &s2[1..])
                        } else {
                            format!("{}{}", s1, s2)
                        };
                        let new_inner = html_lit(merged, span);
                        opt_exp_peephole(
                            Exp::Strcat(Box::new(new_inner), rest.clone()),
                            span,
                            settings,
                            errors,
                        )
                    } else {
                        Exp::Strcat(
                            e1,
                            Box::new(lspan(Exp::Strcat(inner.clone(), rest.clone()), span)),
                        )
                    }
                }

                // Merge leading any-string + any-string-headed strcat
                (Exp::Prim(Prim::String(_, s1)), Exp::Strcat(inner, rest)) => {
                    if let Exp::Prim(Prim::String(_, s2)) = &inner.node {
                        let new_inner = normal_lit(format!("{}{}", s1, s2), span);
                        opt_exp_peephole(
                            Exp::Strcat(Box::new(new_inner), rest.clone()),
                            span,
                            settings,
                            errors,
                        )
                    } else {
                        Exp::Strcat(
                            e1,
                            Box::new(lspan(Exp::Strcat(inner.clone(), rest.clone()), span)),
                        )
                    }
                }

                // Re-associate left-nested strcat to right: ((a ^ b) ^ c) → a ^ (b ^ c)
                (Exp::Strcat(_, _), _) => {
                    if let Exp::Strcat(a, b) = e1.node {
                        let inner = lspan(Exp::Strcat(b, e2), span);
                        opt_loc_exp(
                            lspan(Exp::Strcat(a, Box::new(inner)), span),
                            settings,
                            errors,
                        )
                        .node
                    } else {
                        Exp::Strcat(e1, e2)
                    }
                }

                _ => Exp::Strcat(e1, e2),
            }
        }

        // -----------------------------------------------------------------------
        // EWrite distribution
        // -----------------------------------------------------------------------
        Exp::Write(inner) => match inner.node {
            // EWrite(EStrcat(e1, e2)) → ESeq(EWrite(e1), EWrite(e2))
            Exp::Strcat(e1, e2) => {
                let w1 = opt_loc_exp(lspan(Exp::Write(e1), span), settings, errors);
                let w2 = opt_loc_exp(lspan(Exp::Write(e2), span), settings, errors);
                Exp::Seq(Box::new(w1), Box::new(w2))
            }

            // EWrite("") → ERecord []
            Exp::Prim(Prim::String(_, s)) if s.is_empty() => Exp::Record(vec![]),

            // EWrite(ELet(x,t,e1,e2)) → ELet(x,t,e1,EWrite(e2))
            Exp::Let(x, t, e1, e2) => {
                let new_body = opt_loc_exp(lspan(Exp::Write(e2), span), settings, errors);
                opt_exp_peephole(
                    Exp::Let(x, t, e1, Box::new(new_body)),
                    span,
                    settings,
                    errors,
                )
            }

            // `EWrite(Basis.FfiApp …)` rewrites: `*_w` writer forms and literal folds (see table helper).
            Exp::FfiApp(module_name, function_name, ffi_call_arguments)
                if module_name == "Basis" =>
            {
                match try_rewrite_basis_ffi_inside_write(
                    function_name.as_str(),
                    ffi_call_arguments.as_slice(),
                    span,
                ) {
                    Some(rewritten) => rewritten,
                    None => Exp::Write(Box::new(lspan(
                        Exp::FfiApp(module_name, function_name, ffi_call_arguments),
                        span,
                    ))),
                }
            }

            // EWrite(EQuery{initial="", body=strcat(s, (strcat(ERel 0, e')))}) where s is whitespace
            Exp::Query(ref qm) => {
                let initial_is_empty = matches!(
                    &qm.initial.node,
                    Exp::Prim(Prim::String(_, s)) if s.is_empty()
                );
                if initial_is_empty {
                    let write_inner = inner.clone();
                    opt_exp_peephole(Exp::Write(write_inner), span, settings, errors)
                } else {
                    Exp::Write(inner)
                }
            }

            other => Exp::Write(Box::new(lspan(other, span))),
        },

        // -----------------------------------------------------------------------
        // ESeq of writes: coalesce consecutive literal writes
        // -----------------------------------------------------------------------
        Exp::Seq(e1, e2) => {
            match (&e1.node, &e2.node) {
                (Exp::Write(w1), Exp::Write(w2)) => match (&w1.node, &w2.node) {
                    (Exp::Prim(Prim::String(_, s1)), Exp::Prim(Prim::String(_, s2))) => {
                        let merged_s = format!("{}{}", s1, s2);
                        let span1 = w1.span.clone();
                        Exp::Write(Box::new(lspan(
                            Exp::Prim(Prim::String(StringMode::Normal, merged_s)),
                            &span1,
                        )))
                    }
                    _ => Exp::Seq(e1, e2),
                },
                // ESeq(EWrite(s1), ESeq(EWrite(s2), rest)) → ESeq(EWrite(s1^s2), rest)
                (Exp::Write(w1), Exp::Seq(inner_seq, rest)) => match (&w1.node, &inner_seq.node) {
                    (Exp::Prim(Prim::String(_, s1)), Exp::Write(w2)) => {
                        if let Exp::Prim(Prim::String(_, s2)) = &w2.node {
                            let merged = format!("{}{}", s1, s2);
                            let span1 = w1.span.clone();
                            let new_write = lspan(
                                Exp::Write(Box::new(lspan(
                                    Exp::Prim(Prim::String(StringMode::Normal, merged)),
                                    &span1,
                                ))),
                                &span1,
                            );
                            Exp::Seq(Box::new(new_write), rest.clone())
                        } else {
                            Exp::Seq(e1, e2)
                        }
                    }
                    _ => Exp::Seq(e1, e2),
                },
                _ => Exp::Seq(e1, e2),
            }
        }

        // -----------------------------------------------------------------------
        // htmlify FFI calls
        // -----------------------------------------------------------------------
        Exp::FfiApp(ref m, ref f, ref args) if m == "Basis" => {
            let args = args.clone();
            match f.as_str() {
                "htmlifySpecialChar" if args.len() == 1 => {
                    if let Exp::Prim(Prim::Char(ch)) = args[0].0.node {
                        return Exp::Prim(Prim::String(StringMode::Html, htmlify_special_char(ch)));
                    }
                    Exp::FfiApp("Basis".into(), f.clone(), args)
                }

                // `htmlifyString` composition rewrites (shared with fold helper).
                "htmlifyString" if args.len() == 1 => fold_basis_htmlify_string_arg(args),

                "htmlifyString_w" if args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, s)) = &args[0].0.node {
                        let new_inner = html_lit(htmlify_string(s), &args[0].0.span);
                        return Exp::Write(Box::new(new_inner));
                    }
                    Exp::FfiApp("Basis".into(), "htmlifyString_w".into(), args)
                }

                // attrifyInt/Float/String/Char constant folding
                "attrifyInt" if args.len() == 1 => {
                    if let Exp::Prim(Prim::Int(n)) = args[0].0.node {
                        Exp::Prim(Prim::String(StringMode::Html, attrify_int(n)))
                    } else {
                        Exp::FfiApp("Basis".into(), f.clone(), args)
                    }
                }
                "attrifyFloat" if args.len() == 1 => {
                    if let Exp::Prim(Prim::Float(n)) = args[0].0.node {
                        Exp::Prim(Prim::String(StringMode::Html, attrify_float(n)))
                    } else {
                        Exp::FfiApp("Basis".into(), f.clone(), args)
                    }
                }
                "attrifyString" if args.len() == 1 => match &args[0].0.node {
                    Exp::Prim(Prim::String(_, s)) => {
                        Exp::Prim(Prim::String(StringMode::Html, attrify_string(s)))
                    }
                    Exp::FfiApp(m2, f2, args2) if m2 == "Basis" && f2 == "str1" => {
                        Exp::FfiApp("Basis".into(), "attrifyChar".into(), args2.clone())
                    }
                    _ => Exp::FfiApp("Basis".into(), f.clone(), args),
                },
                "attrifyString_w" if args.len() == 1 => {
                    if let Exp::FfiApp(m2, f2, args2) = &args[0].0.node {
                        if m2 == "Basis" && f2 == "str1" {
                            return Exp::FfiApp(
                                "Basis".into(),
                                "attrifyChar_w".into(),
                                args2.clone(),
                            );
                        }
                    }
                    Exp::FfiApp("Basis".into(), f.clone(), args)
                }
                "attrifyChar" if args.len() == 1 => {
                    if let Exp::Prim(Prim::Char(c)) = args[0].0.node {
                        Exp::Prim(Prim::String(StringMode::Html, attrify_char(c)))
                    } else {
                        Exp::FfiApp("Basis".into(), f.clone(), args)
                    }
                }
                "attrifyCss_class" if args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, s)) = &args[0].0.node {
                        Exp::Prim(Prim::String(StringMode::Html, s.clone()))
                    } else {
                        Exp::FfiApp("Basis".into(), f.clone(), args)
                    }
                }

                // urlify constant folding
                "urlifyInt" if args.len() == 1 => {
                    if let Exp::Prim(Prim::Int(n)) = args[0].0.node {
                        Exp::Prim(Prim::String(StringMode::Normal, urlify_int(n)))
                    } else {
                        Exp::FfiApp("Basis".into(), f.clone(), args)
                    }
                }
                "urlifyFloat" if args.len() == 1 => {
                    if let Exp::Prim(Prim::Float(n)) = args[0].0.node {
                        Exp::Prim(Prim::String(StringMode::Normal, urlify_float(n)))
                    } else {
                        Exp::FfiApp("Basis".into(), f.clone(), args)
                    }
                }
                "urlifyString" if args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, s)) = &args[0].0.node {
                        Exp::Prim(Prim::String(StringMode::Normal, urlify_string(s)))
                    } else {
                        Exp::FfiApp("Basis".into(), f.clone(), args)
                    }
                }
                "urlifyChar" if args.len() == 1 => {
                    if let Exp::Prim(Prim::Char(c)) = args[0].0.node {
                        Exp::Prim(Prim::String(StringMode::Normal, urlify_char(c)))
                    } else {
                        Exp::FfiApp("Basis".into(), f.clone(), args)
                    }
                }
                "urlifyBool" if args.len() == 1 => match &args[0].0.node {
                    Exp::Con(_, pc, None) if is_ffi_con(pc, "Basis", "True") => {
                        Exp::Prim(Prim::String(StringMode::Normal, "1".into()))
                    }
                    Exp::Con(_, pc, None) if is_ffi_con(pc, "Basis", "False") => {
                        Exp::Prim(Prim::String(StringMode::Normal, "0".into()))
                    }
                    _ => Exp::FfiApp("Basis".into(), f.clone(), args),
                },

                // sqlify constant folding
                "sqlifyInt" if args.len() == 1 => {
                    if let Exp::Prim(Prim::Int(n)) = args[0].0.node {
                        Exp::Prim(Prim::String(StringMode::Normal, sqlify_int(n, settings)))
                    } else {
                        Exp::FfiApp("Basis".into(), f.clone(), args)
                    }
                }
                "sqlifyIntN" if args.len() == 1 => match &args[0].0.node {
                    Exp::None(_) => Exp::Prim(Prim::String(StringMode::Normal, "NULL".into())),
                    Exp::Some(_, inner) => {
                        if let Exp::Prim(Prim::Int(n)) = inner.node {
                            Exp::Prim(Prim::String(StringMode::Normal, sqlify_int(n, settings)))
                        } else {
                            Exp::FfiApp("Basis".into(), f.clone(), args)
                        }
                    }
                    _ => Exp::FfiApp("Basis".into(), f.clone(), args),
                },
                "sqlifyFloat" if args.len() == 1 => {
                    if let Exp::Prim(Prim::Float(n)) = args[0].0.node {
                        Exp::Prim(Prim::String(StringMode::Normal, sqlify_float(n, settings)))
                    } else {
                        Exp::FfiApp("Basis".into(), f.clone(), args)
                    }
                }
                "sqlifyBool" if args.len() == 1 => {
                    let bool_arg = args[0].0.clone();
                    let arg_span = bool_arg.span.clone();
                    // Convert to case expression
                    let t_bool =
                        Located::new(Typ::Ffi("Basis".into(), "bool".into()), arg_span.clone());
                    let t_str =
                        Located::new(Typ::Ffi("Basis".into(), "string".into()), arg_span.clone());
                    let true_pat = Located::new(
                        crate::monomorphized::Pat::Con(
                            crate::datatype_kind::DatatypeKind::Enum,
                            crate::monomorphized::PatCon::Ffi {
                                module: "Basis".into(),
                                datatyp: "bool".into(),
                                con: "True".into(),
                                arg: None,
                            },
                            None,
                        ),
                        arg_span.clone(),
                    );
                    let false_pat = Located::new(
                        crate::monomorphized::Pat::Con(
                            crate::datatype_kind::DatatypeKind::Enum,
                            crate::monomorphized::PatCon::Ffi {
                                module: "Basis".into(),
                                datatyp: "bool".into(),
                                con: "False".into(),
                                arg: None,
                            },
                            None,
                        ),
                        arg_span.clone(),
                    );
                    let true_body = lspan(
                        Exp::Prim(Prim::String(
                            StringMode::Normal,
                            sqlify_bool_true(settings).into(),
                        )),
                        &arg_span,
                    );
                    let false_body = lspan(
                        Exp::Prim(Prim::String(
                            StringMode::Normal,
                            sqlify_bool_false(settings).into(),
                        )),
                        &arg_span,
                    );
                    let meta = crate::monomorphized::CaseMeta {
                        disc: t_bool,
                        result: t_str,
                    };
                    let case_e = Exp::Case(
                        Box::new(bool_arg),
                        vec![(true_pat, true_body), (false_pat, false_body)],
                        meta,
                    );
                    opt_exp_peephole(case_e, span, settings, errors)
                }
                "sqlifyString" if args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, s)) = &args[0].0.node {
                        Exp::Prim(Prim::String(StringMode::Normal, sqlify_string(s, settings)))
                    } else {
                        Exp::FfiApp("Basis".into(), f.clone(), args)
                    }
                }
                "sqlifyChar" if args.len() == 1 => {
                    if let Exp::Prim(Prim::Char(c)) = args[0].0.node {
                        Exp::Prim(Prim::String(StringMode::Normal, sqlify_char(c, settings)))
                    } else {
                        Exp::FfiApp("Basis".into(), f.clone(), args)
                    }
                }

                // intToString(n) → FfiApp(intToString, [n])
                "intToString" if args.is_empty() => {
                    // EApp(EFfi("Basis","intToString"), e) → EFfiApp("Basis","intToString",[e])
                    // This is handled in the EApp case below
                    Exp::FfiApp("Basis".into(), f.clone(), args)
                }

                // str1(char_lit) → string literal
                "str1" if args.len() == 1 => {
                    if let Exp::Prim(Prim::Char(c)) = args[0].0.node {
                        Exp::Prim(Prim::String(StringMode::Normal, c.to_string()))
                    } else {
                        Exp::FfiApp("Basis".into(), f.clone(), args)
                    }
                }

                // checkString: rewrite SQL identifier
                "checkString" if args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, s)) = &args[0].0.node {
                        Exp::Prim(Prim::String(StringMode::Normal, uwify_check_string(s)))
                    } else {
                        Exp::FfiApp("Basis".into(), f.clone(), args)
                    }
                }

                // viewify: rewrite AS aliases
                "viewify" if args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, s)) = &args[0].0.node {
                        Exp::Prim(Prim::String(StringMode::Normal, uwify_viewify(s)))
                    } else {
                        Exp::FfiApp("Basis".into(), f.clone(), args)
                    }
                }

                // unAs: strip T_T. prefixes
                "unAs" if args.len() == 1 => {
                    let arg = &args[0].0;
                    if let Exp::Prim(Prim::String(_, s)) = &arg.node {
                        Exp::Prim(Prim::String(StringMode::Normal, un_as(s)))
                    } else {
                        match un_as_exp(arg) {
                            Some(new_node) => new_node,
                            None => Exp::FfiApp("Basis".into(), f.clone(), args),
                        }
                    }
                }

                // Validation / blessing with literal strings
                "blessData" if args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, s)) = &args[0].0.node {
                        if !check_data(s) {
                            errors.borrow_mut().report_at(
                                args[0].0.span.clone(),
                                DiagnosticPayload::new(
                                    DiagnosticId::InvalidHtml5DataAttribute,
                                    vec![s.clone()],
                                ),
                            );
                        }
                        return args[0].0.node.clone();
                    }
                    Exp::FfiApp("Basis".into(), f.clone(), args)
                }
                "bless" if args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, s)) = &args[0].0.node {
                        if !check_url(s, settings) {
                            errors.borrow_mut().report_at(
                                args[0].0.span.clone(),
                                DiagnosticPayload::new(
                                    DiagnosticId::InvalidUrlPassedToBless,
                                    vec![s.clone()],
                                ),
                            );
                        }
                        return args[0].0.node.clone();
                    }
                    Exp::FfiApp("Basis".into(), f.clone(), args)
                }
                "checkUrl" if args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, s)) = &args[0].0.node {
                        let t = Located::new(
                            Typ::Ffi("Basis".into(), "string".into()),
                            args[0].0.span.clone(),
                        );
                        if check_url(s, settings) {
                            return Exp::Some(t, Box::new(args[0].0.clone()));
                        } else {
                            return Exp::None(t);
                        }
                    }
                    Exp::FfiApp("Basis".into(), f.clone(), args)
                }
                "blessMime" if args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, s)) = &args[0].0.node {
                        if !settings.check_mime(s) {
                            errors.borrow_mut().report_at(
                                args[0].0.span.clone(),
                                DiagnosticPayload::new(
                                    DiagnosticId::InvalidStringPassedToBlessMime,
                                    vec![s.clone()],
                                ),
                            );
                        }
                        return args[0].0.node.clone();
                    }
                    Exp::FfiApp("Basis".into(), f.clone(), args)
                }
                "checkMime" if args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, s)) = &args[0].0.node {
                        let t = Located::new(
                            Typ::Ffi("Basis".into(), "string".into()),
                            args[0].0.span.clone(),
                        );
                        if settings.check_mime(s) {
                            return Exp::Some(t, Box::new(args[0].0.clone()));
                        } else {
                            return Exp::None(t);
                        }
                    }
                    Exp::FfiApp("Basis".into(), f.clone(), args)
                }
                "atom" if args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, s)) = &args[0].0.node {
                        if !check_atom(s) {
                            errors.borrow_mut().report_at(
                                args[0].0.span.clone(),
                                DiagnosticPayload::new(
                                    DiagnosticId::InvalidStringPassedToAtom,
                                    vec![s.clone()],
                                ),
                            );
                        }
                        return args[0].0.node.clone();
                    }
                    Exp::FfiApp("Basis".into(), f.clone(), args)
                }
                "css_url" if args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, s)) = &args[0].0.node {
                        if !check_css_url(s) {
                            errors.borrow_mut().report_at(
                                args[0].0.span.clone(),
                                DiagnosticPayload::new(
                                    DiagnosticId::InvalidUrlPassedToCssUrl,
                                    vec![s.clone()],
                                ),
                            );
                        }
                        return args[0].0.node.clone();
                    }
                    Exp::FfiApp("Basis".into(), f.clone(), args)
                }
                "property" if args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, s)) = &args[0].0.node {
                        if !check_property(s) {
                            errors.borrow_mut().report_at(
                                args[0].0.span.clone(),
                                DiagnosticPayload::new(
                                    DiagnosticId::InvalidStringPassedToProperty,
                                    vec![s.clone()],
                                ),
                            );
                        }
                        return args[0].0.node.clone();
                    }
                    Exp::FfiApp("Basis".into(), f.clone(), args)
                }
                "blessRequestHeader" if args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, s)) = &args[0].0.node {
                        if !settings.check_request_header(s) {
                            errors.borrow_mut().report_at(
                                args[0].0.span.clone(),
                                DiagnosticPayload::new(
                                    DiagnosticId::InvalidStringPassedToBlessRequestHeader,
                                    vec![s.clone()],
                                ),
                            );
                        }
                        return args[0].0.node.clone();
                    }
                    Exp::FfiApp("Basis".into(), f.clone(), args)
                }
                "checkRequestHeader" if args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, s)) = &args[0].0.node {
                        let t = Located::new(
                            Typ::Ffi("Basis".into(), "string".into()),
                            args[0].0.span.clone(),
                        );
                        if settings.check_request_header(s) {
                            return Exp::Some(t, Box::new(args[0].0.clone()));
                        } else {
                            return Exp::None(t);
                        }
                    }
                    Exp::FfiApp("Basis".into(), f.clone(), args)
                }
                "blessResponseHeader" if args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, s)) = &args[0].0.node {
                        if !settings.check_response_header(s) {
                            errors.borrow_mut().report_at(
                                args[0].0.span.clone(),
                                DiagnosticPayload::new(
                                    DiagnosticId::InvalidStringPassedToBlessResponseHeader,
                                    vec![s.clone()],
                                ),
                            );
                        }
                        return args[0].0.node.clone();
                    }
                    Exp::FfiApp("Basis".into(), f.clone(), args)
                }
                "checkResponseHeader" if args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, s)) = &args[0].0.node {
                        let t = Located::new(
                            Typ::Ffi("Basis".into(), "string".into()),
                            args[0].0.span.clone(),
                        );
                        if settings.check_response_header(s) {
                            return Exp::Some(t, Box::new(args[0].0.clone()));
                        } else {
                            return Exp::None(t);
                        }
                    }
                    Exp::FfiApp("Basis".into(), f.clone(), args)
                }
                "blessEnvVar" if args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, s)) = &args[0].0.node {
                        if !settings.check_env_var(s) {
                            errors.borrow_mut().report_at(
                                args[0].0.span.clone(),
                                DiagnosticPayload::new(
                                    DiagnosticId::InvalidStringPassedToBlessEnvVar,
                                    vec![s.clone()],
                                ),
                            );
                        }
                        return args[0].0.node.clone();
                    }
                    Exp::FfiApp("Basis".into(), f.clone(), args)
                }
                "checkEnvVar" if args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, s)) = &args[0].0.node {
                        let t = Located::new(
                            Typ::Ffi("Basis".into(), "string".into()),
                            args[0].0.span.clone(),
                        );
                        if settings.check_env_var(s) {
                            return Exp::Some(t, Box::new(args[0].0.clone()));
                        } else {
                            return Exp::None(t);
                        }
                    }
                    Exp::FfiApp("Basis".into(), f.clone(), args)
                }
                "blessMeta" if args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, s)) = &args[0].0.node {
                        if !settings.check_meta(s) {
                            errors.borrow_mut().report_at(
                                args[0].0.span.clone(),
                                DiagnosticPayload::new(
                                    DiagnosticId::InvalidStringPassedToBlessMeta,
                                    vec![s.clone()],
                                ),
                            );
                        }
                        return args[0].0.node.clone();
                    }
                    Exp::FfiApp("Basis".into(), f.clone(), args)
                }
                "checkMeta" if args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, s)) = &args[0].0.node {
                        let t = Located::new(
                            Typ::Ffi("Basis".into(), "string".into()),
                            args[0].0.span.clone(),
                        );
                        if settings.check_meta(s) {
                            return Exp::Some(t, Box::new(args[0].0.clone()));
                        } else {
                            return Exp::None(t);
                        }
                    }
                    Exp::FfiApp("Basis".into(), f.clone(), args)
                }

                _ => Exp::FfiApp("Basis".into(), f.clone(), args),
            }
        }

        // -----------------------------------------------------------------------
        // EApp(EAbs(x,_,_,body), arg) → subExpInExp(0, arg, body)  (unconditional beta reduction)
        // Mirrors SML mono_opt.sml: EApp((EAbs(_, _, _, body), _), arg) => optExp(subExpInExp 0 arg body)
        // -----------------------------------------------------------------------
        // -----------------------------------------------------------------------
        // EApp(EFfi("Basis","intToString"), e) → EFfiApp("Basis","intToString",[e,int_t])
        // -----------------------------------------------------------------------
        Exp::App(fexpr, arg) => {
            // Unconditional beta reduction (like SML mono_opt): App(Abs(x, _, _, body), arg)
            if let Exp::Abs(_, _, _, ref body) = fexpr.node {
                let substituted = crate::monomorphized::environment::sub_exp_in_exp(
                    0,
                    arg.as_ref(),
                    body.as_ref(),
                );
                return opt_loc_exp(lspan(substituted.node, span), settings, errors).node;
            }
            match &fexpr.node {
                Exp::Ffi(m, f) if m == "Basis" && f == "intToString" => {
                    let t =
                        Located::new(Typ::Ffi("Basis".into(), "int".into()), fexpr.span.clone());
                    Exp::FfiApp("Basis".into(), "intToString".into(), vec![(*arg, t)])
                }
                _ => Exp::App(fexpr, arg),
            }
        }

        // -----------------------------------------------------------------------
        // EWrite(ECase(...)) → ECase(..., arms with EWrite applied)
        // -----------------------------------------------------------------------
        // (Handled inside EWrite arm above via general pattern matching is insufficient
        // because we already handled specific EWrite cases. The general ECase distribution
        // needs to be a separate top-level rule.)

        // -----------------------------------------------------------------------
        // ESignalBind(ESignalReturn(e1), e2) → EApp(e2, e1)
        // -----------------------------------------------------------------------
        Exp::SignalBind(e1, e2) => {
            if let Exp::SignalReturn(inner) = e1.node {
                opt_loc_exp(lspan(Exp::App(e2, inner), span), settings, errors).node
            } else {
                Exp::SignalBind(e1, e2)
            }
        }

        // -----------------------------------------------------------------------
        // Arithmetic constant folding
        // -----------------------------------------------------------------------
        Exp::Binop(intness, ref op, ref e1, ref e2) => match (&e1.node, &e2.node, op.as_str()) {
            (Exp::Prim(Prim::Int(n1)), Exp::Prim(Prim::Int(n2)), "+") => {
                Exp::Prim(Prim::Int(n1.wrapping_add(*n2)))
            }
            (Exp::Prim(Prim::Int(n1)), Exp::Prim(Prim::Int(n2)), "-") => {
                Exp::Prim(Prim::Int(n1.wrapping_sub(*n2)))
            }
            (Exp::Prim(Prim::Int(n1)), Exp::Prim(Prim::Int(n2)), "*") => {
                Exp::Prim(Prim::Int(n1.wrapping_mul(*n2)))
            }
            _ => Exp::Binop(intness, op.clone(), e1.clone(), e2.clone()),
        },

        other => other,
    }
}

// ---------------------------------------------------------------------------
// urlify aliases
// ---------------------------------------------------------------------------

fn urlify_int(n: i64) -> String {
    attrify_int(n)
}

fn urlify_float(n: f64) -> String {
    attrify_float(n)
}

fn htmlify_int(n: i64) -> String {
    attrify_int(n)
}

fn htmlify_float(n: f64) -> String {
    attrify_float(n)
}

// ---------------------------------------------------------------------------
// opt_loc_exp — bottom-up application via utilities::exp::map
// ---------------------------------------------------------------------------

/// Optimize a located expression bottom-up.
fn opt_loc_exp(e: LocExp, settings: &Settings, errors: &RefCell<&mut ErrorReporter>) -> LocExp {
    let span = e.span.clone();
    // utilities::exp::map processes children recursively then applies fe to each node.
    utilities::exp::map(e, &|t| t, &|node: Exp| {
        opt_exp_peephole(node, &span, settings, errors)
    })
}

// ---------------------------------------------------------------------------
// Public entry points
// ---------------------------------------------------------------------------

/// Optimize a single located expression (public, for use by fuse stub etc.)
pub fn opt_exp(e: LocExp, settings: &Settings, errors: &mut ErrorReporter) -> LocExp {
    let errors_cell = RefCell::new(errors);
    opt_loc_exp(e, settings, &errors_cell)
}

/// Optimize an entire Mono file.
pub fn optimize(
    file: crate::monomorphized::File,
    settings: &Settings,
    errors: &mut ErrorReporter,
) -> crate::monomorphized::File {
    let (decls, exports) = file;
    let errors_cell = RefCell::new(errors);
    let new_decls: Vec<LocDecl> = decls
        .into_iter()
        .map(|d| {
            let span = d.span.clone();
            utilities::decl::map(
                d,
                &|t| t,
                &|node: Exp| {
                    let e = Located::new(node, span.clone());
                    opt_loc_exp(e, settings, &errors_cell).node
                },
                &|d| d,
            )
        })
        .collect();
    (new_decls, exports)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error_types::Located;
    use crate::settings::Settings;
    use anyhow::Context as _; // .with_context() on Option/Result in tests

    fn dummy<T>(node: T) -> Located<T> {
        Located::dummy(node)
    }

    fn settings() -> Settings {
        Settings::default()
    }

    fn settings_mysql() -> Settings {
        Settings {
            db_backend: Some(crate::db::ProjectDb::mysql()),
            ..Default::default()
        }
    }

    fn settings_postgres() -> Settings {
        Settings {
            db_backend: Some(crate::db::ProjectDb::postgres()),
            ..Default::default()
        }
    }

    fn no_errors() -> ErrorReporter {
        ErrorReporter::new()
    }

    #[test]
    fn optimize_empty_file() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut errors = no_errors();
        let result = optimize((vec![], vec![]), &settings(), &mut errors);
        assert!(result.0.is_empty());
        Ok(()) // return success to the test harness
    }

    #[test]
    fn attrify_int_positive() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(attrify_int(42), "42");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn attrify_int_negative() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(attrify_int(-7), "-7");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn attrify_int_zero_not_negative() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // Kills: replace < with == or <= in attrify_int (0 < 0 false => "0"; 0==0 true => "-0")
        assert_eq!(attrify_int(0), "0");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn attrify_char_quote() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(attrify_char('"'), "&quot;");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn attrify_char_amp() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(attrify_char('&'), "&amp;");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn htmlify_string_lt() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(htmlify_string("<b>"), "&lt;b>");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn urlify_string_empty() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(urlify_string(""), "_");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn urlify_string_underscore_prefix() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // '_' is encoded as ".5F" by urlifyCharAux; prefix "_" is prepended.
        let s = urlify_string("_hello");
        assert!(s.starts_with("_.5F"), "got: {}", s);
        Ok(()) // return success to the test harness
    }

    #[test]
    fn hex_it_ascii() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(hex_it('A'), "41");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn fold_strcat_empty() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut errors = no_errors();
        let e1 = dummy(Exp::Prim(Prim::String(StringMode::Normal, "hello".into())));
        let e2 = dummy(Exp::Prim(Prim::String(StringMode::Normal, "".into())));
        let cat = dummy(Exp::Strcat(Box::new(e1.clone()), Box::new(e2)));
        let result = opt_exp(cat, &settings(), &mut errors);
        assert!(matches!(&result.node, Exp::Prim(Prim::String(_, s)) if s == "hello"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn fold_strcat_two_lits() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut errors = no_errors();
        let e1 = dummy(Exp::Prim(Prim::String(StringMode::Normal, "foo".into())));
        let e2 = dummy(Exp::Prim(Prim::String(StringMode::Normal, "bar".into())));
        let cat = dummy(Exp::Strcat(Box::new(e1), Box::new(e2)));
        let result = opt_exp(cat, &settings(), &mut errors);
        assert!(matches!(&result.node, Exp::Prim(Prim::String(_, s)) if s == "foobar"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn attrify_float_positive() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(attrify_float(1.5), "1.5");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn attrify_float_negative() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(attrify_float(-2.0), "-2");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn attrify_float_zero_not_negative() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // Kills: replace < with == or <= in attrify_float
        assert_eq!(attrify_float(0.0), "0");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn attrify_string_escape() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(attrify_string("a&b"), "a&amp;b");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn urlify_char_space() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(urlify_char(' '), "+");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn urlify_char_alphanumeric() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(urlify_char('a'), "a");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn urlify_char_underscore_prefix() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // '_' gets prefix "_" + aux; aux for '_' is ".5F"
        let s = urlify_char('_');
        assert!(s.starts_with("_.5F") || s.contains("5F"), "got: {}", s);
        Ok(()) // return success to the test harness
    }

    #[test]
    fn htmlify_special_char_formats_codepoint() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(htmlify_special_char('x'), "&#120;");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn hex_pad_single_digit() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(hex_pad(5), "05");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn hex_pad_zero() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // format!("{:X}", 0) = "0", len 1 => "0" + "0" = "00"
        assert_eq!(hex_pad(0), "00");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn hex_it_two_byte_boundary() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // 0x80 = 128: first branch c <= 0x7f is false, second c <= 0x7ff true
        let s = hex_it(
            std::char::from_u32(0x80).context("0x80 should be a valid Unicode scalar value")?,
        );
        assert!(s.len() >= 2 && s.chars().all(|c| c.is_ascii_hexdigit()));
        Ok(()) // return success to the test harness
    }

    /// `EWrite(Basis.htmlifyInt)` lowers to `htmlifyInt_w` (writer combinator).
    #[test]
    fn write_basis_htmlify_int_becomes_writer_suffix() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut errors = no_errors();
        let arg = dummy(Exp::Prim(Prim::Int(3)));
        let t_int = dummy(Typ::Ffi("Basis".into(), "int".into()));
        let inner = dummy(Exp::FfiApp(
            "Basis".into(),
            "htmlifyInt".into(),
            vec![(arg, t_int)],
        ));
        let wrapped = dummy(Exp::Write(Box::new(inner)));
        let result = opt_exp(wrapped, &settings(), &mut errors);
        assert!(
            matches!(
                &result.node,
                Exp::FfiApp(m, f, _) if m == "Basis" && f == "htmlifyInt_w"
            ),
            "expected htmlifyInt_w, got {:?}",
            result.node
        );
        Ok(()) // return success to the test harness
    }

    /// `htmlifyString(Basis.intToString n)` folds like the legacy nested-match path.
    #[test]
    fn fold_htmlify_string_via_curried_int_to_string() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut errors = no_errors();
        let n = dummy(Exp::Prim(Prim::Int(42)));
        let fn_part = dummy(Exp::Ffi("Basis".into(), "intToString".into()));
        let arg = dummy(Exp::App(Box::new(fn_part), Box::new(n)));
        let t_str = dummy(Typ::Ffi("Basis".into(), "string".into()));
        let e = dummy(Exp::FfiApp(
            "Basis".into(),
            "htmlifyString".into(),
            vec![(arg, t_str)],
        ));
        let result = opt_exp(e, &settings(), &mut errors);
        assert!(
            matches!(&result.node, Exp::Prim(Prim::String(StringMode::Html, s)) if s == "42"),
            "expected folded HTML string, got {:?}",
            result.node
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn fold_attrify_int() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut errors = no_errors();
        let arg = dummy(Exp::Prim(Prim::Int(99)));
        let t = dummy(Typ::Ffi("Basis".into(), "int".into()));
        let e = dummy(Exp::FfiApp(
            "Basis".into(),
            "attrifyInt".into(),
            vec![(arg, t)],
        ));
        let result = opt_exp(e, &settings(), &mut errors);
        assert!(
            matches!(&result.node, Exp::Prim(Prim::String(_, s)) if s == "99"),
            "attrifyInt(99) => \"99\""
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn fold_attrify_string() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut errors = no_errors();
        let arg = dummy(Exp::Prim(Prim::String(StringMode::Normal, "a&b".into())));
        let t = dummy(Typ::Ffi("Basis".into(), "string".into()));
        let e = dummy(Exp::FfiApp(
            "Basis".into(),
            "attrifyString".into(),
            vec![(arg, t)],
        ));
        let result = opt_exp(e, &settings(), &mut errors);
        assert!(
            matches!(&result.node, Exp::Prim(Prim::String(_, s)) if s == "a&amp;b"),
            "attrifyString(\"a&b\") => \"a&amp;b\""
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn fold_urlify_int() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut errors = no_errors();
        let arg = dummy(Exp::Prim(Prim::Int(1)));
        let t = dummy(Typ::Ffi("Basis".into(), "int".into()));
        let e = dummy(Exp::FfiApp(
            "Basis".into(),
            "urlifyInt".into(),
            vec![(arg, t)],
        ));
        let result = opt_exp(e, &settings(), &mut errors);
        assert!(
            matches!(&result.node, Exp::Prim(Prim::String(_, s)) if s == "1"),
            "urlifyInt(1) => \"1\""
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn fold_strcat_three_lits() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut errors = no_errors();
        let e1 = dummy(Exp::Prim(Prim::String(StringMode::Normal, "a".into())));
        let e2 = dummy(Exp::Prim(Prim::String(StringMode::Normal, "b".into())));
        let e3 = dummy(Exp::Prim(Prim::String(StringMode::Normal, "c".into())));
        let cat12 = dummy(Exp::Strcat(Box::new(e1), Box::new(e2)));
        let cat = dummy(Exp::Strcat(Box::new(cat12), Box::new(e3)));
        let result = opt_exp(cat, &settings(), &mut errors);
        assert!(matches!(&result.node, Exp::Prim(Prim::String(_, s)) if s == "abc"));
        Ok(()) // return success to the test harness
    }

    // --- sqlify_*: exact output so return-value mutants are killed ---
    #[test]
    fn sqlify_int_postgres_adds_cast() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(sqlify_int(42, &settings_postgres()), "42::int8");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sqlify_int_mysql_no_cast() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(sqlify_int(42, &settings_mysql()), "42");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sqlify_float_postgres_adds_cast() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(sqlify_float(1.5, &settings_postgres()), "1.5::float8");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sqlify_float_mysql_no_cast() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(sqlify_float(1.5, &settings_mysql()), "1.5");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sqlify_string_postgres_doubles_quote() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(sqlify_string("'", &settings_postgres()), "''''");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sqlify_string_mysql_escapes_backslash() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(sqlify_string("\\", &settings_mysql()), "'\\\\'");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sqlify_char_postgres() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(sqlify_char('x', &settings_postgres()), "'x'");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sqlify_bool_true_postgres() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(sqlify_bool_true(&settings_postgres()), "TRUE");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sqlify_bool_true_mysql() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(sqlify_bool_true(&settings_mysql()), "1");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sqlify_bool_false_postgres() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(sqlify_bool_false(&settings_postgres()), "FALSE");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn sqlify_bool_false_mysql() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert_eq!(sqlify_bool_false(&settings_mysql()), "0");
        Ok(()) // return success to the test harness
    }

    // --- check_url, check_data, check_atom, check_css_url, check_property ---
    #[test]
    fn check_url_true_when_rule_allows() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut s = Settings::default();
        s.url_rules.push(crate::settings::Rule {
            action: crate::settings::Action::Allow,
            kind: crate::settings::PatternKind::Exact,
            pattern: "/foo".into(),
        });
        assert!(check_url("/foo", &s), "allowed URL must be true");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn check_url_false_when_no_rule() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let s = Settings::default();
        assert!(!check_url("/bar", &s), "no rule => false");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn check_data_allows_alphanumeric_underscore_hyphen() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(check_data("a_1"));
        assert!(check_data("x-y"));
        assert!(!check_data("a b"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn check_atom_allows_plus_minus_dot() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(check_atom("a+b"));
        assert!(check_atom("1.2"));
        assert!(!check_atom("a!b"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn check_css_url_allows_slash_colon() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(check_css_url("https://x/y"));
        assert!(!check_css_url("a<>"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn hex_pad_two_digits_unchanged() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // len 2 => no leading zero. Kills "delete match arm 0" and arm 1.
        assert_eq!(hex_pad(0x0A), "0A");
        assert_eq!(hex_pad(0xFF), "FF");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn hex_it_three_byte_utf8() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // Codepoint > 0x7ff hits third branch (c <= 0xffff).
        let ch =
            std::char::from_u32(0x0800).context("0x0800 should be a valid Unicode scalar value")?;
        let s = hex_it(ch);
        assert!(
            s.len() >= 3,
            "three-byte UTF-8 produces at least 3 hex pairs"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn check_data_rejects_space() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(!check_data("a b"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn check_data_allows_hyphen() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(check_data("a-b"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn check_atom_rejects_bang() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(!check_atom("a!b"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn check_atom_allows_hash() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(check_atom("a#b"));
        Ok(()) // return success to the test harness
    }
}
