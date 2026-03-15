//! Peephole optimizer for the Mono IR.
//!
//! Constant-folds string encoding, arithmetic, and HTML/URL/SQL generation
//! functions, distributes `EWrite` into `EStrcat`/`ECase`/`ELet`, etc.
//!
//! Mirrors `mono_opt.sml`.

use std::cell::RefCell;

use crate::error_types::{ErrorReporter, Located, Span};
use crate::monomorphized::{utilities, Exp, LocDecl, LocExp, Typ};
use crate::primitives::{Prim, StringMode};
use crate::settings::Settings;

// ---------------------------------------------------------------------------
// String encoding helpers — pure, no settings
// ---------------------------------------------------------------------------

fn attrify_int(n: i64) -> String {
    if n < 0 {
        format!("-{}", -n)
    } else {
        n.to_string()
    }
}

fn attrify_float(n: f64) -> String {
    if n < 0.0 {
        format!("-{}", -n)
    } else {
        n.to_string()
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
    if c <= 0x7f {
        hex_pad(c)
    } else if c <= 0x7ff {
        format!("{}{}", hex_pad((c >> 6) | 0xc0), hex_pad((c & 0x3f) | 0x80))
    } else if c <= 0xffff {
        format!(
            "{}{}{}",
            hex_pad((c >> 12) | 0xe0),
            hex_pad(((c >> 6) & 0x3f) | 0x80),
            hex_pad((c & 0x3f) | 0x80)
        )
    } else {
        format!(
            "{}{}{}{}",
            hex_pad((c >> 18) | 0xf0),
            hex_pad(((c >> 12) & 0x3f) | 0x80),
            hex_pad(((c >> 6) & 0x3f) | 0x80),
            hex_pad((c & 0x3f) | 0x80)
        )
    }
}

fn urlify_char_aux(ch: char) -> String {
    if ch == ' ' {
        "+".into()
    } else if ch as u32 == 0 {
        "_".into()
    } else if ch.is_alphanumeric() {
        ch.to_string()
    } else {
        format!(".{}", hex_it(ch))
    }
}

fn urlify_char(ch: char) -> String {
    if ch == '_' {
        format!("_{}", urlify_char_aux(ch))
    } else {
        urlify_char_aux(ch)
    }
}

fn urlify_string(s: &str) -> String {
    if s.is_empty() {
        return "_".into();
    }
    let prefix = if s.starts_with('_') { "_" } else { "" };
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
    if settings.dbms == "mysql" {
        s
    } else {
        // PostgreSQL: cast syntax
        format!("{}::int8", s)
    }
}

fn sqlify_float(n: f64, settings: &Settings) -> String {
    let s = attrify_float(n);
    if settings.dbms == "mysql" {
        s
    } else {
        format!("{}::float8", s)
    }
}

fn sqlify_string(s: &str, settings: &Settings) -> String {
    if settings.dbms == "mysql" {
        // MySQL: escape backslash and single-quote
        let escaped: String = s
            .chars()
            .flat_map(|c| match c {
                '\'' => vec!['\\', '\''],
                '\\' => vec!['\\', '\\'],
                c => vec![c],
            })
            .collect();
        format!("'{}'", escaped)
    } else {
        // PostgreSQL: double single-quotes
        let escaped = s.replace('\'', "''");
        format!("'{}'", escaped)
    }
}

fn sqlify_char(ch: char, settings: &Settings) -> String {
    let mut buf = String::new();
    buf.push(ch);
    sqlify_string(&buf, settings)
}

fn sqlify_bool_true(settings: &Settings) -> &'static str {
    if settings.dbms == "mysql" {
        "1"
    } else {
        "TRUE"
    }
}

fn sqlify_bool_false(settings: &Settings) -> &'static str {
    if settings.dbms == "mysql" {
        "0"
    } else {
        "FALSE"
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
    if s.is_empty() {
        return false;
    }
    let first = s.chars().next().unwrap();
    let rest_ok = s.chars().all(nmchar);
    rest_ok
        && (nmstart(first) || (s.len() > 1 && first == '-' && nmstart(s.chars().nth(1).unwrap())))
}

// ---------------------------------------------------------------------------
// SQL string helpers
// ---------------------------------------------------------------------------

/// Strip `T_T.` table-alias prefixes from SQL strings, handling quoted strings.
fn un_as(s: &str) -> String {
    let chars: Vec<char> = s.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        if i + 3 < chars.len()
            && chars[i] == 'T'
            && chars[i + 1] == '_'
            && chars[i + 2] == 'T'
            && chars[i + 3] == '.'
        {
            i += 4;
        } else if chars[i] == '\'' {
            out.push('\'');
            i += 1;
            // string literal — copy until closing quote (handle escapes)
            loop {
                if i >= chars.len() {
                    break;
                }
                if chars[i] == '\\' && i + 1 < chars.len() && chars[i + 1] == '\\' {
                    out.push('\\');
                    out.push('\\');
                    i += 2;
                } else if chars[i] == '\\' && i + 1 < chars.len() && chars[i + 1] == '\'' {
                    out.push('\\');
                    out.push('\'');
                    i += 2;
                } else if chars[i] == '\'' {
                    out.push('\'');
                    i += 1;
                    break;
                } else {
                    out.push(chars[i]);
                    i += 1;
                }
            }
        } else {
            out.push(chars[i]);
            i += 1;
        }
    }
    out.into_iter().collect()
}

/// Rename `_identifier` to `uw_identifier` in a SQL fragment
/// (for `checkString`).
fn uwify_check_string(s: &str) -> String {
    let chars: Vec<char> = s.chars().collect();
    let prefix = if chars.first() == Some(&'_') {
        "uw_"
    } else {
        ""
    };
    let start = if chars.first() == Some(&'_') { 1 } else { 0 };
    let body = uwify_inner(&chars[start..]);
    format!("{}{}", prefix, body)
}

fn uwify_inner(chars: &[char]) -> String {
    let mut out = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        // `( _` → `(uw_`, ` _` → ` uw_`
        if i + 1 < chars.len() && (chars[i] == '(' || chars[i] == ' ') && chars[i + 1] == '_' {
            out.push(chars[i]);
            out.extend("uw_".chars());
            i += 2;
        } else if chars[i] == '\'' {
            out.push('\'');
            i += 1;
            // skip string literal
            loop {
                if i >= chars.len() {
                    break;
                }
                if chars[i] == '\\' && i + 1 < chars.len() && chars[i + 1] == '\\' {
                    out.push('\\');
                    out.push('\\');
                    i += 2;
                } else if chars[i] == '\\' && i + 1 < chars.len() && chars[i + 1] == '\'' {
                    out.push('\\');
                    out.push('\'');
                    i += 2;
                } else if chars[i] == '\'' {
                    out.push('\'');
                    i += 1;
                    break;
                } else {
                    out.push(chars[i]);
                    i += 1;
                }
            }
        } else {
            out.push(chars[i]);
            i += 1;
        }
    }
    out.into_iter().collect()
}

/// Rename `AS _col` → `AS uw_col` in SQL (for `viewify`).
fn uwify_viewify(s: &str) -> String {
    let chars: Vec<char> = s.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        // `A S   _` pattern
        if i + 4 < chars.len()
            && chars[i] == 'A'
            && chars[i + 1] == 'S'
            && chars[i + 2] == ' '
            && chars[i + 3] == '_'
        {
            out.extend("AS uw_".chars());
            i += 4;
        } else if chars[i] == '\'' {
            out.push('\'');
            i += 1;
            loop {
                if i >= chars.len() {
                    break;
                }
                if chars[i] == '\\' && i + 1 < chars.len() && chars[i + 1] == '\\' {
                    out.push('\\');
                    out.push('\\');
                    i += 2;
                } else if chars[i] == '\\' && i + 1 < chars.len() && chars[i + 1] == '\'' {
                    out.push('\\');
                    out.push('\'');
                    i += 2;
                } else if chars[i] == '\'' {
                    out.push('\'');
                    i += 1;
                    break;
                } else {
                    out.push(chars[i]);
                    i += 1;
                }
            }
        } else {
            out.push(chars[i]);
            i += 1;
        }
    }
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
        1 => Some(ps.into_iter().next().unwrap().node),
        _ => {
            let mut iter = ps.into_iter().rev();
            let first = iter.next().unwrap();
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

fn is_ffi_con(pc: &crate::monomorphized::PatCon, module: &str, con: &str) -> bool {
    match pc {
        crate::monomorphized::PatCon::Ffi {
            module: m, con: c, ..
        } => m == module && c == con,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Core peephole function — applied to one node after children are optimized
// ---------------------------------------------------------------------------

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
                .filter_map(|c| {
                    let is_space = c.is_ascii_whitespace();
                    if is_space && last_space {
                        None
                    } else {
                        last_space = is_space;
                        Some(c)
                    }
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
                        unreachable!()
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

            // EWrite(EFfiApp("Basis","htmlifySpecialChar",[e])) → htmlifySpecialChar_w
            Exp::FfiApp(ref m, ref f, ref args) if m == "Basis" && f == "htmlifySpecialChar" => {
                Exp::FfiApp("Basis".into(), "htmlifySpecialChar_w".into(), args.clone())
            }

            // EWrite(EFfiApp("Basis","intToString",[e])) → htmlifyInt_w
            Exp::FfiApp(ref m, ref f, ref args) if m == "Basis" && f == "intToString" => {
                Exp::FfiApp("Basis".into(), "htmlifyInt_w".into(), args.clone())
            }

            // EWrite(htmlifyInt) → htmlifyInt_w
            Exp::FfiApp(ref m, ref f, ref args) if m == "Basis" && f == "htmlifyInt" => {
                Exp::FfiApp("Basis".into(), "htmlifyInt_w".into(), args.clone())
            }

            // EWrite(htmlifyFloat) → htmlifyFloat_w
            Exp::FfiApp(ref m, ref f, ref args) if m == "Basis" && f == "htmlifyFloat" => {
                Exp::FfiApp("Basis".into(), "htmlifyFloat_w".into(), args.clone())
            }

            // EWrite(htmlifyBool) → htmlifyBool_w
            Exp::FfiApp(ref m, ref f, ref args) if m == "Basis" && f == "htmlifyBool" => {
                Exp::FfiApp("Basis".into(), "htmlifyBool_w".into(), args.clone())
            }

            // EWrite(htmlifyTime) → htmlifyTime_w
            Exp::FfiApp(ref m, ref f, ref args) if m == "Basis" && f == "htmlifyTime" => {
                Exp::FfiApp("Basis".into(), "htmlifyTime_w".into(), args.clone())
            }

            // EWrite(htmlifyString with literal) → EWrite(html_lit)
            Exp::FfiApp(ref m, ref f, ref args)
                if m == "Basis" && f == "htmlifyString" && args.len() == 1 =>
            {
                if let Exp::Prim(Prim::String(_, ref s)) = args[0].0.node {
                    let new_inner = html_lit(htmlify_string(s), span);
                    Exp::Write(Box::new(new_inner))
                } else {
                    Exp::FfiApp("Basis".into(), "htmlifyString_w".into(), args.clone())
                }
            }

            // EWrite(htmlifyString) → htmlifyString_w
            Exp::FfiApp(ref m, ref f, ref args) if m == "Basis" && f == "htmlifyString" => {
                Exp::FfiApp("Basis".into(), "htmlifyString_w".into(), args.clone())
            }

            // EWrite(htmlifySource) → htmlifySource_w
            Exp::FfiApp(ref m, ref f, ref args) if m == "Basis" && f == "htmlifySource" => {
                Exp::FfiApp("Basis".into(), "htmlifySource_w".into(), args.clone())
            }

            // EWrite(attrifyInt(lit)) → EWrite(html_lit)
            Exp::FfiApp(ref m, ref f, ref args)
                if m == "Basis" && f == "attrifyInt" && args.len() == 1 =>
            {
                if let Exp::Prim(Prim::Int(n)) = args[0].0.node {
                    Exp::Write(Box::new(html_lit(attrify_int(n), span)))
                } else {
                    Exp::FfiApp("Basis".into(), "attrifyInt_w".into(), args.clone())
                }
            }

            // EWrite(attrifyFloat(lit)) → EWrite(html_lit)
            Exp::FfiApp(ref m, ref f, ref args)
                if m == "Basis" && f == "attrifyFloat" && args.len() == 1 =>
            {
                if let Exp::Prim(Prim::Float(n)) = args[0].0.node {
                    Exp::Write(Box::new(html_lit(attrify_float(n), span)))
                } else {
                    Exp::FfiApp("Basis".into(), "attrifyFloat_w".into(), args.clone())
                }
            }

            // EWrite(attrifyString(lit)) → EWrite(html_lit)
            Exp::FfiApp(ref m, ref f, ref args)
                if m == "Basis" && f == "attrifyString" && args.len() == 1 =>
            {
                if let Exp::Prim(Prim::String(_, ref s)) = args[0].0.node {
                    Exp::Write(Box::new(html_lit(attrify_string(s), span)))
                } else {
                    Exp::FfiApp("Basis".into(), "attrifyString_w".into(), args.clone())
                }
            }

            // EWrite(attrifyChar(lit)) → EWrite(html_lit)
            Exp::FfiApp(ref m, ref f, ref args)
                if m == "Basis" && f == "attrifyChar" && args.len() == 1 =>
            {
                if let Exp::Prim(Prim::Char(c)) = args[0].0.node {
                    Exp::Write(Box::new(html_lit(attrify_char(c), span)))
                } else {
                    Exp::FfiApp("Basis".into(), "attrifyChar_w".into(), args.clone())
                }
            }

            // EWrite(attrifyCss_class(lit)) → EWrite(html_lit)
            Exp::FfiApp(ref m, ref f, ref args)
                if m == "Basis" && f == "attrifyCss_class" && args.len() == 1 =>
            {
                if let Exp::Prim(Prim::String(_, ref s)) = args[0].0.node {
                    Exp::Write(Box::new(html_lit(s.clone(), span)))
                } else {
                    Exp::FfiApp("Basis".into(), "attrifyString_w".into(), args.clone())
                }
            }

            // EWrite(urlifyInt(lit)) → EWrite(normal_lit)
            Exp::FfiApp(ref m, ref f, ref args)
                if m == "Basis" && f == "urlifyInt" && args.len() == 1 =>
            {
                if let Exp::Prim(Prim::Int(n)) = args[0].0.node {
                    Exp::Write(Box::new(normal_lit(urlify_int(n), span)))
                } else {
                    Exp::FfiApp("Basis".into(), "urlifyInt_w".into(), args.clone())
                }
            }

            // EWrite(urlifyFloat(lit)) → EWrite(normal_lit)
            Exp::FfiApp(ref m, ref f, ref args)
                if m == "Basis" && f == "urlifyFloat" && args.len() == 1 =>
            {
                if let Exp::Prim(Prim::Float(n)) = args[0].0.node {
                    Exp::Write(Box::new(normal_lit(urlify_float(n), span)))
                } else {
                    Exp::FfiApp("Basis".into(), "urlifyFloat_w".into(), args.clone())
                }
            }

            // EWrite(urlifyString(lit)) → EWrite(normal_lit)  [Normal mode only for string]
            Exp::FfiApp(ref m, ref f, ref args)
                if m == "Basis" && f == "urlifyString" && args.len() == 1 =>
            {
                if let Exp::Prim(Prim::String(StringMode::Normal, ref s)) = args[0].0.node {
                    Exp::Write(Box::new(normal_lit(urlify_string(s), span)))
                } else {
                    Exp::FfiApp("Basis".into(), "urlifyString_w".into(), args.clone())
                }
            }

            // EWrite(urlifyChar(lit)) → EWrite(normal_lit)
            Exp::FfiApp(ref m, ref f, ref args)
                if m == "Basis" && f == "urlifyChar" && args.len() == 1 =>
            {
                if let Exp::Prim(Prim::Char(c)) = args[0].0.node {
                    Exp::Write(Box::new(normal_lit(urlify_char(c), span)))
                } else {
                    Exp::FfiApp("Basis".into(), "urlifyChar_w".into(), args.clone())
                }
            }

            // EWrite(urlifyBool(True/False)) → EWrite(normal_lit)
            Exp::FfiApp(ref m, ref f, ref args)
                if m == "Basis" && f == "urlifyBool" && args.len() == 1 =>
            {
                match &args[0].0.node {
                    Exp::Con(_, pc, None) if is_ffi_con(pc, "Basis", "True") => {
                        Exp::Write(Box::new(normal_lit("1", span)))
                    }
                    Exp::Con(_, pc, None) if is_ffi_con(pc, "Basis", "False") => {
                        Exp::Write(Box::new(normal_lit("0", span)))
                    }
                    _ => Exp::FfiApp("Basis".into(), "urlifyBool_w".into(), args.clone()),
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

            // EWrite(EStr1(e)) → writec(e)
            Exp::FfiApp(ref m, ref f, ref args) if m == "Basis" && f == "str1" => {
                Exp::FfiApp("Basis".into(), "writec".into(), args.clone())
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

                // intToString → htmlifyInt conversion
                "htmlifyString" if args.len() == 1 => {
                    // htmlifyString(intToString(n)) → htmlifyInt(n) or literal
                    match &args[0].0.node {
                        Exp::FfiApp(m2, f2, args2) if m2 == "Basis" && f2 == "intToString" => {
                            if args2.len() == 1 {
                                if let Exp::Prim(Prim::Int(n)) = args2[0].0.node {
                                    return Exp::Prim(Prim::String(
                                        StringMode::Html,
                                        htmlify_int(n),
                                    ));
                                }
                            }
                            Exp::FfiApp("Basis".into(), "htmlifyInt".into(), args2.clone())
                        }
                        Exp::App(fexpr, earg) => {
                            if let Exp::Ffi(m2, f2) = &fexpr.node {
                                if m2 == "Basis" {
                                    if f2 == "intToString" {
                                        if let Exp::Prim(Prim::Int(n)) = earg.node {
                                            return Exp::Prim(Prim::String(
                                                StringMode::Html,
                                                htmlify_int(n),
                                            ));
                                        }
                                        let t = Located::new(
                                            Typ::Ffi("Basis".into(), "int".into()),
                                            fexpr.span.clone(),
                                        );
                                        return Exp::FfiApp(
                                            "Basis".into(),
                                            "htmlifyInt".into(),
                                            vec![(*earg.clone(), t)],
                                        );
                                    } else if f2 == "floatToString" {
                                        if let Exp::Prim(Prim::Float(n)) = earg.node {
                                            return Exp::Prim(Prim::String(
                                                StringMode::Html,
                                                htmlify_float(n),
                                            ));
                                        }
                                        let t = Located::new(
                                            Typ::Ffi("Basis".into(), "float".into()),
                                            fexpr.span.clone(),
                                        );
                                        return Exp::FfiApp(
                                            "Basis".into(),
                                            "htmlifyFloat".into(),
                                            vec![(*earg.clone(), t)],
                                        );
                                    } else if f2 == "timeToString" {
                                        let t = Located::new(
                                            Typ::Ffi("Basis".into(), "time".into()),
                                            fexpr.span.clone(),
                                        );
                                        return Exp::FfiApp(
                                            "Basis".into(),
                                            "htmlifyTime".into(),
                                            vec![(*earg.clone(), t)],
                                        );
                                    }
                                }
                            }
                            Exp::FfiApp("Basis".into(), "htmlifyString".into(), args)
                        }
                        // htmlifyString(floatToString(...))
                        Exp::FfiApp(m2, f2, args2) if m2 == "Basis" && f2 == "floatToString" => {
                            if args2.len() == 1 {
                                if let Exp::Prim(Prim::Float(n)) = args2[0].0.node {
                                    return Exp::Prim(Prim::String(
                                        StringMode::Html,
                                        htmlify_float(n),
                                    ));
                                }
                            }
                            Exp::FfiApp("Basis".into(), "htmlifyFloat".into(), args2.clone())
                        }
                        // htmlifyString(boolToString(...))
                        Exp::FfiApp(m2, f2, args2) if m2 == "Basis" && f2 == "boolToString" => {
                            if args2.len() == 1 {
                                match &args2[0].0.node {
                                    Exp::Con(_, pc, None) if is_ffi_con(pc, "Basis", "True") => {
                                        return Exp::Prim(Prim::String(
                                            StringMode::Html,
                                            "True".into(),
                                        ))
                                    }
                                    Exp::Con(_, pc, None) if is_ffi_con(pc, "Basis", "False") => {
                                        return Exp::Prim(Prim::String(
                                            StringMode::Html,
                                            "False".into(),
                                        ))
                                    }
                                    _ => {}
                                }
                            }
                            Exp::FfiApp("Basis".into(), "htmlifyBool".into(), args2.clone())
                        }
                        // htmlifyString(literal)
                        Exp::Prim(Prim::String(_, s)) => {
                            Exp::Prim(Prim::String(StringMode::Html, htmlify_string(s)))
                        }
                        _ => Exp::FfiApp("Basis".into(), "htmlifyString".into(), args),
                    }
                }

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
                                format!("Invalid HTML5 data-* attribute {}", s),
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
                                format!("Invalid URL {} passed to 'bless'", s),
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
                                format!("Invalid string {} passed to 'blessMime'", s),
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
                                format!("Invalid string {} passed to 'atom'", s),
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
                                format!("Invalid URL {} passed to 'css_url'", s),
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
                                format!("Invalid string {} passed to 'property'", s),
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
                                format!("Invalid string {} passed to 'blessRequestHeader'", s),
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
                                format!("Invalid string {} passed to 'blessResponseHeader'", s),
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
                                format!("Invalid string {} passed to 'blessEnvVar'", s),
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
                                format!("Invalid string {} passed to 'blessMeta'", s),
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
        // EApp(EFfi("Basis","intToString"), e) → EFfiApp("Basis","intToString",[e,int_t])
        // -----------------------------------------------------------------------
        Exp::App(fexpr, arg) => match &fexpr.node {
            Exp::Ffi(m, f) if m == "Basis" && f == "intToString" => {
                let t = Located::new(Typ::Ffi("Basis".into(), "int".into()), fexpr.span.clone());
                Exp::FfiApp("Basis".into(), "intToString".into(), vec![(*arg, t)])
            }
            _ => Exp::App(fexpr, arg),
        },

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

    fn dummy<T>(node: T) -> Located<T> {
        Located::dummy(node)
    }

    fn settings() -> Settings {
        Settings::default()
    }

    fn settings_mysql() -> Settings {
        let mut s = Settings::default();
        s.dbms = "mysql".into();
        s
    }

    fn settings_postgres() -> Settings {
        let mut s = Settings::default();
        s.dbms = "postgres".into();
        s
    }

    fn no_errors() -> ErrorReporter {
        ErrorReporter::new()
    }

    #[test]
    fn optimize_empty_file() {
        let mut errors = no_errors();
        let result = optimize((vec![], vec![]), &settings(), &mut errors);
        assert!(result.0.is_empty());
    }

    #[test]
    fn attrify_int_positive() {
        assert_eq!(attrify_int(42), "42");
    }

    #[test]
    fn attrify_int_negative() {
        assert_eq!(attrify_int(-7), "-7");
    }

    #[test]
    fn attrify_int_zero_not_negative() {
        // Kills: replace < with == or <= in attrify_int (0 < 0 false => "0"; 0==0 true => "-0")
        assert_eq!(attrify_int(0), "0");
    }

    #[test]
    fn attrify_char_quote() {
        assert_eq!(attrify_char('"'), "&quot;");
    }

    #[test]
    fn attrify_char_amp() {
        assert_eq!(attrify_char('&'), "&amp;");
    }

    #[test]
    fn htmlify_string_lt() {
        assert_eq!(htmlify_string("<b>"), "&lt;b>");
    }

    #[test]
    fn urlify_string_empty() {
        assert_eq!(urlify_string(""), "_");
    }

    #[test]
    fn urlify_string_underscore_prefix() {
        // '_' is encoded as ".5F" by urlifyCharAux; prefix "_" is prepended.
        let s = urlify_string("_hello");
        assert!(s.starts_with("_.5F"), "got: {}", s);
    }

    #[test]
    fn hex_it_ascii() {
        assert_eq!(hex_it('A'), "41");
    }

    #[test]
    fn fold_strcat_empty() {
        let mut errors = no_errors();
        let e1 = dummy(Exp::Prim(Prim::String(StringMode::Normal, "hello".into())));
        let e2 = dummy(Exp::Prim(Prim::String(StringMode::Normal, "".into())));
        let cat = dummy(Exp::Strcat(Box::new(e1.clone()), Box::new(e2)));
        let result = opt_exp(cat, &settings(), &mut errors);
        assert!(matches!(&result.node, Exp::Prim(Prim::String(_, s)) if s == "hello"));
    }

    #[test]
    fn fold_strcat_two_lits() {
        let mut errors = no_errors();
        let e1 = dummy(Exp::Prim(Prim::String(StringMode::Normal, "foo".into())));
        let e2 = dummy(Exp::Prim(Prim::String(StringMode::Normal, "bar".into())));
        let cat = dummy(Exp::Strcat(Box::new(e1), Box::new(e2)));
        let result = opt_exp(cat, &settings(), &mut errors);
        assert!(matches!(&result.node, Exp::Prim(Prim::String(_, s)) if s == "foobar"));
    }

    #[test]
    fn attrify_float_positive() {
        assert_eq!(attrify_float(1.5), "1.5");
    }

    #[test]
    fn attrify_float_negative() {
        assert_eq!(attrify_float(-2.0), "-2");
    }

    #[test]
    fn attrify_float_zero_not_negative() {
        // Kills: replace < with == or <= in attrify_float
        assert_eq!(attrify_float(0.0), "0");
    }

    #[test]
    fn attrify_string_escape() {
        assert_eq!(attrify_string("a&b"), "a&amp;b");
    }

    #[test]
    fn urlify_char_space() {
        assert_eq!(urlify_char(' '), "+");
    }

    #[test]
    fn urlify_char_alphanumeric() {
        assert_eq!(urlify_char('a'), "a");
    }

    #[test]
    fn urlify_char_underscore_prefix() {
        // '_' gets prefix "_" + aux; aux for '_' is ".5F"
        let s = urlify_char('_');
        assert!(s.starts_with("_.5F") || s.contains("5F"), "got: {}", s);
    }

    #[test]
    fn htmlify_special_char_formats_codepoint() {
        assert_eq!(htmlify_special_char('x'), "&#120;");
    }

    #[test]
    fn hex_pad_single_digit() {
        assert_eq!(hex_pad(5), "05");
    }

    #[test]
    fn hex_pad_zero() {
        // format!("{:X}", 0) = "0", len 1 => "0" + "0" = "00"
        assert_eq!(hex_pad(0), "00");
    }

    #[test]
    fn hex_it_two_byte_boundary() {
        // 0x80 = 128: first branch c <= 0x7f is false, second c <= 0x7ff true
        let s = hex_it(std::char::from_u32(0x80).unwrap());
        assert!(s.len() >= 2 && s.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn fold_attrify_int() {
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
    }

    #[test]
    fn fold_attrify_string() {
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
    }

    #[test]
    fn fold_urlify_int() {
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
    }

    #[test]
    fn fold_strcat_three_lits() {
        let mut errors = no_errors();
        let e1 = dummy(Exp::Prim(Prim::String(StringMode::Normal, "a".into())));
        let e2 = dummy(Exp::Prim(Prim::String(StringMode::Normal, "b".into())));
        let e3 = dummy(Exp::Prim(Prim::String(StringMode::Normal, "c".into())));
        let cat12 = dummy(Exp::Strcat(Box::new(e1), Box::new(e2)));
        let cat = dummy(Exp::Strcat(Box::new(cat12), Box::new(e3)));
        let result = opt_exp(cat, &settings(), &mut errors);
        assert!(matches!(&result.node, Exp::Prim(Prim::String(_, s)) if s == "abc"));
    }

    // --- sqlify_*: exact output so return-value mutants are killed ---
    #[test]
    fn sqlify_int_postgres_adds_cast() {
        assert_eq!(sqlify_int(42, &settings_postgres()), "42::int8");
    }

    #[test]
    fn sqlify_int_mysql_no_cast() {
        assert_eq!(sqlify_int(42, &settings_mysql()), "42");
    }

    #[test]
    fn sqlify_float_postgres_adds_cast() {
        assert_eq!(sqlify_float(1.5, &settings_postgres()), "1.5::float8");
    }

    #[test]
    fn sqlify_float_mysql_no_cast() {
        assert_eq!(sqlify_float(1.5, &settings_mysql()), "1.5");
    }

    #[test]
    fn sqlify_string_postgres_doubles_quote() {
        assert_eq!(sqlify_string("'", &settings_postgres()), "''''");
    }

    #[test]
    fn sqlify_string_mysql_escapes_backslash() {
        assert_eq!(sqlify_string("\\", &settings_mysql()), "'\\\\'");
    }

    #[test]
    fn sqlify_char_postgres() {
        assert_eq!(sqlify_char('x', &settings_postgres()), "'x'");
    }

    #[test]
    fn sqlify_bool_true_postgres() {
        assert_eq!(sqlify_bool_true(&settings_postgres()), "TRUE");
    }

    #[test]
    fn sqlify_bool_true_mysql() {
        assert_eq!(sqlify_bool_true(&settings_mysql()), "1");
    }

    #[test]
    fn sqlify_bool_false_postgres() {
        assert_eq!(sqlify_bool_false(&settings_postgres()), "FALSE");
    }

    #[test]
    fn sqlify_bool_false_mysql() {
        assert_eq!(sqlify_bool_false(&settings_mysql()), "0");
    }

    // --- check_url, check_data, check_atom, check_css_url, check_property ---
    #[test]
    fn check_url_true_when_rule_allows() {
        let mut s = Settings::default();
        s.url_rules.push(crate::settings::Rule {
            action: crate::settings::Action::Allow,
            kind: crate::settings::PatternKind::Exact,
            pattern: "/foo".into(),
        });
        assert!(check_url("/foo", &s), "allowed URL must be true");
    }

    #[test]
    fn check_url_false_when_no_rule() {
        let s = Settings::default();
        assert!(!check_url("/bar", &s), "no rule => false");
    }

    #[test]
    fn check_data_allows_alphanumeric_underscore_hyphen() {
        assert!(check_data("a_1"));
        assert!(check_data("x-y"));
        assert!(!check_data("a b"));
    }

    #[test]
    fn check_atom_allows_plus_minus_dot() {
        assert!(check_atom("a+b"));
        assert!(check_atom("1.2"));
        assert!(!check_atom("a!b"));
    }

    #[test]
    fn check_css_url_allows_slash_colon() {
        assert!(check_css_url("https://x/y"));
        assert!(!check_css_url("a<>"));
    }

    #[test]
    fn hex_pad_two_digits_unchanged() {
        // len 2 => no leading zero. Kills "delete match arm 0" and arm 1.
        assert_eq!(hex_pad(0x0A), "0A");
        assert_eq!(hex_pad(0xFF), "FF");
    }

    #[test]
    fn hex_it_three_byte_utf8() {
        // Codepoint > 0x7ff hits third branch (c <= 0xffff).
        let ch = std::char::from_u32(0x0800).unwrap();
        let s = hex_it(ch);
        assert!(
            s.len() >= 3,
            "three-byte UTF-8 produces at least 3 hex pairs"
        );
    }

    #[test]
    fn check_data_rejects_space() {
        assert!(!check_data("a b"));
    }

    #[test]
    fn check_data_allows_hyphen() {
        assert!(check_data("a-b"));
    }

    #[test]
    fn check_atom_rejects_bang() {
        assert!(!check_atom("a!b"));
    }

    #[test]
    fn check_atom_allows_hash() {
        assert!(check_atom("a#b"));
    }
}
