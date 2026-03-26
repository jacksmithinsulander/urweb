//! Marshal-check pass for the Core IR.
//!
//! Verifies that exported page handlers, cookies, and `serialize`/`deserialize`
//! call-sites do not involve FFI types that are disallowed for client-to-server
//! marshalling.
//!
//! Mirrors `marshalcheck.sml`.

use std::collections::{BTreeSet, HashMap};

use crate::core::utilities::constructor as con_util;
use crate::core::*;
use crate::error_types::ErrorReporter;
use crate::settings::Settings;

// ---------------------------------------------------------------------------
// Internal maps
// ---------------------------------------------------------------------------

/// For each named-constructor id: the set of Ffi (module, name) pairs
/// reachable through it that are disallowed for client-to-server marshalling.
type CMap = HashMap<usize, BTreeSet<(String, String)>>;

/// For each named-value id: its type constructor and human-readable tag.
type EMap = HashMap<usize, (LocatedConstructor, String)>;

// ---------------------------------------------------------------------------
// sins — collect disallowed Ffi pairs from a constructor
// ---------------------------------------------------------------------------

fn sins(cmap: &CMap, con: &LocatedConstructor, settings: &Settings) -> BTreeSet<(String, String)> {
    con_util::fold(
        con,
        BTreeSet::new(),
        &|_k, s| s, // kinds carry no Ffi info
        &|c_node, mut s| {
            match &c_node.node {
                Constructor::Ffi(m, x) => {
                    if !settings.may_client_to_server(&(m.clone(), x.clone())) {
                        s.insert((m.clone(), x.clone()));
                    }
                }
                Constructor::Named(n) => {
                    if let Some(sin_set) = cmap.get(n) {
                        s.extend(sin_set.iter().cloned());
                    }
                }
                _ => {}
            }
            s
        },
    )
}

fn sins_to_string(s: &BTreeSet<(String, String)>) -> String {
    let items: Vec<String> = s.iter().map(|(m, x)| format!("{m}.{x}")).collect();
    match items.as_slice() {
        [] => "{}".into(),
        [one] => one.clone(),
        _ => items.join(", "),
    }
}

// ---------------------------------------------------------------------------
// is_exempt_input — skip postBody / option(queryString) arg types
// ---------------------------------------------------------------------------

fn is_exempt_input(c: &Constructor) -> bool {
    match c {
        Constructor::Ffi(m, x) => m == "Basis" && x == "postBody",
        Constructor::App(f, arg) => {
            matches!(&f.node, Constructor::Ffi(m, x) if m == "Basis" && x == "option")
                && matches!(&arg.node, Constructor::Ffi(m, x) if m == "Basis" && x == "queryString")
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// make_s — walk TFun chain collecting sins from non-exempt argument types
// ---------------------------------------------------------------------------

fn make_s(cmap: &CMap, t: &LocatedConstructor, settings: &Settings) -> BTreeSet<(String, String)> {
    match &t.node {
        Constructor::TFun(dom, ran) => {
            let dom_sins = if is_exempt_input(&dom.node) {
                BTreeSet::new()
            } else {
                sins(cmap, dom, settings)
            };
            let ran_sins = make_s(cmap, ran, settings);
            dom_sins.into_iter().chain(ran_sins).collect()
        }
        _ => BTreeSet::new(),
    }
}

// ---------------------------------------------------------------------------
// walk_expression — scan for serialize/deserialize CApps
// ---------------------------------------------------------------------------

fn walk_expression(
    exp: &LocatedExpression,
    cmap: &CMap,
    settings: &Settings,
    errors: &mut ErrorReporter,
) {
    match &exp.node {
        Expression::CApp(f, t_con) => {
            if let Expression::Ffi(m, x) = &f.node {
                if m == "Basis" && (x == "serialize" || x == "deserialize") {
                    let s = sins(cmap, t_con, settings);
                    if !s.is_empty() {
                        errors.report_at(
                            t_con.span.clone(),
                            format!(
                                "Not allowed to [de]serialize a value involving one or more \
                                 disallowed types: {}",
                                sins_to_string(&s)
                            ),
                        );
                    }
                }
            }
            walk_expression(f, cmap, settings, errors);
            // t_con is a constructor — no expression sub-trees to walk
        }
        Expression::App(f, arg) => {
            walk_expression(f, cmap, settings, errors);
            walk_expression(arg, cmap, settings, errors);
        }
        Expression::Abs(_, _, _, body)
        | Expression::CAbs(_, _, body)
        | Expression::KAbs(_, body) => walk_expression(body, cmap, settings, errors),
        Expression::KApp(f, _) | Expression::Write(f) | Expression::Field(f, _, _) => {
            walk_expression(f, cmap, settings, errors)
        }
        Expression::Let(_, _, e1, e2) => {
            walk_expression(e1, cmap, settings, errors);
            walk_expression(e2, cmap, settings, errors);
        }
        Expression::Case(disc, arms, _) => {
            walk_expression(disc, cmap, settings, errors);
            for (_, body) in arms {
                walk_expression(body, cmap, settings, errors);
            }
        }
        Expression::Record(fields) => {
            for (_, e, _) in fields {
                walk_expression(e, cmap, settings, errors);
            }
        }
        Expression::Concat(e1, _, e2, _) => {
            walk_expression(e1, cmap, settings, errors);
            walk_expression(e2, cmap, settings, errors);
        }
        Expression::Cut(e, _, _) | Expression::CutMulti(e, _, _) => {
            walk_expression(e, cmap, settings, errors)
        }
        Expression::FfiApp(_, _, args) => {
            for (e, _) in args {
                walk_expression(e, cmap, settings, errors);
            }
        }
        Expression::Constructor(_, _, _, Some(inner)) => {
            walk_expression(inner, cmap, settings, errors)
        }
        Expression::ServerCall(_, args, _, _) | Expression::Closure(_, args) => {
            for e in args {
                walk_expression(e, cmap, settings, errors);
            }
        }
        // Leaves: Prim, Rel, Named, Ffi, Constructor(no arg)
        Expression::Prim(_)
        | Expression::Rel(_)
        | Expression::Named(_)
        | Expression::Ffi(_, _)
        | Expression::Constructor(_, _, _, None) => {}
    }
}

// ---------------------------------------------------------------------------
// process_declaration — dispatch on each declaration kind
// ---------------------------------------------------------------------------

fn process_declaration(
    decl: &LocatedDeclaration,
    cmap: &mut CMap,
    emap: &mut EMap,
    settings: &Settings,
    errors: &mut ErrorReporter,
) {
    let span = decl.span.clone();
    match &decl.node {
        Declaration::Constructor(_, n, _, c) => {
            let s = sins(cmap, c, settings);
            cmap.insert(*n, s);
        }

        Declaration::Datatype(dts) => {
            for dt in dts {
                // Each dt sees the cmap updated by earlier dts in this group.
                let s = dt
                    .constrs
                    .iter()
                    .fold(BTreeSet::new(), |mut acc, (_, _, co)| {
                        if let Some(c) = co {
                            acc.extend(sins(cmap, c, settings));
                        }
                        acc
                    });
                cmap.insert(dt.id, s);
            }
        }

        Declaration::Val(_, n, t, e, tag) => {
            emap.insert(*n, (t.clone(), tag.clone()));
            walk_expression(e, cmap, settings, errors);
        }

        Declaration::ValRec(vis) => {
            // Insert all emap entries first so exports can find them.
            for (_, n, t, _, tag) in vis {
                emap.insert(*n, (t.clone(), tag.clone()));
            }
            for (_, _, _, e, _) in vis {
                walk_expression(e, cmap, settings, errors);
            }
        }

        Declaration::Export(_, n, _) => match emap.get(n) {
            None => errors.report_at(span, "MarshalCheck: Unknown export".to_string()),
            Some((t, tag)) => {
                let t = t.clone();
                let tag = tag.clone();
                let s = make_s(cmap, &t, settings);
                if !s.is_empty() {
                    errors.report_at(
                        span,
                        format!(
                            "Input to exported function '{}' involves one or more types \
                             that are disallowed for page handler inputs: {}",
                            tag,
                            sins_to_string(&s)
                        ),
                    );
                }
            }
        },

        Declaration::Cookie(_, _, t, tag) => {
            let s = sins(cmap, t, settings);
            if !s.is_empty() {
                errors.report_at(
                    span,
                    format!(
                        "Cookie '{}' includes one or more types that are disallowed for cookies: {}",
                        tag,
                        sins_to_string(&s)
                    ),
                );
            }
        }

        Declaration::Table { exp, pk_exp, .. } => {
            walk_expression(exp, cmap, settings, errors);
            walk_expression(pk_exp, cmap, settings, errors);
        }
        Declaration::View(_, _, _, e, _) => walk_expression(e, cmap, settings, errors),
        Declaration::Index(e1, e2) | Declaration::Task(e1, e2) => {
            walk_expression(e1, cmap, settings, errors);
            walk_expression(e2, cmap, settings, errors);
        }
        Declaration::Policy(e) => walk_expression(e, cmap, settings, errors),

        // No expressions inside these declarations.
        Declaration::Sequence(_, _, _)
        | Declaration::Database(_)
        | Declaration::Style(_, _, _)
        | Declaration::OnError(_) => {}
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Run the marshal-check pass over the Core file, reporting errors via
/// `errors`.  Does not transform the file.
pub fn check(file: &[LocatedDeclaration], settings: &Settings, errors: &mut ErrorReporter) {
    let mut cmap: CMap = HashMap::new();
    let mut emap: EMap = HashMap::new();
    for decl in file {
        process_declaration(decl, &mut cmap, &mut emap, settings, errors);
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error_types::Located;

    fn dummy<T>(node: T) -> Located<T> {
        Located::dummy(node)
    }

    fn dummy_con() -> LocatedConstructor {
        dummy(Constructor::Unit)
    }

    fn dummy_exp() -> LocatedExpression {
        dummy(Expression::Named(0))
    }

    fn settings_with_allowed(allowed: &[(&str, &str)]) -> Settings {
        let mut s = Settings::default();
        for (m, x) in allowed {
            s.client_to_server.insert((m.to_string(), x.to_string()));
        }
        s
    }

    /// Empty file produces no errors.
    #[test]
    fn test_empty_file() {
        let mut errors = ErrorReporter::new();
        let settings = Settings::default();
        check(&[], &settings, &mut errors);
        assert!(!errors.has_errors());
    }

    /// sins returns empty for Unit constructor.
    #[test]
    fn test_sins_unit() {
        let settings = Settings::default();
        let s = sins(&HashMap::new(), &dummy_con(), &settings);
        assert!(s.is_empty());
    }

    /// sins captures a disallowed Ffi type.
    #[test]
    fn test_sins_disallowed_ffi() {
        // Default settings: "MyMod.secret" is not in client_to_server
        let settings = Settings::default();
        let c = dummy(Constructor::Ffi("MyMod".into(), "secret".into()));
        let s = sins(&HashMap::new(), &c, &settings);
        assert!(s.contains(&("MyMod".into(), "secret".into())));
    }

    /// sins does not capture an allowed Ffi type.
    #[test]
    fn test_sins_allowed_ffi() {
        let mut settings = Settings::default();
        settings
            .client_to_server
            .insert(("Basis".into(), "int".into()));
        let c = dummy(Constructor::Ffi("Basis".into(), "int".into()));
        let s = sins(&HashMap::new(), &c, &settings);
        assert!(s.is_empty());
    }

    /// sins propagates through Named constructor lookup.
    #[test]
    fn test_sins_named_propagates() {
        let settings = Settings::default();
        let mut cmap = HashMap::new();
        let sin_set: BTreeSet<(String, String)> =
            std::iter::once(("M".into(), "x".into())).collect();
        cmap.insert(42usize, sin_set);
        let c = dummy(Constructor::Named(42));
        let s = sins(&cmap, &c, &settings);
        assert!(s.contains(&("M".into(), "x".into())));
    }

    /// is_exempt_input accepts postBody.
    #[test]
    fn test_is_exempt_postbody() {
        assert!(is_exempt_input(&Constructor::Ffi(
            "Basis".into(),
            "postBody".into()
        )));
    }

    /// is_exempt_input accepts option(queryString).
    #[test]
    fn test_is_exempt_option_querystring() {
        let c = Constructor::App(
            Box::new(dummy(Constructor::Ffi("Basis".into(), "option".into()))),
            Box::new(dummy(Constructor::Ffi(
                "Basis".into(),
                "queryString".into(),
            ))),
        );
        assert!(is_exempt_input(&c));
    }

    /// is_exempt_input rejects a non-exempt Ffi.
    #[test]
    fn test_is_exempt_other() {
        assert!(!is_exempt_input(&Constructor::Ffi(
            "Basis".into(),
            "int".into()
        )));
        assert!(!is_exempt_input(&Constructor::Unit));
    }

    /// sins_to_string formats correctly.
    #[test]
    fn test_sins_to_string() {
        let empty: BTreeSet<(String, String)> = BTreeSet::new();
        assert_eq!(sins_to_string(&empty), "{}");
        let one: BTreeSet<(String, String)> =
            std::iter::once(("Basis".into(), "foo".into())).collect();
        assert_eq!(sins_to_string(&one), "Basis.foo");
        let two: BTreeSet<(String, String)> = [
            ("Basis".into(), "bar".into()),
            ("Basis".into(), "foo".into()),
        ]
        .into_iter()
        .collect();
        assert_eq!(sins_to_string(&two), "Basis.bar, Basis.foo");
    }

    /// Cookie with disallowed type reports an error.
    #[test]
    fn test_cookie_disallowed_type() {
        let settings = Settings::default();
        let disallowed = dummy(Constructor::Ffi("Bad".into(), "type".into()));
        let file: File = vec![dummy(Declaration::Cookie(
            "myCookie".into(),
            1,
            disallowed,
            "myCookieTag".into(),
        ))];
        let mut errors = ErrorReporter::new();
        check(&file, &settings, &mut errors);
        assert!(errors.has_errors());
    }

    /// Cookie with allowed (Unit) type reports no error.
    #[test]
    fn test_cookie_allowed_type() {
        let mut settings = Settings::default();
        settings
            .client_to_server
            .insert(("Good".into(), "type".into()));
        let allowed = dummy(Constructor::Ffi("Good".into(), "type".into()));
        let file: File = vec![dummy(Declaration::Cookie(
            "myCookie".into(),
            1,
            allowed,
            "tag".into(),
        ))];
        let mut errors = ErrorReporter::new();
        check(&file, &settings, &mut errors);
        assert!(!errors.has_errors());
    }
}
