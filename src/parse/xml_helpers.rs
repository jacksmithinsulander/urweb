//! Helper types and functions for XML desugaring in the LALRPOP grammar.

use crate::error_types::{Located, Span};
use crate::source::*;

// ---------------------------------------------------------------------------
// Function parameter (term or constructor-level) for fun/fn sugar
// ---------------------------------------------------------------------------

#[derive(Clone)]
pub enum FunParam {
    /// A regular term-level pattern argument
    Term(LocPat),
    /// A constructor-level argument: `[nm]` (lowercase) or `[nm :: K]`, `[nm ::: K]`.
    /// `[lowercase]` produces `ECAbs`; `[uppercase]` that has an explicit kind also
    /// goes through this path.
    ConArg(Explicitness, String, Option<LocKind>),
    /// A **kind**-level binder `[K]` where `K` is an uppercase identifier.
    /// Desugars to `Exp::KAbs(K, body)` — matches `eargp: LBRACK CSYMBOL RBRACK`
    /// in `urweb.grm` which produces `EKAbs`/`TKFun`.
    KindArg(String),
    /// A disjointness constraint: `[c1 ~ c2]`
    Disjoint(LocCon, LocCon),
}

/// Fold a list of `FunParam`s (from innermost to outermost) into nested
/// `Exp::Abs`, `Exp::CAbs`, and `Exp::Disjoint` wrappers around `body`.
pub fn wrap_fun_params(params: Vec<FunParam>, body: LocExp) -> LocExp {
    params
        .into_iter()
        .rev()
        .fold(body, |acc, param| match param {
            FunParam::Term(p) => {
                let span = p.span.clone();
                let (name, annotation, inner) = match p.node {
                    Pat::Var(x) => (x, None, acc),
                    Pat::Annot(inner_pattern, annotation_constructor)
                        if annotated_var_pattern_supports_direct_lambda(
                            &span,
                            inner_pattern.as_ref(),
                            &annotation_constructor,
                        ) =>
                    {
                        match inner_pattern.as_ref().node.clone() {
                            Pat::Var(name) => (name, Some(annotation_constructor.clone()), acc),
                            _ => unreachable!("guard only allows variable patterns"),
                        }
                    }
                    node => {
                        let fresh = "_arg".to_string();
                        let case_e = Located::dummy(Exp::Case(
                            Box::new(Located::dummy(Exp::Var(
                                vec![],
                                fresh.clone(),
                                Inference::DontInfer,
                            ))),
                            vec![(Located::new(node, span), acc)],
                        ));
                        (fresh, None, case_e)
                    }
                };
                Located::dummy(Exp::Abs(name, annotation, Box::new(inner)))
            }
            FunParam::ConArg(exp, nm, opt_k) => {
                // Constructor/type-level abstraction: `[nm :: K]` or `[nm]` (lowercase).
                let k = opt_k.unwrap_or_else(|| Located::dummy(Kind::Wild));
                Located::dummy(Exp::CAbs(exp, nm, Box::new(k), Box::new(acc)))
            }
            FunParam::KindArg(nm) => {
                // Kind-level abstraction: `[K]` where K is an uppercase identifier.
                // Matches `eargp: LBRACK CSYMBOL RBRACK → EKAbs(CSYMBOL, e)` in urweb.grm.
                Located::dummy(Exp::KAbs(nm, Box::new(acc)))
            }
            FunParam::Disjoint(c1, c2) => Located::dummy(Exp::Disjoint(c1, c2, Box::new(acc))),
        })
}

fn annotated_var_pattern_supports_direct_lambda(
    pattern_span: &Span,
    pattern: &LocPat,
    annotation_constructor: &LocCon,
) -> bool {
    match (&pattern.node, &annotation_constructor.node) {
        (Pat::Var(_), Con::Var(module_path, _)) => {
            !is_dummy_parser_repair_span(pattern_span) || !module_path.is_empty()
        }
        (Pat::Var(_), _) => true,
        _ => false,
    }
}

fn is_dummy_parser_repair_span(span: &Span) -> bool {
    span.first.line == 0 && span.first.col == 0 && span.last.line == 0 && span.last.col == 0
}

/// Convert a parsed `Str` to `Decl::Open` (for simple module paths) or
/// `Decl::OpenStr` (for functor applications and other complex structures).
pub fn str_to_decl_open(s: LocStr) -> Decl {
    fn try_path(s: &Str) -> Option<Vec<String>> {
        match s {
            Str::Var(x) => Some(vec![x.clone()]),
            Str::Proj(base, f) => {
                let mut path = try_path(&base.node)?;
                path.push(f.clone());
                Some(path)
            }
            _ => None,
        }
    }
    match try_path(&s.node) {
        Some(mut path) => {
            let last = path.pop().unwrap_or_default();
            Decl::Open(last, path)
        }
        None => Decl::OpenStr(s),
    }
}

/// A single parsed XML attribute before accumulation into the attrs tuple.
#[derive(Clone)]
pub enum XmlAttr {
    Class(LocExp),
    DynClass(LocExp),
    Style(LocExp),
    DynStyle(LocExp),
    Normal(LocCon, LocExp),
}

/// Capitalize the first character of an XML attribute name: "href" → "Href".
pub fn capitalize_attr(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(c) => c.to_uppercase().to_string() + chars.as_str(),
    }
}

/// Build `Basis.cdata (Html "")`.
///
/// Boxed so LALRPOP’s `____Symbol` stack type stays small (`clippy::large_enum_variant`).
pub type XmlAttrsAccInner = (
    Option<LocExp>,
    Option<LocExp>,
    Option<LocExp>,
    Option<LocExp>,
    Vec<(LocCon, LocExp)>,
);
pub type XmlAttrsAcc = Box<XmlAttrsAccInner>;

#[inline]
pub fn xml_attrs_empty() -> XmlAttrsAcc {
    Box::new((None, None, None, None, vec![]))
}

pub fn xml_attrs_push(mut acc: XmlAttrsAcc, a: XmlAttr) -> XmlAttrsAcc {
    let (ref mut cls, ref mut dcls, ref mut sty, ref mut dsty, ref mut av) = &mut *acc;
    match a {
        XmlAttr::Class(e) => *cls = Some(e),
        XmlAttr::DynClass(e) => *dcls = Some(e),
        XmlAttr::Style(e) => *sty = Some(e),
        XmlAttr::DynStyle(e) => *dsty = Some(e),
        XmlAttr::Normal(k, v) => av.push((k, v)),
    }
    acc
}

/// Desugar `<tag attrs>…` opening (before XML content) to the curried `Basis.tag` / `form` / etc.
/// expression consumed by `XmlOne`.
pub fn xml_desugar_tag_open(
    l: usize,
    r: usize,
    head: (String, LocExp),
    attrs: XmlAttrsAcc,
) -> LocExp {
    let pos = Span::from_offsets("", l, r, &[]);
    let (name, head_exp) = head;
    let (cls, dcls, sty, dsty, attr_pairs) = *attrs;

    let some_wrap = |e: LocExp, p: Span| -> LocExp {
        Located::new(
            Exp::App(
                Box::new(Located::new(
                    Exp::Var(vec!["Basis".into()], "Some".into(), Inference::Infer),
                    p.clone(),
                )),
                Box::new(e),
            ),
            p,
        )
    };
    let none_exp = |p: Span| -> LocExp {
        Located::new(
            Exp::Var(vec!["Basis".into()], "None".into(), Inference::Infer),
            p,
        )
    };

    if name == "form" {
        let key_exp = none_exp(pos.clone());
        let cls_exp = match cls {
            None => none_exp(pos.clone()),
            Some(ce) => some_wrap(ce, pos.clone()),
        };
        let e = Located::new(
            Exp::Var(vec!["Basis".into()], "form".into(), Inference::Infer),
            pos.clone(),
        );
        let e = Located::new(Exp::App(Box::new(e), Box::new(key_exp)), pos.clone());
        Located::new(Exp::App(Box::new(e), Box::new(cls_exp)), pos)
    } else if name == "subform" || name == "subforms" {
        head_exp
    } else if name == "entry" {
        Located::new(
            Exp::Var(vec!["Basis".into()], "entry".into(), Inference::Infer),
            pos,
        )
    } else {
        let basis_tag = Located::new(
            Exp::Var(vec!["Basis".into()], "tag".into(), Inference::Infer),
            pos.clone(),
        );
        let class_exp = match cls {
            None => Located::new(
                Exp::Var(vec!["Basis".into()], "null".into(), Inference::Infer),
                pos.clone(),
            ),
            Some(ce) => ce,
        };
        let e = Located::new(
            Exp::App(Box::new(basis_tag), Box::new(class_exp)),
            pos.clone(),
        );
        let dcls_exp = match dcls {
            None => none_exp(pos.clone()),
            Some(ce) => some_wrap(ce, pos.clone()),
        };
        let e = Located::new(Exp::App(Box::new(e), Box::new(dcls_exp)), pos.clone());
        let sty_exp = match sty {
            None => Located::new(
                Exp::Var(vec!["Basis".into()], "noStyle".into(), Inference::Infer),
                pos.clone(),
            ),
            Some(se) => se,
        };
        let e = Located::new(Exp::App(Box::new(e), Box::new(sty_exp)), pos.clone());
        let dsty_exp = match dsty {
            None => none_exp(pos.clone()),
            Some(se) => some_wrap(se, pos.clone()),
        };
        let e = Located::new(Exp::App(Box::new(e), Box::new(dsty_exp)), pos.clone());
        let attrs_rec = Located::new(Exp::Record(attr_pairs, false), pos.clone());
        let e = Located::new(Exp::App(Box::new(e), Box::new(attrs_rec)), pos.clone());
        let empty_rec = Located::new(Exp::Record(vec![], false), pos.clone());
        let head_applied = Located::new(
            Exp::App(Box::new(head_exp), Box::new(empty_rec)),
            pos.clone(),
        );
        Located::new(Exp::App(Box::new(e), Box::new(head_applied)), pos)
    }
}

pub fn xml_empty_cdata(pos: Span) -> LocExp {
    Located::new(
        Exp::App(
            Box::new(Located::new(
                Exp::Var(vec!["Basis".into()], "cdata".into(), Inference::Infer),
                pos.clone(),
            )),
            Box::new(Located::new(
                Exp::Prim(crate::primitives::Prim::String(
                    crate::primitives::StringMode::Html,
                    "".into(),
                )),
                pos.clone(),
            )),
        ),
        pos,
    )
}

/// ML parser parity for self-closing XML tags whose empty child must have `use = []`.
///
/// `Basis.cdata` is polymorphic in the XML use row, so a plain `cdata ""` leaves a
/// phantom `?useInner` behind. The original grammar special-cases `submit` and `dyn`
/// by fixing the second implicit argument to the empty row for self-closing tags.
pub fn xml_empty_cdata_for_self_closing_tag(name: &str, pos: Span) -> LocExp {
    if name != "submit" && name != "dyn" {
        return xml_empty_cdata(pos);
    }

    let cdata_head = Located::new(
        Exp::Var(vec!["Basis".into()], "cdata".into(), Inference::DontInfer),
        pos.clone(),
    );
    let wildcard_kind = Located::new(crate::source::Kind::Wild, pos.clone());
    let wildcard_ctx = Located::new(
        crate::source::Con::Wild(Box::new(wildcard_kind)),
        pos.clone(),
    );
    let empty_use_row = Located::new(crate::source::Con::Record(vec![]), pos.clone());
    let fixed_ctx = Located::new(Exp::CApp(Box::new(cdata_head), wildcard_ctx), pos.clone());
    let fixed_use = Located::new(Exp::CApp(Box::new(fixed_ctx), empty_use_row), pos.clone());
    Located::new(
        Exp::App(
            Box::new(fixed_use),
            Box::new(Located::new(
                Exp::Prim(crate::primitives::Prim::String(
                    crate::primitives::StringMode::Html,
                    "".into(),
                )),
                pos.clone(),
            )),
        ),
        pos,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn subforms_tag_open_keeps_constructor_applied_head() {
        let head_exp = Located::dummy(Exp::CApp(
            Box::new(Located::dummy(Exp::Var(
                vec!["Basis".into()],
                "subforms".into(),
                Inference::Infer,
            ))),
            Located::dummy(Con::Name("Lines".into())),
        ));
        let desugared =
            xml_desugar_tag_open(0, 0, ("subforms".into(), head_exp), xml_attrs_empty());
        match desugared.node {
            Exp::CApp(inner, constructor_argument) => {
                assert!(
                    matches!(
                        &inner.node,
                        Exp::Var(module_path, name, Inference::Infer)
                            if *module_path == vec!["Basis".to_string()] && name == "subforms"
                    ),
                    "subforms head should stay as the original function, got {:?}",
                    inner
                );
                assert!(
                    matches!(&constructor_argument.node, Con::Name(name) if name == "Lines"),
                    "subforms constructor argument should be preserved, got {:?}",
                    constructor_argument
                );
            }
            other => {
                panic!("subforms tag open should not inject an empty-record app, got {other:?}")
            }
        }
    }

    #[test]
    fn self_closing_dyn_empty_child_fixes_use_row_to_empty() {
        let desugared = xml_empty_cdata_for_self_closing_tag("dyn", Span::dummy());
        let Exp::App(cdata_call, payload) = &desugared.node else {
            panic!(
                "expected application of Basis.cdata, got {:?}",
                desugared.node
            );
        };
        assert!(
            matches!(&payload.node, Exp::Prim(crate::primitives::Prim::String(_, text)) if text.is_empty()),
            "expected empty string payload, got {:?}",
            payload.node
        );
        let Exp::CApp(cdata_with_ctx, use_row) = &cdata_call.node else {
            panic!(
                "expected self-closing dyn helper to explicitly fix the use row, got {:?}",
                cdata_call.node
            );
        };
        assert!(
            matches!(&use_row.node, crate::source::Con::Record(fields) if fields.is_empty()),
            "expected empty row constructor for the use argument, got {:?}",
            use_row.node
        );
        let Exp::CApp(cdata_head, wildcard_ctx) = &cdata_with_ctx.node else {
            panic!(
                "expected self-closing dyn helper to explicitly fix the ctx wildcard, got {:?}",
                cdata_with_ctx.node
            );
        };
        assert!(
            matches!(&cdata_head.node, Exp::Var(module_path, name, Inference::DontInfer)
                if *module_path == vec!["Basis".to_string()] && name == "cdata"),
            "expected Basis.cdata with DontInfer, got {:?}",
            cdata_head.node
        );
        assert!(
            matches!(&wildcard_ctx.node, crate::source::Con::Wild(_)),
            "expected wildcard ctx constructor, got {:?}",
            wildcard_ctx.node
        );
    }
}
