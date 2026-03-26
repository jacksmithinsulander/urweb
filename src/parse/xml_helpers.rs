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
    /// A constructor-level argument: `[nm]`, `[nm :: K]`, `[nm ::: K]`
    ConArg(Explicitness, String, Option<LocKind>),
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
                let (name, inner) = match p.node {
                    Pat::Var(x) => (x, acc),
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
                        (fresh, case_e)
                    }
                };
                Located::dummy(Exp::Abs(name, None, Box::new(inner)))
            }
            FunParam::ConArg(exp, nm, opt_k) => {
                let k = opt_k.unwrap_or_else(|| Located::dummy(Kind::Wild));
                Located::dummy(Exp::CAbs(exp, nm, Box::new(k), Box::new(acc)))
            }
            FunParam::Disjoint(c1, c2) => Located::dummy(Exp::Disjoint(c1, c2, Box::new(acc))),
        })
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
        let empty_rec = Located::new(Exp::Record(vec![], false), pos.clone());
        Located::new(Exp::App(Box::new(head_exp), Box::new(empty_rec)), pos)
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
