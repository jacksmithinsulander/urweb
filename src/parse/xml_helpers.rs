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

pub fn materialize_dummy_spans_in_exp(mut expression: LocExp, anchor: &Span) -> LocExp {
    fn fill_kind_spans(kind: &mut LocKind, anchor: &Span) {
        if is_dummy_parser_repair_span(&kind.span) {
            kind.span = anchor.clone();
        }
        match &mut kind.node {
            Kind::Arrow(left, right) => {
                fill_kind_spans(left, anchor);
                fill_kind_spans(right, anchor);
            }
            Kind::Record(inner) | Kind::Fun(_, inner) => fill_kind_spans(inner, anchor),
            Kind::Tuple(items) => {
                for item in items {
                    fill_kind_spans(item, anchor);
                }
            }
            Kind::Type | Kind::Name | Kind::Unit | Kind::Wild | Kind::Var(_) => {}
        }
    }

    fn fill_con_spans(constructor: &mut LocCon, anchor: &Span) {
        if is_dummy_parser_repair_span(&constructor.span) {
            constructor.span = anchor.clone();
        }
        match &mut constructor.node {
            Con::Annot(inner, kind) => {
                fill_con_spans(inner, anchor);
                fill_kind_spans(kind, anchor);
            }
            Con::TFun(left, right) | Con::App(left, right) | Con::Concat(left, right) => {
                fill_con_spans(left, anchor);
                fill_con_spans(right, anchor);
            }
            Con::TCFun(_, _, kind, body) => {
                fill_kind_spans(kind, anchor);
                fill_con_spans(body, anchor);
            }
            Con::TRecord(inner) | Con::KAbs(_, inner) | Con::TKFun(_, inner) => {
                fill_con_spans(inner, anchor);
            }
            Con::TDisjoint(left, right, body) => {
                fill_con_spans(left, anchor);
                fill_con_spans(right, anchor);
                fill_con_spans(body, anchor);
            }
            Con::Abs(_, kind, body) => {
                if let Some(kind) = kind {
                    fill_kind_spans(kind, anchor);
                }
                fill_con_spans(body, anchor);
            }
            Con::Record(fields) => {
                for (field_name, field_value) in fields {
                    fill_con_spans(field_name, anchor);
                    fill_con_spans(field_value, anchor);
                }
            }
            Con::Tuple(items) => {
                for item in items {
                    fill_con_spans(item, anchor);
                }
            }
            Con::Proj(inner, _) => fill_con_spans(inner, anchor),
            Con::Enum(arms) => {
                for (_, payloads) in arms {
                    for payload in payloads {
                        fill_con_spans(payload, anchor);
                    }
                }
            }
            Con::Wild(kind) => fill_kind_spans(kind, anchor),
            Con::Var(_, _) | Con::Name(_) | Con::Map | Con::Unit => {}
        }
    }

    fn fill_pat_spans(pattern: &mut LocPat, anchor: &Span) {
        if is_dummy_parser_repair_span(&pattern.span) {
            pattern.span = anchor.clone();
        }
        match &mut pattern.node {
            Pat::Con(_, _, Some(argument_pattern)) => fill_pat_spans(argument_pattern, anchor),
            Pat::Record(fields, _) => {
                for (_, field_pattern) in fields {
                    fill_pat_spans(field_pattern, anchor);
                }
            }
            Pat::Annot(inner_pattern, annotation) => {
                fill_pat_spans(inner_pattern, anchor);
                fill_con_spans(annotation, anchor);
            }
            Pat::Var(_) | Pat::Prim(_) | Pat::Con(_, _, None) => {}
        }
    }

    fn preserves_lambda_annotation_repair_marker(
        pattern: &LocPat,
        branch_expression: &LocExp,
    ) -> bool {
        matches!(
            (&pattern.node, &branch_expression.node),
            (
                Pat::Annot(inner_pattern, annotation_constructor),
                Exp::Abs(_, None, _)
            )
                if matches!(inner_pattern.as_ref().node, Pat::Var(_))
                    && matches!(&annotation_constructor.node, Con::Var(module_path, _) if module_path.is_empty())
                    && is_dummy_parser_repair_span(&branch_expression.span)
        )
    }

    fn fill_exp_spans(expression: &mut LocExp, anchor: &Span) {
        if is_dummy_parser_repair_span(&expression.span) {
            expression.span = anchor.clone();
        }
        match &mut expression.node {
            Exp::Annot(inner, constructor) => {
                fill_exp_spans(inner, anchor);
                fill_con_spans(constructor, anchor);
            }
            Exp::App(function_expression, argument_expression)
            | Exp::Concat(function_expression, argument_expression)
            | Exp::Infix(_, function_expression, argument_expression) => {
                fill_exp_spans(function_expression, anchor);
                fill_exp_spans(argument_expression, anchor);
            }
            Exp::Abs(_, annotation, body) => {
                if let Some(annotation) = annotation {
                    fill_con_spans(annotation, anchor);
                }
                fill_exp_spans(body, anchor);
            }
            Exp::CApp(inner, constructor) => {
                fill_exp_spans(inner, anchor);
                fill_con_spans(constructor, anchor);
            }
            Exp::CAbs(_, _, kind, body) => {
                fill_kind_spans(kind, anchor);
                fill_exp_spans(body, anchor);
            }
            Exp::Disjoint(left, right, body) => {
                fill_con_spans(left, anchor);
                fill_con_spans(right, anchor);
                fill_exp_spans(body, anchor);
            }
            Exp::DisjointApp(inner) | Exp::KAbs(_, inner) => fill_exp_spans(inner, anchor),
            Exp::Record(fields, _) => {
                for (field_name, field_expression) in fields {
                    fill_con_spans(field_name, anchor);
                    fill_exp_spans(field_expression, anchor);
                }
            }
            Exp::Field(inner, field_constructor)
            | Exp::Cut(inner, field_constructor)
            | Exp::CutMulti(inner, field_constructor) => {
                fill_exp_spans(inner, anchor);
                fill_con_spans(field_constructor, anchor);
            }
            Exp::Case(scrutinee, branches) => {
                fill_exp_spans(scrutinee, anchor);
                for (pattern, branch_expression) in branches {
                    fill_pat_spans(pattern, anchor);
                    if preserves_lambda_annotation_repair_marker(pattern, branch_expression) {
                        if let Exp::Abs(_, _, inner_body) = &mut branch_expression.node {
                            fill_exp_spans(inner_body, anchor);
                        }
                    } else {
                        fill_exp_spans(branch_expression, anchor);
                    }
                }
            }
            Exp::Let(declarations, body) => {
                for declaration in declarations {
                    if is_dummy_parser_repair_span(&declaration.span) {
                        declaration.span = anchor.clone();
                    }
                    match &mut declaration.node {
                        EDecl::Val(pattern, bound_expression) => {
                            fill_pat_spans(pattern, anchor);
                            fill_exp_spans(bound_expression, anchor);
                        }
                        EDecl::ValRec(bindings) => {
                            for (_, annotation, bound_expression) in bindings {
                                if let Some(annotation) = annotation {
                                    fill_con_spans(annotation, anchor);
                                }
                                fill_exp_spans(bound_expression, anchor);
                            }
                        }
                    }
                }
                fill_exp_spans(body, anchor);
            }
            Exp::Prim(_) | Exp::Var(_, _, _) | Exp::Wild | Exp::Hole => {}
        }
    }

    fill_exp_spans(&mut expression, anchor);
    expression
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

/// Mirror the ML grammar's `makeAttr` helper:
/// `type` -> `Typ`, `name` -> `Nam`, otherwise capitalize and translate `-` to `_`.
pub fn capitalize_attr(s: &str) -> String {
    match s {
        "type" => "Typ".to_string(),
        "name" => "Nam".to_string(),
        _ => {
            let translated = s.replace('-', "_");
            let mut chars = translated.chars();
            match chars.next() {
                None => String::new(),
                Some(c) => c.to_uppercase().to_string() + chars.as_str(),
            }
        }
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
        XmlAttr::Normal(k, v) => av.push((k.clone(), bless_xml_literal_attr_value(&k, v))),
    }
    acc
}

fn basis_var_expression(name: &str, span: Span) -> LocExp {
    Located::new(
        Exp::Var(vec!["Basis".into()], name.into(), Inference::Infer),
        span,
    )
}

fn is_primitive_literal_expression(expression: &LocExp) -> bool {
    matches!(expression.node, Exp::Prim(_))
}

fn bless_xml_literal_attr_value(attr_name: &LocCon, attr_value: LocExp) -> LocExp {
    let Con::Name(name) = &attr_name.node else {
        return attr_value;
    };
    if !is_primitive_literal_expression(&attr_value) {
        return attr_value;
    }

    let bless_function_name = match name.as_str() {
        "Href" | "Src" => Some("bless"),
        "Nam" => Some("blessMeta"),
        _ => None,
    };
    let Some(bless_function_name) = bless_function_name else {
        return attr_value;
    };

    let span = attr_value.span.clone();
    Located::new(
        Exp::App(
            Box::new(basis_var_expression(bless_function_name, span.clone())),
            Box::new(attr_value),
        ),
        span,
    )
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
