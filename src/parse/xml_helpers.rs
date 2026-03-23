//! Helper types and functions for XML desugaring in the LALRPOP grammar.

use crate::error_types::{Located, Span};
use crate::source::*;

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
