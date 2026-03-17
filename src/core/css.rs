//! css — CSS property-usage summary pass.
//!
//! Ports `css.sml`. Runs on the Core AST after the shake passes.
//!
//! The pass walks the Core file and, for each application of `Basis.tag`
//! (which represents an HTML tag), records which CSS property categories
//! are used.  The result is a `Summary` containing:
//! - `overall`: the union of all properties used anywhere in the file.
//! - `classes`: per-style-class property summaries (keyed by style name).
//!
//! This is used only by the CSS diagnostic tool (`ur --css`); the main
//! compilation pipeline does not depend on its output.

use std::collections::BTreeMap;

use crate::core::{Declaration, Expression, File, LocatedExpression};

// ---------------------------------------------------------------------------
// Property categories (mirror SML `inheritable` / `others`)
// ---------------------------------------------------------------------------

/// CSS properties that are inherited by child elements.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Inheritable {
    Block,
    List,
    Table,
    Caption,
    Td,
}

/// CSS properties that are not inherited.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Other {
    OBlock,
    OTable,
    OTd,
    Tr,
    NonReplacedInline,
    ReplacedInline,
    Width,
    Height,
}

pub type TagSummary = (Vec<Inheritable>, Vec<Other>);

fn merge_into(target: &mut Vec<Inheritable>, src: &[Inheritable]) {
    for x in src {
        if !target.contains(x) {
            target.push(x.clone());
        }
    }
}

fn merge_other_into(target: &mut Vec<Other>, src: &[Other]) {
    for x in src {
        if !target.contains(x) {
            target.push(x.clone());
        }
    }
}

fn merge_summary(a: &mut TagSummary, b: &TagSummary) {
    merge_into(&mut a.0, &b.0);
    merge_other_into(&mut a.1, &b.1);
}

/// Merge parent summary with child inheritable list (`mergePC` in SML).
fn merge_parent_child(parent: &TagSummary, child_inh: &[Inheritable]) -> TagSummary {
    let mut inh = parent.0.clone();
    merge_into(&mut inh, child_inh);
    (inh, parent.1.clone())
}

// ---------------------------------------------------------------------------
// Tag table (mirrors SML `tags`)
// ---------------------------------------------------------------------------

fn build_tag_table() -> BTreeMap<&'static str, TagSummary> {
    let block: TagSummary = (
        vec![Inheritable::Block],
        vec![Other::OBlock, Other::Width, Other::Height],
    );
    let inline: TagSummary = (vec![], vec![Other::NonReplacedInline]);
    let list: TagSummary = (
        vec![Inheritable::Block, Inheritable::List],
        vec![Other::OBlock, Other::Width, Other::Height],
    );
    let replaced: TagSummary = (
        vec![],
        vec![Other::ReplacedInline, Other::Width, Other::Height],
    );
    let table: TagSummary = (
        vec![Inheritable::Block, Inheritable::Table],
        vec![Other::OBlock, Other::OTable, Other::Width, Other::Height],
    );
    let tr: TagSummary = (
        vec![Inheritable::Block],
        vec![Other::OBlock, Other::Tr, Other::Height],
    );
    let td: TagSummary = (
        vec![Inheritable::Block, Inheritable::Td],
        vec![Other::OBlock, Other::OTd, Other::Width],
    );

    let entries: &[(&str, TagSummary)] = &[
        ("span", inline.clone()),
        ("div", block.clone()),
        ("p", block.clone()),
        ("b", inline.clone()),
        ("i", inline.clone()),
        ("tt", inline.clone()),
        ("h1", block.clone()),
        ("h2", block.clone()),
        ("h3", block.clone()),
        ("h4", block.clone()),
        ("h5", block.clone()),
        ("h6", block.clone()),
        ("li", list.clone()),
        ("ol", list.clone()),
        ("ul", list.clone()),
        ("hr", block.clone()),
        ("a", inline.clone()),
        ("img", replaced.clone()),
        ("form", block.clone()),
        ("hidden", replaced.clone()),
        ("textbox", replaced.clone()),
        ("password", replaced.clone()),
        ("textarea", replaced.clone()),
        ("checkbox", replaced.clone()),
        ("upload", replaced.clone()),
        ("radio", replaced.clone()),
        ("select", replaced.clone()),
        ("submit", replaced.clone()),
        ("label", inline.clone()),
        ("ctextbox", replaced.clone()),
        ("cpassword", replaced.clone()),
        ("button", replaced.clone()),
        ("ccheckbox", replaced.clone()),
        ("cradio", replaced.clone()),
        ("cselect", replaced.clone()),
        ("ctextarea", replaced.clone()),
        ("tabl", table),
        ("tr", tr),
        ("th", td.clone()),
        ("td", td),
    ];
    entries.iter().cloned().collect()
}

// ---------------------------------------------------------------------------
// Summary result
// ---------------------------------------------------------------------------

/// The CSS summary returned by `summarize`.
#[derive(Debug, Default)]
pub struct Summary {
    /// Union of all CSS properties used anywhere.
    pub overall: TagSummary,
    /// Per-style-class property summaries, sorted by class name.
    pub classes: Vec<(String, TagSummary)>,
}

// ---------------------------------------------------------------------------
// Traversal state
// ---------------------------------------------------------------------------

struct Summarizer {
    tags: BTreeMap<&'static str, TagSummary>,
    /// name→(style_name_or_None, summary): globals table (by Named id).
    globals: BTreeMap<usize, (Option<String>, TagSummary)>,
    /// class id → accumulated summary.
    classes: BTreeMap<usize, TagSummary>,
}

impl Summarizer {
    fn new() -> Self {
        Summarizer {
            tags: build_tag_table(),
            globals: BTreeMap::new(),
            classes: BTreeMap::new(),
        }
    }

    // -----------------------------------------------------------------------
    // Peel a chain of App/CApp/KApp to find the head.
    // -----------------------------------------------------------------------

    fn get_tag_name(e: &LocatedExpression) -> Option<&str> {
        match &e.node {
            Expression::Ffi(m, x) if m == "Basis" => Some(x.as_str()),
            Expression::CApp(f, _) => Self::get_tag_name(f),
            Expression::App(f, _) => Self::get_tag_name(f),
            Expression::KApp(f, _) => Self::get_tag_name(f),
            _ => None,
        }
    }

    // -----------------------------------------------------------------------
    // Walk an expression, returning the summary of properties it uses.
    // -----------------------------------------------------------------------

    fn exp(&mut self, e: &LocatedExpression) -> TagSummary {
        match &e.node {
            Expression::Named(n) => {
                if let Some((_, sm)) = self.globals.get(n) {
                    sm.clone()
                } else {
                    (vec![], vec![])
                }
            }

            // The big pattern: Basis.tag applied to many arguments.
            // SML matches exactly 8 EApp layers + 8 ECApp layers + EFfi.
            // We use a simpler heuristic: detect any EApp/ECApp chain that
            // ends at EFfi("Basis", "tag") and whose last two explicit EApp
            // args are (xml_body, attrs) — then look up the first EApp arg.
            //
            // The full SML pattern is a 15-level nested EApp/ECApp. We peel
            // the application chain and check if the head is Basis.tag.
            Expression::App(f, xml) => {
                // Peel the outer-most App: f is the partially-applied tag, xml is the body.
                let xml_sm = self.exp(xml);
                let f_sm = self.exp_app_tag(f, &xml_sm);
                f_sm
            }

            Expression::CApp(f, _) => self.exp(f),
            Expression::KApp(f, _) => self.exp(f),
            Expression::Abs(_, _, _, body) => self.exp(body),
            Expression::CAbs(_, _, body) => self.exp(body),
            Expression::KAbs(_, body) => self.exp(body),
            Expression::FfiApp(_, _, args) => {
                let mut sm: TagSummary = (vec![], vec![]);
                for (a, _) in args {
                    let s = self.exp(a);
                    merge_summary(&mut sm, &s);
                }
                sm
            }
            Expression::Record(fields) => {
                let mut sm: TagSummary = (vec![], vec![]);
                for (_, v, _) in fields {
                    let s = self.exp(v);
                    merge_summary(&mut sm, &s);
                }
                sm
            }
            Expression::Field(e2, _, _) => self.exp(e2),
            Expression::Concat(a, _, b, _) => {
                let mut sm = self.exp(a);
                let sb = self.exp(b);
                merge_summary(&mut sm, &sb);
                sm
            }
            Expression::Cut(e2, _, _) | Expression::CutMulti(e2, _, _) => self.exp(e2),
            Expression::Case(disc, arms, _) => {
                let mut sm = self.exp(disc);
                for (_, arm) in arms {
                    let s = self.exp(arm);
                    merge_summary(&mut sm, &s);
                }
                sm
            }
            Expression::Write(e2) => self.exp(e2),
            Expression::Closure(_, envs) => {
                let mut sm: TagSummary = (vec![], vec![]);
                for a in envs {
                    let s = self.exp(a);
                    merge_summary(&mut sm, &s);
                }
                sm
            }
            Expression::Let(_, _, e2, body) => {
                let mut sm = self.exp(e2);
                let sb = self.exp(body);
                merge_summary(&mut sm, &sb);
                sm
            }
            Expression::ServerCall(_, args, _, _) => {
                let mut sm: TagSummary = (vec![], vec![]);
                for a in args {
                    let s = self.exp(a);
                    merge_summary(&mut sm, &s);
                }
                sm
            }
            _ => (vec![], vec![]),
        }
    }

    /// Handle the EApp chain for `Basis.tag` applications.
    /// Returns the merged summary.
    fn exp_app_tag(&mut self, e: &LocatedExpression, xml_sm: &TagSummary) -> TagSummary {
        // Check if this (after peeling CApp/KApp) is the `Basis.tag` applied to:
        //   tag_expr attrs_expr
        // The full application in SML is: tag applied to many CApp args, then
        // EApp(EApp(..., class_id), tag_constructor_expr), attrs, xml.
        // We simplify: detect App(App(..., attrs), _) where head is Basis.tag.
        match &e.node {
            Expression::App(inner, attrs) => {
                let attrs_sm = self.exp(attrs);
                let merged_xml = {
                    let mut s = xml_sm.clone();
                    merge_summary(&mut s, &attrs_sm);
                    s
                };
                // Check if inner (peeling further) involves class + tag.
                match &inner.node {
                    Expression::App(maybe_class_app, tag_expr) => {
                        // Look for class: ENamed(class_id) after peeling.
                        let class_id = Self::extract_named_from_peel(maybe_class_app);
                        let tag_name = Self::get_tag_name(tag_expr);

                        if let Some(tag_str) = tag_name {
                            if let Some(tag_summary) = self.tags.get(tag_str) {
                                let tag_summary = tag_summary.clone();
                                let combined = merge_parent_child(&tag_summary, &merged_xml.0);

                                if let Some(cid) = class_id {
                                    let old =
                                        self.classes.entry(cid).or_insert_with(|| (vec![], vec![]));
                                    merge_summary(old, &combined);
                                }
                                // Return the inheritable part + tag's other properties.
                                let mut result = merged_xml.clone();
                                merge_into(&mut result.0, &tag_summary.0);
                                return result;
                            }
                        }

                        // Not a recognized Basis.tag pattern; just recurse.
                        let mut s = self.exp(inner);
                        merge_summary(&mut s, &merged_xml);
                        s
                    }
                    _ => {
                        let mut s = self.exp(inner);
                        merge_summary(&mut s, &merged_xml);
                        s
                    }
                }
            }
            Expression::CApp(f, _) | Expression::KApp(f, _) => self.exp_app_tag(f, xml_sm),
            _ => self.exp(e),
        }
    }

    /// Peel App/CApp/KApp chains to find an ENamed node.
    fn extract_named_from_peel(e: &LocatedExpression) -> Option<usize> {
        match &e.node {
            Expression::Named(n) => Some(*n),
            Expression::App(f, _) => Self::extract_named_from_peel(f),
            Expression::CApp(f, _) => Self::extract_named_from_peel(f),
            Expression::KApp(f, _) => Self::extract_named_from_peel(f),
            _ => None,
        }
    }

    fn decl(&mut self, d: &Declaration) {
        match d {
            Declaration::Val(_, n, _, e, _) => {
                let sm = self.exp(e);
                self.globals.insert(*n, (None, sm));
            }
            Declaration::ValRec(vis) => {
                let mut combined: TagSummary = (vec![], vec![]);
                for (_, _, _, e, _) in vis {
                    let s = self.exp(e);
                    merge_summary(&mut combined, &s);
                }
                for (_, n, _, _, _) in vis {
                    self.globals.insert(*n, (None, combined.clone()));
                }
            }
            Declaration::Style(_, n, s) => {
                self.globals.insert(*n, (Some(s.clone()), (vec![], vec![])));
            }
            _ => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Compute CSS property-usage summary for `file`.
pub fn summarize(file: &File) -> Summary {
    let mut state = Summarizer::new();

    for d in file {
        state.decl(&d.node);
    }

    // Build Overall: union of all globals' summaries.
    let mut overall: TagSummary = (vec![], vec![]);
    for (_, sm) in state.globals.values() {
        merge_summary(&mut overall, sm);
    }

    // Build Classes: map class ids to their accumulated summaries,
    // then resolve to style names via globals.
    let mut classes: Vec<(String, TagSummary)> = state
        .classes
        .into_iter()
        .filter_map(|(id, sm)| {
            if let Some((Some(style_name), _)) = state.globals.get(&id) {
                Some((style_name.clone(), sm))
            } else {
                None
            }
        })
        .collect();
    classes.sort_by(|(a, _), (b, _)| a.cmp(b));

    Summary { overall, classes }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::File;

    #[test]
    fn summarize_empty_file() {
        let file: File = vec![];
        let s = summarize(&file);
        assert!(s.overall.0.is_empty());
        assert!(s.overall.1.is_empty());
        assert!(s.classes.is_empty());
    }

    #[test]
    fn build_tag_table_has_div() {
        let t = build_tag_table();
        assert!(t.contains_key("div"));
        let (inh, _) = &t["div"];
        assert!(inh.contains(&Inheritable::Block));
    }
}
