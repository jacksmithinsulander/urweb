//! Repair LALRPOP spans: empty `file`, placeholder `line == 1` cols = UTF-8 byte offsets in the
//! **preprocessed** buffer (`from_offsets("", l, r, &[])`).
//!
//! Spans that already have real line numbers (wrappers like `"<basis>"` / `"<top>"`, or any
//! `line != 1`) skip remapping and only update an empty `file` field when the label is supplied.

use crate::error_types::Located;

use super::{Con, Decl, EDecl, Exp, File, Kind, Pat, Sgn, SgnItem, Str};

/// Walk a parsed `.ur` [`File`] and fix every [`Located`] span using `file_label` + lexer buffer `preprocessed`.
pub(crate) fn attach_file_label_to_source_file(
    file: &mut File,
    file_label: &str,
    preprocessed: &str,
) {
    let line_table = crate::error_types::Span::newline_byte_indices_in_utf8_source(preprocessed);
    for decl in file.iter_mut() {
        attach_on_located(decl, file_label, preprocessed, &line_table, walk_decl);
    }
}

/// Walk parsed `.urs` items and fix spans (same as [`attach_file_label_to_source_file`]).
pub(crate) fn attach_file_label_to_signature_items(
    items: &mut [super::LocSgnItem],
    file_label: &str,
    preprocessed: &str,
) {
    let line_table = crate::error_types::Span::newline_byte_indices_in_utf8_source(preprocessed);
    for item in items.iter_mut() {
        attach_on_located(item, file_label, preprocessed, &line_table, walk_sgn_item);
    }
}

fn attach_on_located<T, F>(
    located: &mut Located<T>,
    file_label: &str,
    pre: &str,
    line_table: &[usize],
    walk_inner: F,
) where
    F: FnOnce(&mut T, &str, &str, &[usize]),
{
    located
        .span
        .remap_after_lalrpop_parse_with_line_table(file_label, pre, line_table);
    walk_inner(&mut located.node, file_label, pre, line_table);
}

fn walk_kind(kind: &mut Kind, label: &str, pre: &str, line_table: &[usize]) {
    match kind {
        Kind::Arrow(a, b) => {
            attach_on_located(a, label, pre, line_table, walk_kind);
            attach_on_located(b, label, pre, line_table, walk_kind);
        }
        Kind::Record(inner) => attach_on_located(inner, label, pre, line_table, walk_kind),
        Kind::Tuple(ks) => {
            for k in ks.iter_mut() {
                attach_on_located(k, label, pre, line_table, walk_kind);
            }
        }
        Kind::Fun(_, body) => attach_on_located(body, label, pre, line_table, walk_kind),
        Kind::Type | Kind::Name | Kind::Unit | Kind::Wild | Kind::Var(_) => {}
    }
}

fn walk_con(con: &mut Con, label: &str, pre: &str, line_table: &[usize]) {
    match con {
        Con::Annot(c, k) => {
            attach_on_located(c, label, pre, line_table, walk_con);
            attach_on_located(k, label, pre, line_table, walk_kind);
        }
        Con::TFun(a, b) => {
            attach_on_located(a, label, pre, line_table, walk_con);
            attach_on_located(b, label, pre, line_table, walk_con);
        }
        Con::TCFun(_, _, k, body) => {
            attach_on_located(k, label, pre, line_table, walk_kind);
            attach_on_located(body, label, pre, line_table, walk_con);
        }
        Con::TRecord(r) => attach_on_located(r, label, pre, line_table, walk_con),
        Con::TDisjoint(a, b, t) => {
            attach_on_located(a, label, pre, line_table, walk_con);
            attach_on_located(b, label, pre, line_table, walk_con);
            attach_on_located(t, label, pre, line_table, walk_con);
        }
        Con::Var(_, _) => {}
        Con::App(f, x) => {
            attach_on_located(f, label, pre, line_table, walk_con);
            attach_on_located(x, label, pre, line_table, walk_con);
        }
        Con::Abs(_, ko, body) => {
            if let Some(k) = ko {
                attach_on_located(k.as_mut(), label, pre, line_table, walk_kind);
            }
            attach_on_located(body, label, pre, line_table, walk_con);
        }
        Con::KAbs(_, body) => attach_on_located(body, label, pre, line_table, walk_con),
        Con::TKFun(_, body) => attach_on_located(body, label, pre, line_table, walk_con),
        Con::Name(_) | Con::Map | Con::Unit => {}
        Con::Record(fields) => {
            for (n, v) in fields.iter_mut() {
                attach_on_located(n, label, pre, line_table, walk_con);
                attach_on_located(v, label, pre, line_table, walk_con);
            }
        }
        Con::Concat(a, b) => {
            attach_on_located(a, label, pre, line_table, walk_con);
            attach_on_located(b, label, pre, line_table, walk_con);
        }
        Con::Tuple(cs) => {
            for c in cs.iter_mut() {
                attach_on_located(c, label, pre, line_table, walk_con);
            }
        }
        Con::Proj(inner, _) => attach_on_located(inner, label, pre, line_table, walk_con),
        Con::Wild(k) => attach_on_located(k, label, pre, line_table, walk_kind),
        Con::Enum(arms) => {
            // Walk each arm's argument constructors for span attachment.
            for (_, arg_cons) in arms.iter_mut() {
                for arg_con in arg_cons.iter_mut() {
                    attach_on_located(arg_con, label, pre, line_table, walk_con);
                }
            }
        }
    }
}

fn walk_pat(pat: &mut Pat, label: &str, pre: &str, line_table: &[usize]) {
    match pat {
        Pat::Var(_) | Pat::Prim(_) => {}
        Pat::Con(_, _, arg) => {
            if let Some(p) = arg.as_mut() {
                attach_on_located(p.as_mut(), label, pre, line_table, walk_pat);
            }
        }
        Pat::Record(fields, _) => {
            for (_, p) in fields.iter_mut() {
                attach_on_located(p, label, pre, line_table, walk_pat);
            }
        }
        Pat::Annot(p, c) => {
            attach_on_located(p, label, pre, line_table, walk_pat);
            attach_on_located(c, label, pre, line_table, walk_con);
        }
    }
}

fn walk_exp(exp: &mut Exp, label: &str, pre: &str, line_table: &[usize]) {
    match exp {
        Exp::Annot(e, c) => {
            attach_on_located(e, label, pre, line_table, walk_exp);
            attach_on_located(c, label, pre, line_table, walk_con);
        }
        Exp::Prim(_) | Exp::Var(_, _, _) | Exp::Wild | Exp::Hole => {}
        Exp::App(f, x) => {
            attach_on_located(f, label, pre, line_table, walk_exp);
            attach_on_located(x, label, pre, line_table, walk_exp);
        }
        Exp::Abs(_, to, body) => {
            if let Some(t) = to {
                attach_on_located(t, label, pre, line_table, walk_con);
            }
            attach_on_located(body, label, pre, line_table, walk_exp);
        }
        Exp::CApp(e, c) => {
            attach_on_located(e, label, pre, line_table, walk_exp);
            attach_on_located(c, label, pre, line_table, walk_con);
        }
        Exp::CAbs(_, _, k, body) => {
            attach_on_located(k, label, pre, line_table, walk_kind);
            attach_on_located(body, label, pre, line_table, walk_exp);
        }
        Exp::Disjoint(a, b, body) => {
            attach_on_located(a, label, pre, line_table, walk_con);
            attach_on_located(b, label, pre, line_table, walk_con);
            attach_on_located(body, label, pre, line_table, walk_exp);
        }
        Exp::DisjointApp(e) => attach_on_located(e, label, pre, line_table, walk_exp),
        Exp::KAbs(_, body) => attach_on_located(body, label, pre, line_table, walk_exp),
        Exp::Record(fields, _) => {
            for (nc, ve) in fields.iter_mut() {
                attach_on_located(nc, label, pre, line_table, walk_con);
                attach_on_located(ve, label, pre, line_table, walk_exp);
            }
        }
        Exp::Field(e, c) => {
            attach_on_located(e, label, pre, line_table, walk_exp);
            attach_on_located(c, label, pre, line_table, walk_con);
        }
        Exp::Concat(a, b) => {
            attach_on_located(a, label, pre, line_table, walk_exp);
            attach_on_located(b, label, pre, line_table, walk_exp);
        }
        Exp::Cut(a, b) | Exp::CutMulti(a, b) => {
            attach_on_located(a, label, pre, line_table, walk_exp);
            attach_on_located(b, label, pre, line_table, walk_con);
        }
        Exp::Case(e, arms) => {
            attach_on_located(e, label, pre, line_table, walk_exp);
            for (p, rhs) in arms.iter_mut() {
                attach_on_located(p, label, pre, line_table, walk_pat);
                attach_on_located(rhs, label, pre, line_table, walk_exp);
            }
        }
        Exp::Let(bindings, body) => {
            for b in bindings.iter_mut() {
                attach_on_located(b, label, pre, line_table, walk_edecl);
            }
            attach_on_located(body, label, pre, line_table, walk_exp);
        }
        Exp::Infix(_, a, b) => {
            attach_on_located(a, label, pre, line_table, walk_exp);
            attach_on_located(b, label, pre, line_table, walk_exp);
        }
    }
}

fn walk_edecl(ed: &mut EDecl, label: &str, pre: &str, line_table: &[usize]) {
    match ed {
        EDecl::Val(p, e) => {
            attach_on_located(p, label, pre, line_table, walk_pat);
            attach_on_located(e, label, pre, line_table, walk_exp);
        }
        EDecl::ValRec(bindings) => {
            for (_, ot, e) in bindings.iter_mut() {
                if let Some(t) = ot {
                    attach_on_located(t, label, pre, line_table, walk_con);
                }
                attach_on_located(e, label, pre, line_table, walk_exp);
            }
        }
    }
}

fn walk_sgn(sgn: &mut Sgn, label: &str, pre: &str, line_table: &[usize]) {
    match sgn {
        Sgn::Const(items) => {
            for it in items.iter_mut() {
                attach_on_located(it, label, pre, line_table, walk_sgn_item);
            }
        }
        Sgn::Var(_) => {}
        Sgn::Fun(_, dom, ran) => {
            attach_on_located(dom, label, pre, line_table, walk_sgn);
            attach_on_located(ran, label, pre, line_table, walk_sgn);
        }
        Sgn::Where(inner, _, _, c) => {
            attach_on_located(inner, label, pre, line_table, walk_sgn);
            attach_on_located(c, label, pre, line_table, walk_con);
        }
        Sgn::Proj(_, _, _) => {}
    }
}

fn walk_sgn_item(item: &mut SgnItem, label: &str, pre: &str, line_table: &[usize]) {
    match item {
        SgnItem::ConAbs(_, k) => attach_on_located(k, label, pre, line_table, walk_kind),
        SgnItem::Con(_, ko, c) => {
            if let Some(k) = ko {
                attach_on_located(k.as_mut(), label, pre, line_table, walk_kind);
            }
            attach_on_located(c, label, pre, line_table, walk_con);
        }
        SgnItem::Datatype(dts) => {
            for dt in dts.iter_mut() {
                for (_, oty) in dt.constrs.iter_mut() {
                    if let Some(t) = oty {
                        attach_on_located(t, label, pre, line_table, walk_con);
                    }
                }
            }
        }
        SgnItem::DatatypeImp(_, _, _) => {}
        SgnItem::Val(_, c) => attach_on_located(c, label, pre, line_table, walk_con),
        SgnItem::Table(_, c, e1, e2) => {
            attach_on_located(c, label, pre, line_table, walk_con);
            attach_on_located(e1, label, pre, line_table, walk_exp);
            attach_on_located(e2, label, pre, line_table, walk_exp);
        }
        SgnItem::Str(_, sg) => attach_on_located(sg, label, pre, line_table, walk_sgn),
        SgnItem::Sgn(_, sg) => attach_on_located(sg, label, pre, line_table, walk_sgn),
        SgnItem::Include(sg) => attach_on_located(sg, label, pre, line_table, walk_sgn),
        SgnItem::Constraint(a, b) => {
            attach_on_located(a, label, pre, line_table, walk_con);
            attach_on_located(b, label, pre, line_table, walk_con);
        }
        SgnItem::ClassAbs(_, k) => attach_on_located(k, label, pre, line_table, walk_kind),
        SgnItem::Class(_, k, c) => {
            attach_on_located(k, label, pre, line_table, walk_kind);
            attach_on_located(c, label, pre, line_table, walk_con);
        }
        SgnItem::Functor(_, _, arg, res) => {
            attach_on_located(arg, label, pre, line_table, walk_sgn);
            attach_on_located(res, label, pre, line_table, walk_sgn);
        }
    }
}

fn walk_str(str_node: &mut Str, label: &str, pre: &str, line_table: &[usize]) {
    match str_node {
        Str::Const(decls) => {
            for d in decls.iter_mut() {
                attach_on_located(d, label, pre, line_table, walk_decl);
            }
        }
        Str::Var(_) => {}
        Str::Proj(inner, _) => attach_on_located(inner, label, pre, line_table, walk_str),
        Str::Fun(_, sg, oso, body) => {
            attach_on_located(sg, label, pre, line_table, walk_sgn);
            if let Some(s) = oso {
                attach_on_located(s, label, pre, line_table, walk_sgn);
            }
            attach_on_located(body, label, pre, line_table, walk_str);
        }
        Str::App(a, b) => {
            attach_on_located(a, label, pre, line_table, walk_str);
            attach_on_located(b, label, pre, line_table, walk_str);
        }
    }
}

fn walk_decl(decl: &mut Decl, label: &str, pre: &str, line_table: &[usize]) {
    match decl {
        Decl::Con(_, ko, c) => {
            if let Some(k) = ko {
                attach_on_located(k.as_mut(), label, pre, line_table, walk_kind);
            }
            attach_on_located(c, label, pre, line_table, walk_con);
        }
        Decl::Datatype(dts) => {
            for dt in dts.iter_mut() {
                for (_, oty) in dt.constrs.iter_mut() {
                    if let Some(t) = oty {
                        attach_on_located(t, label, pre, line_table, walk_con);
                    }
                }
            }
        }
        Decl::DatatypeImp(_, _, _) => {}
        Decl::Val(p, e) => {
            attach_on_located(p, label, pre, line_table, walk_pat);
            attach_on_located(e, label, pre, line_table, walk_exp);
        }
        Decl::ValRec(bindings) => {
            for (_, ot, e) in bindings.iter_mut() {
                if let Some(t) = ot {
                    attach_on_located(t, label, pre, line_table, walk_con);
                }
                attach_on_located(e, label, pre, line_table, walk_exp);
            }
        }
        Decl::Sgn(_, sg) => attach_on_located(sg, label, pre, line_table, walk_sgn),
        Decl::Str(_, osgi, _, body, _) => {
            if let Some(sg) = osgi {
                attach_on_located(sg, label, pre, line_table, walk_sgn);
            }
            attach_on_located(body, label, pre, line_table, walk_str);
        }
        Decl::FfiStr(_, sg, _) => attach_on_located(sg, label, pre, line_table, walk_sgn),
        Decl::Open(_, _) | Decl::OpenConstraints(_, _) => {}
        Decl::Constraint(a, b) => {
            attach_on_located(a, label, pre, line_table, walk_con);
            attach_on_located(b, label, pre, line_table, walk_con);
        }
        Decl::Export(s) => attach_on_located(s, label, pre, line_table, walk_str),
        Decl::Table(_, c, e1, e2) => {
            attach_on_located(c, label, pre, line_table, walk_con);
            attach_on_located(e1, label, pre, line_table, walk_exp);
            attach_on_located(e2, label, pre, line_table, walk_exp);
        }
        Decl::Sequence(_) => {}
        Decl::View(_, e) => attach_on_located(e, label, pre, line_table, walk_exp),
        Decl::Index(e1, e2, oc) => {
            attach_on_located(e1, label, pre, line_table, walk_exp);
            attach_on_located(e2, label, pre, line_table, walk_exp);
            if let Some(c) = oc {
                attach_on_located(c, label, pre, line_table, walk_con);
            }
        }
        Decl::Database(_) => {}
        Decl::Cookie(_, c) => attach_on_located(c, label, pre, line_table, walk_con),
        Decl::Style(_) => {}
        Decl::Task(e1, e2) => {
            attach_on_located(e1, label, pre, line_table, walk_exp);
            attach_on_located(e2, label, pre, line_table, walk_exp);
        }
        Decl::Policy(e) => attach_on_located(e, label, pre, line_table, walk_exp),
        Decl::OnError(_, _, _) => {}
        Decl::Ffi(_, _, c) => attach_on_located(c, label, pre, line_table, walk_con),
        Decl::OpenStr(s) => attach_on_located(s, label, pre, line_table, walk_str),
    }
}
