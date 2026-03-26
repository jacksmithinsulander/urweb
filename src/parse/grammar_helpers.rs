//! Small helpers and enums used only from `grammar.lalrpop` (LALRPOP allows only `use` before `grammar;`).

use crate::error_types::{Located, Span};
use crate::source::{Con, Exp, Inference, LocCon, LocExp, LocPat, Pat};

/// `Pat = PatCore PatOptAnn?` in one production so `:` after `PatCore` is never a reduce/shift
/// split between two `Pat` rules (LangSec / LR(1)).
pub fn fold_pat_opt_ann(l: usize, r: usize, p: Pat, ann: Option<LocCon>) -> LocPat {
    let span = Span::from_offsets("", l, r, &[]);
    match ann {
        None => Located::new(p, span),
        Some(c) => Located::new(Pat::Annot(Box::new(Located::dummy(p)), c), span),
    }
}

/// Left-fold relational operators: `AddExp (relop AddExp)*` without left-recursive `CmpExp`.
pub fn fold_cmp_rel_chain(first: LocExp, tail: Vec<(String, LocExp)>) -> LocExp {
    let mut acc = first;
    for (op, rhs) in tail {
        let l = acc.span.first.clone();
        let r = rhs.span.last.clone();
        let file = acc.span.file.clone();
        acc = Located::new(
            Exp::Infix(op, Box::new(acc), Box::new(rhs)),
            Span {
                file,
                first: l,
                last: r,
            },
        );
    }
    acc
}

/// Left-fold `andalso` / `orelse` after `BoolExp` (no left-recursive `NonSeqExp`).
pub fn fold_nonseq_chain(mut acc: LocExp, tail: Vec<(bool, LocExp)>) -> Exp {
    for (is_andalso, rhs) in tail {
        acc = if is_andalso {
            Located::new(
                Exp::Case(
                    Box::new(acc),
                    vec![
                        (
                            Located::dummy(Pat::Con(vec!["Basis".into()], "True".into(), None)),
                            rhs,
                        ),
                        (
                            Located::dummy(Pat::Con(vec!["Basis".into()], "False".into(), None)),
                            Located::dummy(Exp::Var(
                                vec!["Basis".into()],
                                "False".into(),
                                Inference::DontInfer,
                            )),
                        ),
                    ],
                ),
                Span::dummy(),
            )
        } else {
            Located::new(
                Exp::Case(
                    Box::new(acc),
                    vec![
                        (
                            Located::dummy(Pat::Con(vec!["Basis".into()], "True".into(), None)),
                            Located::dummy(Exp::Var(
                                vec!["Basis".into()],
                                "True".into(),
                                Inference::DontInfer,
                            )),
                        ),
                        (
                            Located::dummy(Pat::Con(vec!["Basis".into()], "False".into(), None)),
                            rhs,
                        ),
                    ],
                ),
                Span::dummy(),
            )
        };
    }
    acc.node
}

/// `urweb.grm` `rconn`: bare `rpath` fields default to unit (or pun for lowercase symbols).
pub fn con_record_field_pun(name: LocCon) -> (LocCon, LocCon) {
    match &name.node {
        Con::Var(ms, x)
            if ms.is_empty() && x.chars().next().map(|c| c.is_uppercase()).unwrap_or(false) =>
        {
            let name_con = Located::dummy(Con::Name(x.clone()));
            (name_con, Located::dummy(Con::Unit))
        }
        _ => (name.clone(), name),
    }
}
