//! Termination checker for the Core IR.
//!
//! Verifies that mutually-recursive function groups (`ValRec`) terminate by
//! checking that every recursive call is on a structurally smaller argument.
//!
//! The algorithm:
//! 1. For each `ValRec` group, peel off leading lambdas to identify formal
//!    arguments, tagging each with a *pedigree*:
//!    - `Arg(func_idx, arg_pos, typ)` — a direct formal argument
//!    - `Subarg(func_idx, arg_pos, typ)` — a structural sub-component of an arg
//!    - `Func(func_idx)` — a reference to one of the recursive functions
//!    - `Rabble` — anything else (no useful structural information)
//!
//! 2. Traverse the body, collecting *calls*: triples
//!    `(caller_func_idx, callee_func_idx, arg_pedigrees)`.
//!
//! 3. Filter to only truly recursive calls (those that participate in a cycle).
//!
//! 4. Search for a *witness* assignment of "which argument position is the
//!    structural-decrease witness" for each function.  If found, every
//!    recursive call must pass a `Subarg(callee_idx, witness_pos, t)` where
//!    `t` is a datatype and the sub-argument comes from the caller's own
//!    witness position.
//!
//! Mirrors `termination.sml`.

use std::collections::{HashMap, HashSet};

use crate::core::*;
use crate::error_types::ErrorReporter;

// ---------------------------------------------------------------------------
// Pedigree — tracks structural provenance of an expression
// ---------------------------------------------------------------------------

/// Describes the structural provenance of an expression value.
#[derive(Debug, Clone)]
enum Pedigree {
    /// A reference to recursive function number `i` in the current group.
    Func(usize),
    /// The `j`-th formal argument of function `i`, with type `typ`.
    Arg(usize, usize, LocatedConstructor),
    /// A structural sub-component of the `j`-th argument of function `i`,
    /// with the *sub-component's* type `typ`.
    Subarg(usize, usize, LocatedConstructor),
    /// Unknown / not useful for termination.
    Rabble,
}

// ---------------------------------------------------------------------------
// Constructor-payload map
// ---------------------------------------------------------------------------

/// Build a map from constructor id → payload type by scanning all Datatype
/// declarations in the file.  Used by `pat_con` to determine the structural
/// type of a matched sub-component.
fn build_con_payload_map(file: &[LocatedDeclaration]) -> HashMap<usize, LocatedConstructor> {
    let mut map = HashMap::new();
    for ld in file {
        if let Declaration::Datatype(dts) = &ld.node {
            for dt in dts {
                for (_, con_id, payload_opt) in &dt.constrs {
                    if let Some(payload) = payload_opt {
                        map.insert(*con_id, payload.clone());
                    }
                }
            }
        }
    }
    map
}

// ---------------------------------------------------------------------------
// is_datatype — does a constructor head reduce to a Named/Ffi type?
// ---------------------------------------------------------------------------

fn is_datatype(t: &LocatedConstructor) -> bool {
    match &t.node {
        Constructor::Named(_) => true,
        Constructor::Ffi(_, _) => true,
        Constructor::App(f, _) => is_datatype(f),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// names_eq — structural equality on constructor names/heads
// ---------------------------------------------------------------------------

fn names_eq(a: &Constructor, b: &Constructor) -> bool {
    match (a, b) {
        (Constructor::Name(s1), Constructor::Name(s2)) => s1 == s2,
        (Constructor::Rel(n1), Constructor::Rel(n2)) => n1 == n2,
        (Constructor::Named(n1), Constructor::Named(n2)) => n1 == n2,
        (Constructor::Ffi(m1, x1), Constructor::Ffi(m2, x2)) => m1 == m2 && x1 == x2,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// pat_con — extract the payload type of a constructor pattern
// ---------------------------------------------------------------------------

/// Given a `PatternConstructor` and the global constructor payload map, return
/// the type of the payload (the type of the value bound inside the
/// constructor).  Returns `None` if the type is not known.
fn pat_con(
    pc: &PatternConstructor,
    payload_map: &HashMap<usize, LocatedConstructor>,
) -> Option<LocatedConstructor> {
    match pc {
        PatternConstructor::Var(id) => payload_map.get(id).cloned(),
        PatternConstructor::Ffi { .. } => None,
    }
}

// ---------------------------------------------------------------------------
// extract_record_fields — get fields from TRecord(Record(...))
// ---------------------------------------------------------------------------

/// Extract record fields from a `Constructor::TRecord` wrapping a
/// `Constructor::Record`.
fn extract_record_fields(
    con: &Constructor,
) -> Option<Vec<(LocatedConstructor, LocatedConstructor)>> {
    match con {
        Constructor::TRecord(inner) => match &inner.node {
            Constructor::Record(_, fields) => Some(fields.clone()),
            _ => None,
        },
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// pat — extend the pedigree environment by processing a pattern
// ---------------------------------------------------------------------------

/// Process a pattern match, pushing new pedigrees onto `penv`.
///
/// `scrutinee_ped` is the pedigree of the value being matched.
fn process_pat(
    penv: &mut Vec<Pedigree>,
    scrutinee_ped: &Pedigree,
    pattern: &LocatedPattern,
    payload_map: &HashMap<usize, LocatedConstructor>,
) {
    match &pattern.node {
        Pattern::Var(_, _) => {
            penv.push(scrutinee_ped.clone());
        }
        Pattern::Prim(_) => {}
        Pattern::Constructor(_, _pc, _type_args, None) => {}
        Pattern::Constructor(_, pc, _type_args, Some(sub_pat)) => {
            let sub_ped = match scrutinee_ped {
                Pedigree::Arg(i, j, _) | Pedigree::Subarg(i, j, _) => {
                    match pat_con(pc, payload_map) {
                        Some(payload_ty) => Pedigree::Subarg(*i, *j, payload_ty),
                        None => Pedigree::Rabble,
                    }
                }
                _ => Pedigree::Rabble,
            };
            process_pat(penv, &sub_ped, sub_pat, payload_map);
        }
        Pattern::Record(fields) => {
            let record_fields_opt: Option<Vec<(LocatedConstructor, LocatedConstructor)>> =
                match scrutinee_ped {
                    Pedigree::Arg(_, _, t) | Pedigree::Subarg(_, _, t) => {
                        extract_record_fields(&t.node)
                    }
                    _ => None,
                };

            for (field_name, sub_pat, _field_type) in fields {
                let field_ped = match scrutinee_ped {
                    Pedigree::Arg(i, j, _) | Pedigree::Subarg(i, j, _) => {
                        match &record_fields_opt {
                            Some(rf) => {
                                let found = rf.iter().find(|(fname, _)| {
                                    names_eq(&fname.node, &Constructor::Name(field_name.clone()))
                                });
                                match found {
                                    Some((_, fty)) => Pedigree::Subarg(*i, *j, fty.clone()),
                                    None => Pedigree::Rabble,
                                }
                            }
                            None => Pedigree::Rabble,
                        }
                    }
                    _ => Pedigree::Rabble,
                };
                process_pat(penv, &field_ped, sub_pat, payload_map);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Call record
// ---------------------------------------------------------------------------

/// (caller_func_idx, callee_func_idx, arg_pedigrees)
type Call = (usize, usize, Vec<Pedigree>);

// ---------------------------------------------------------------------------
// exp_pedigree — traverse an expression, collecting calls
// ---------------------------------------------------------------------------

fn exp_pedigree(
    e: &LocatedExpression,
    parent: usize,
    penv: &[Pedigree],
    calls: &mut Vec<Call>,
    fenv: &HashMap<usize, usize>,
    payload_map: &HashMap<usize, LocatedConstructor>,
) -> Pedigree {
    match &e.node {
        Expression::Prim(_) => Pedigree::Rabble,

        Expression::Rel(n) => {
            if *n < penv.len() {
                penv[penv.len() - 1 - n].clone()
            } else {
                Pedigree::Rabble
            }
        }

        Expression::Named(n) => match fenv.get(n) {
            Some(&idx) => Pedigree::Func(idx),
            None => Pedigree::Rabble,
        },

        Expression::Ffi(_, _) => Pedigree::Rabble,

        Expression::FfiApp(_, _, args) => {
            for (arg, _) in args {
                exp_pedigree(arg, parent, penv, calls, fenv, payload_map);
            }
            Pedigree::Rabble
        }

        Expression::Constructor(_, _, _, sub_exp) => {
            if let Some(inner) = sub_exp {
                exp_pedigree(inner, parent, penv, calls, fenv, payload_map);
            }
            Pedigree::Rabble
        }

        Expression::App(_, _) | Expression::CApp(_, _) | Expression::KApp(_, _) => {
            apps_pedigree(e, parent, penv, calls, fenv, payload_map)
        }

        Expression::Abs(_, _dom, _, body) => {
            let mut penv2 = penv.to_vec();
            penv2.push(Pedigree::Rabble); // body-level lambda, not a top-level arg
            exp_pedigree(body, parent, &penv2, calls, fenv, payload_map);
            Pedigree::Rabble
        }
        Expression::CAbs(_, _, body) | Expression::KAbs(_, body) => {
            exp_pedigree(body, parent, penv, calls, fenv, payload_map);
            Pedigree::Rabble
        }

        Expression::Record(fields) => {
            for (_, fe, _) in fields {
                exp_pedigree(fe, parent, penv, calls, fenv, payload_map);
            }
            Pedigree::Rabble
        }

        Expression::Field(base, field_name, _meta) => {
            let base_ped = exp_pedigree(base, parent, penv, calls, fenv, payload_map);
            match &base_ped {
                Pedigree::Subarg(i, j, t) => match extract_record_fields(&t.node) {
                    Some(rf) => {
                        let found = rf
                            .iter()
                            .find(|(fname, _)| names_eq(&fname.node, &field_name.node));
                        match found {
                            Some((_, fty)) => Pedigree::Subarg(*i, *j, fty.clone()),
                            None => Pedigree::Rabble,
                        }
                    }
                    None => Pedigree::Rabble,
                },
                _ => Pedigree::Rabble,
            }
        }

        Expression::Concat(e1, _, e2, _) => {
            exp_pedigree(e1, parent, penv, calls, fenv, payload_map);
            exp_pedigree(e2, parent, penv, calls, fenv, payload_map);
            Pedigree::Rabble
        }
        Expression::Cut(inner, _, _) | Expression::CutMulti(inner, _, _) => {
            exp_pedigree(inner, parent, penv, calls, fenv, payload_map);
            Pedigree::Rabble
        }
        Expression::Write(inner) => {
            exp_pedigree(inner, parent, penv, calls, fenv, payload_map);
            Pedigree::Rabble
        }

        Expression::Case(disc, arms, _) => {
            let disc_ped = exp_pedigree(disc, parent, penv, calls, fenv, payload_map);
            for (pat, body) in arms {
                let mut arm_penv = penv.to_vec();
                process_pat(&mut arm_penv, &disc_ped, pat, payload_map);
                exp_pedigree(body, parent, &arm_penv, calls, fenv, payload_map);
            }
            Pedigree::Rabble
        }

        Expression::Let(_, _, e1, e2) => {
            exp_pedigree(e1, parent, penv, calls, fenv, payload_map);
            let mut penv2 = penv.to_vec();
            penv2.push(Pedigree::Rabble);
            exp_pedigree(e2, parent, &penv2, calls, fenv, payload_map);
            Pedigree::Rabble
        }

        Expression::ServerCall(_, args, _, _) | Expression::Closure(_, args) => {
            for arg in args {
                exp_pedigree(arg, parent, penv, calls, fenv, payload_map);
            }
            Pedigree::Rabble
        }
    }
}

// ---------------------------------------------------------------------------
// apps_pedigree — handle application chains
// ---------------------------------------------------------------------------

/// Peel an application chain, collecting the head pedigree and all argument
/// pedigrees.  If the head turns out to be a `Func`, record a call.
fn apps_pedigree(
    e: &LocatedExpression,
    parent: usize,
    penv: &[Pedigree],
    calls: &mut Vec<Call>,
    fenv: &HashMap<usize, usize>,
    payload_map: &HashMap<usize, LocatedConstructor>,
) -> Pedigree {
    /// Returns `(result_pedigree, [head_pedigree, arg1_pedigree, ...])`.
    fn combiner(
        e: &LocatedExpression,
        parent: usize,
        penv: &[Pedigree],
        calls: &mut Vec<Call>,
        fenv: &HashMap<usize, usize>,
        payload_map: &HashMap<usize, LocatedConstructor>,
    ) -> (Pedigree, Vec<Pedigree>) {
        match &e.node {
            Expression::App(e1, e2) => {
                let (p1, mut ps) = combiner(e1, parent, penv, calls, fenv, payload_map);
                let p2 = exp_pedigree(e2, parent, penv, calls, fenv, payload_map);
                let result_ped = match &p1 {
                    Pedigree::Subarg(i, j, t) => match &t.node {
                        Constructor::TFun(_, ran) => Pedigree::Subarg(*i, *j, *ran.clone()),
                        _ => Pedigree::Rabble,
                    },
                    _ => Pedigree::Rabble,
                };
                ps.push(p2);
                (result_ped, ps)
            }
            Expression::CApp(e1, _) => {
                let (p1, ps) = combiner(e1, parent, penv, calls, fenv, payload_map);
                let result_ped = match &p1 {
                    Pedigree::Subarg(i, j, t) => match &t.node {
                        Constructor::TCFun(_, _, body) => Pedigree::Subarg(*i, *j, *body.clone()),
                        _ => Pedigree::Rabble,
                    },
                    _ => Pedigree::Rabble,
                };
                (result_ped, ps)
            }
            Expression::KApp(e1, _) => combiner(e1, parent, penv, calls, fenv, payload_map),
            _ => {
                let p = exp_pedigree(e, parent, penv, calls, fenv, payload_map);
                (p.clone(), vec![p])
            }
        }
    }

    let (_, ps) = combiner(e, parent, penv, calls, fenv, payload_map);

    // If the head element is a Func, this is a call to a recursive function.
    if let Some(Pedigree::Func(callee_idx)) = ps.first() {
        let arg_peds = ps[1..].to_vec();
        calls.push((parent, *callee_idx, arg_peds));
    }

    Pedigree::Rabble
}

// ---------------------------------------------------------------------------
// reachable — cycle-detection for recursive call filtering
// ---------------------------------------------------------------------------

fn reachable(at: usize, goal: usize, calls: &[Call], visited: &mut HashSet<usize>) -> bool {
    if at == goal {
        return true;
    }
    // Collect successors first to avoid borrow issues.
    let successors: Vec<usize> = calls
        .iter()
        .filter_map(|(from, to, _)| if *from == at { Some(*to) } else { None })
        .collect();
    for to in successors {
        if !visited.contains(&to) {
            visited.insert(to);
            if reachable(to, goal, calls, visited) {
                return true;
            }
        }
    }
    false
}

// ---------------------------------------------------------------------------
// search — find a witness argument assignment
// ---------------------------------------------------------------------------

/// Search for an assignment of "witness argument positions" that proves all
/// recursive calls decrease structurally.
///
/// `ns[i]` = number of arguments of function `i`.
/// `choices` = the assignment built so far (one choice per function assigned).
fn search(ns: &[usize], choices: &[usize], calls: &[Call]) -> bool {
    match ns.split_first() {
        None => {
            // All functions assigned; verify every recursive call.
            calls.iter().all(|(_, callee, args)| {
                let rec_arg = choices[*callee];
                if args.len() <= rec_arg {
                    return false;
                }
                match &args[rec_arg] {
                    Pedigree::Subarg(i, j, t) => is_datatype(t) && *j == choices[*i],
                    _ => false,
                }
            })
        }
        Some((n, rest)) => {
            let mut choices_ext = choices.to_vec();
            choices_ext.push(0); // placeholder
            let idx = choices_ext.len() - 1;
            for choice in 0..*n {
                choices_ext[idx] = choice;
                if search(rest, &choices_ext, calls) {
                    return true;
                }
            }
            false
        }
    }
}

// ---------------------------------------------------------------------------
// unravel — peel leading lambdas to identify formal arguments
// ---------------------------------------------------------------------------

fn unravel(
    e: &LocatedExpression,
    func_idx: usize,
    arg_pos: usize,
    penv: &[Pedigree],
    fenv: &HashMap<usize, usize>,
    payload_map: &HashMap<usize, LocatedConstructor>,
) -> (usize, Vec<Call>) {
    match &e.node {
        Expression::Abs(_, dom, _, body) => {
            let arg_ped = Pedigree::Arg(func_idx, arg_pos, dom.clone());
            let mut new_penv = penv.to_vec();
            new_penv.push(arg_ped);
            unravel(body, func_idx, arg_pos + 1, &new_penv, fenv, payload_map)
        }
        Expression::CAbs(_, _, body) | Expression::KAbs(_, body) => {
            unravel(body, func_idx, arg_pos, penv, fenv, payload_map)
        }
        _ => {
            let mut calls = Vec::new();
            exp_pedigree(e, func_idx, penv, &mut calls, fenv, payload_map);
            (arg_pos, calls)
        }
    }
}

// ---------------------------------------------------------------------------
// check_val_rec
// ---------------------------------------------------------------------------

fn check_val_rec(
    vis: &[(String, usize, LocatedConstructor, LocatedExpression, String)],
    decl_span: &crate::error_types::Span,
    payload_map: &HashMap<usize, LocatedConstructor>,
    errors: &mut ErrorReporter,
) {
    // Map from Named id → index in the ValRec group.
    let fenv: HashMap<usize, usize> = vis
        .iter()
        .enumerate()
        .map(|(i, (_, id, _, _, _))| (*id, i))
        .collect();

    // Collect calls from all functions in the group.
    let mut all_calls: Vec<Call> = Vec::new();
    let mut ns: Vec<usize> = Vec::new();

    for (func_idx, (_, _, _, body, _)) in vis.iter().enumerate() {
        let (n_args, func_calls) = unravel(body, func_idx, 0, &[], &fenv, payload_map);
        ns.push(n_args);
        all_calls.extend(func_calls);
    }

    // Filter to only recursive calls (those in a cycle in the call graph).
    let recursive_calls: Vec<Call> = all_calls
        .iter()
        .filter(|(from, to, _)| {
            let mut visited = HashSet::new();
            visited.insert(*from);
            reachable(*to, *from, &all_calls, &mut visited)
        })
        .cloned()
        .collect();

    if recursive_calls.is_empty() {
        return;
    }

    if !search(&ns, &[], &recursive_calls) {
        errors.report_at(
            decl_span.clone(),
            "Can't prove termination of recursive function(s)".to_string(),
        );
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Run the termination checker over a Core file.
pub fn check(file: &crate::core::File, errors: &mut ErrorReporter) {
    let payload_map = build_con_payload_map(file);
    for ld in file {
        if let Declaration::ValRec(vis) = &ld.node {
            check_val_rec(vis, &ld.span, &payload_map, errors);
        }
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

    fn dummy_ty() -> LocatedConstructor {
        dummy(Constructor::Named(999))
    }

    #[test]
    fn test_empty() {
        let mut errors = ErrorReporter::new();
        let file: File = vec![];
        check(&file, &mut errors);
        assert!(!errors.has_errors());
    }

    #[test]
    fn test_non_recursive_val_rec() {
        let file: File = vec![dummy(Declaration::ValRec(vec![(
            "f".into(),
            1,
            dummy_ty(),
            dummy(Expression::Prim(crate::primitives::Prim::Int(0))),
            "".into(),
        )]))];
        let mut errors = ErrorReporter::new();
        check(&file, &mut errors);
        assert!(!errors.has_errors());
    }

    #[test]
    fn test_is_datatype_named() {
        assert!(is_datatype(&dummy(Constructor::Named(0))));
    }

    #[test]
    fn test_is_datatype_tfun_false() {
        let c = dummy(Constructor::TFun(
            Box::new(dummy(Constructor::Named(0))),
            Box::new(dummy(Constructor::Named(1))),
        ));
        assert!(!is_datatype(&c));
    }

    #[test]
    fn test_names_eq() {
        assert!(names_eq(
            &Constructor::Name("Foo".into()),
            &Constructor::Name("Foo".into())
        ));
        assert!(!names_eq(
            &Constructor::Name("Foo".into()),
            &Constructor::Name("Bar".into())
        ));
    }
}
