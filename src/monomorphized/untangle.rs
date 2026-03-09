//! Untangle pass for the Mono IR.
//!
//! Decomposes over-grouped `DValRec` blocks into their minimal strongly-connected
//! components (SCCs), converting non-recursive singletons back to `DVal`.
//!
//! Mirrors `untangle.sml` (which operates on the Mono AST).

use std::collections::{BTreeMap, BTreeSet};

use crate::error_types::Located;
use crate::monomorphized::*;

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Decompose over-grouped `DValRec` blocks into minimal SCCs.
///
/// Mirrors `Untangle.untangle`.
pub fn untangle(file: File) -> File {
    let (decls, exports) = file;
    let result = decls
        .into_iter()
        .flat_map(|d| match d.node {
            Decl::ValRec(vis) => split_val_rec(vis, d.span),
            _ => vec![d],
        })
        .collect();
    (result, exports)
}

// ---------------------------------------------------------------------------
// Split a single DValRec into SCCs
// ---------------------------------------------------------------------------

fn split_val_rec(
    vis: Vec<(String, usize, LocTyp, LocExp, String)>,
    span: crate::error_types::Span,
) -> Vec<LocDecl> {
    let group_ids: BTreeSet<usize> = vis.iter().map(|(_, n, _, _, _)| *n).collect();

    // For each member, compute the set of group members its body references.
    let dep_map: BTreeMap<usize, BTreeSet<usize>> = vis
        .iter()
        .map(|(_, n, _, e, _)| (*n, find_deps(e, &group_ids)))
        .collect();

    let sccs = tarjan_sccs_topological(&group_ids, &dep_map);

    // Index by id for O(1) lookup.
    let by_id: BTreeMap<usize, (String, usize, LocTyp, LocExp, String)> = vis
        .into_iter()
        .map(|(x, n, t, e, s)| (n, (x, n, t, e, s)))
        .collect();

    sccs.into_iter()
        .map(|scc| {
            if let Some(lone) = non_recursive_singleton(&scc, &dep_map) {
                let (x, n, t, e, s) = by_id[&lone].clone();
                Located::new(Decl::Val(x, n, t, e, s), span.clone())
            } else {
                // Preserve original declaration order within the SCC.
                let members: Vec<_> = by_id
                    .values()
                    .filter(|(_, n, _, _, _)| scc.contains(n))
                    .cloned()
                    .collect();
                Located::new(Decl::ValRec(members), span.clone())
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Dependency collection — only ENamed references within the group
// ---------------------------------------------------------------------------

fn find_deps(e: &LocExp, group: &BTreeSet<usize>) -> BTreeSet<usize> {
    let mut deps = BTreeSet::new();
    collect_deps(e, group, &mut deps);
    deps
}

fn collect_deps(e: &LocExp, group: &BTreeSet<usize>, deps: &mut BTreeSet<usize>) {
    if let Exp::Named(n) = &e.node {
        if group.contains(n) {
            deps.insert(*n);
        }
    }
    match &e.node {
        Exp::Prim(_) | Exp::Rel(_) | Exp::Named(_) | Exp::Ffi(_, _) => {}

        Exp::Con(_, _, arg) => {
            if let Some(inner) = arg {
                collect_deps(inner, group, deps);
            }
        }
        Exp::None(_) => {}
        Exp::Some(_, inner) => collect_deps(inner, group, deps),

        Exp::FfiApp(_, _, args) => args.iter().for_each(|(e, _)| collect_deps(e, group, deps)),

        Exp::App(e1, e2)
        | Exp::Binop(_, _, e1, e2)
        | Exp::Strcat(e1, e2)
        | Exp::Seq(e1, e2)
        | Exp::SignalBind(e1, e2)
        | Exp::Setval(e1, e2) => {
            collect_deps(e1, group, deps);
            collect_deps(e2, group, deps);
        }

        Exp::Abs(_, _, _, body)
        | Exp::Unop(_, body)
        | Exp::Field(body, _)
        | Exp::Write(body)
        | Exp::SignalReturn(body)
        | Exp::SignalSource(body)
        | Exp::Sleep(body)
        | Exp::Spawn(body)
        | Exp::Nextval(body)
        | Exp::Dml(body, _) => collect_deps(body, group, deps),

        Exp::Record(xets) => xets
            .iter()
            .for_each(|(_, e, _)| collect_deps(e, group, deps)),

        Exp::Case(disc, arms, _) => {
            collect_deps(disc, group, deps);
            arms.iter().for_each(|(_, e)| collect_deps(e, group, deps));
        }

        Exp::Error(e1, _)
        | Exp::Redirect(e1, _)
        | Exp::Uurlify(e1, _, _)
        | Exp::ServerCall(e1, _, _, _)
        | Exp::Recv(e1, _) => collect_deps(e1, group, deps),

        Exp::ReturnBlob {
            blob, mime_type, ..
        } => {
            if let Some(b) = blob {
                collect_deps(b, group, deps);
            }
            collect_deps(mime_type, group, deps);
        }

        Exp::Let(_, _, e1, e2) => {
            collect_deps(e1, group, deps);
            collect_deps(e2, group, deps);
        }

        Exp::Closure(_, envs) => envs.iter().for_each(|e| collect_deps(e, group, deps)),

        Exp::Query(qm) => {
            collect_deps(&qm.query, group, deps);
            collect_deps(&qm.body, group, deps);
            collect_deps(&qm.initial, group, deps);
        }

        Exp::JavaScript(_, inner) => collect_deps(inner, group, deps),
    }
}

// ---------------------------------------------------------------------------
// Non-recursive singleton detection
// ---------------------------------------------------------------------------

fn non_recursive_singleton(
    scc: &BTreeSet<usize>,
    dep_map: &BTreeMap<usize, BTreeSet<usize>>,
) -> Option<usize> {
    if scc.len() != 1 {
        return None;
    }
    let n = *scc.iter().next().unwrap();
    let empty = BTreeSet::new();
    let deps = dep_map.get(&n).unwrap_or(&empty);
    if deps.contains(&n) {
        None
    } else {
        Some(n)
    }
}

// ---------------------------------------------------------------------------
// Tarjan's SCC — iterative to avoid stack overflow
// ---------------------------------------------------------------------------

fn tarjan_sccs_topological(
    nodes: &BTreeSet<usize>,
    successors: &BTreeMap<usize, BTreeSet<usize>>,
) -> Vec<BTreeSet<usize>> {
    let mut disc: BTreeMap<usize, usize> = BTreeMap::new();
    let mut lowlink: BTreeMap<usize, usize> = BTreeMap::new();
    let mut on_stack: BTreeSet<usize> = BTreeSet::new();
    let mut stack: Vec<usize> = Vec::new();
    let mut counter: usize = 0;
    let mut result: Vec<BTreeSet<usize>> = Vec::new();
    let empty = BTreeSet::new();

    for &start in nodes {
        if disc.contains_key(&start) {
            continue;
        }
        disc.insert(start, counter);
        lowlink.insert(start, counter);
        counter += 1;
        on_stack.insert(start);
        stack.push(start);

        let start_succs: Vec<usize> = successors
            .get(&start)
            .unwrap_or(&empty)
            .iter()
            .copied()
            .collect();
        let mut dfs: Vec<(usize, Vec<usize>)> = vec![(start, start_succs)];

        'outer: while let Some((cur, ref mut rem)) = dfs.last_mut() {
            let cur = *cur;
            while let Some(w) = rem.pop() {
                if !disc.contains_key(&w) {
                    let w_succs: Vec<usize> = successors
                        .get(&w)
                        .unwrap_or(&empty)
                        .iter()
                        .copied()
                        .collect();
                    disc.insert(w, counter);
                    lowlink.insert(w, counter);
                    counter += 1;
                    on_stack.insert(w);
                    stack.push(w);
                    dfs.push((w, w_succs));
                    continue 'outer;
                } else if on_stack.contains(&w) {
                    let wi = disc[&w];
                    let ll = lowlink[&cur];
                    lowlink.insert(cur, ll.min(wi));
                }
            }
            if lowlink[&cur] == disc[&cur] {
                let mut scc = BTreeSet::new();
                loop {
                    let v = stack.pop().expect("Tarjan stack underflow");
                    on_stack.remove(&v);
                    scc.insert(v);
                    if v == cur {
                        break;
                    }
                }
                result.push(scc);
            }
            dfs.pop();
            if let Some((par, _)) = dfs.last() {
                let par = *par;
                let pll = lowlink[&par];
                let cll = lowlink[&cur];
                lowlink.insert(par, pll.min(cll));
            }
        }
    }

    result.reverse();
    result
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

    fn dummy_typ() -> LocTyp {
        dummy(Typ::Ffi("Basis".into(), "int".into()))
    }

    fn dummy_exp() -> LocExp {
        dummy(Exp::Prim(crate::primitives::Prim::Int(0)))
    }

    #[test]
    fn untangle_empty_file() {
        let (decls, exports) = untangle((vec![], vec![]));
        assert!(decls.is_empty());
        assert!(exports.is_empty());
    }

    /// A DValRec with a single non-recursive member becomes a DVal.
    #[test]
    fn untangle_singleton_non_rec_becomes_val() {
        let vis = vec![("f".into(), 1usize, dummy_typ(), dummy_exp(), "f".into())];
        let decl = dummy(Decl::ValRec(vis));
        let (out, _) = untangle((vec![decl], vec![]));
        assert_eq!(out.len(), 1);
        assert!(matches!(&out[0].node, Decl::Val(_, 1, _, _, _)));
    }

    /// A self-recursive singleton remains a DValRec.
    #[test]
    fn untangle_self_recursive_stays_valrec() {
        // Body references id 1 (itself).
        let body = dummy(Exp::Named(1));
        let vis = vec![("f".into(), 1usize, dummy_typ(), body, "f".into())];
        let decl = dummy(Decl::ValRec(vis));
        let (out, _) = untangle((vec![decl], vec![]));
        assert_eq!(out.len(), 1);
        assert!(matches!(&out[0].node, Decl::ValRec(_)));
    }
}
