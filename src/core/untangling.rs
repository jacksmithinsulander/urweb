//! Split over-grouped `ValRec` blocks into their minimal strongly-connected components.
//!
//! When the elaborator groups mutually recursive bindings it may over-approximate
//! the recursion: a `DValRec` block might contain functions that are not actually
//! mutually recursive.  The untangle pass decomposes each `DValRec` block into
//! its strongly-connected components (SCCs), converts non-recursive singletons
//! back into plain `DVal` declarations, and emits everything in topological order
//! (dependencies before dependents).
//!
//! # Algorithm
//!
//! For each `DValRec` block:
//!
//! 1. Compute the *within-group dependency graph*: for each member id, which other
//!    member ids does its body reference (via [`Expression::Named`], [`Expression::Closure`], or
//!    [`Expression::ServerCall`])?
//!
//! 2. Run Tarjan's SCC algorithm on that graph.  The result is a list of SCCs in
//!    topological order (each SCC's dependencies appear earlier in the list).
//!
//! 3. For each SCC:
//!    - **Singleton with no self-loop** → emit a single [`Declaration::Val`] (non-recursive).
//!    - **Otherwise** → emit a [`Declaration::ValRec`] containing only the SCC's members.
//!
//! All other declarations are passed through unchanged.
//!
//! Mirrors `core_untangle.sml`.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::{Declaration, Expression, File, LocatedDeclaration, LocatedExpression};
use crate::error_types::Located;

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Decompose over-grouped `ValRec` blocks into their minimal SCCs.
///
/// Each [`Declaration::ValRec`] in `file` is split into its strongly-connected
/// components (in topological order).  Non-recursive singletons become
/// [`Declaration::Val`].  All other declarations are passed through unchanged.
///
/// Mirrors `CoreUntangle.untangle`.
pub fn untangle(file: File) -> File {
    file.into_iter()
        .flat_map(|located_decl| match located_decl.node {
            Declaration::ValRec(bindings) => split_val_rec_into_sccs(bindings, located_decl.span),
            _ => vec![located_decl],
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Split a single ValRec block
// ---------------------------------------------------------------------------

/// Split one `ValRec` binding group into an ordered sequence of minimal SCCs.
///
/// Returns a `Vec` because each SCC may expand into a different [`Decl`] variant
/// and the caller needs to flatten the results into the output file.
fn split_val_rec_into_sccs(
    bindings: Vec<(
        String,
        usize,
        crate::core::LocatedConstructor,
        LocatedExpression,
        String,
    )>,
    span: crate::error_types::Span,
) -> Vec<LocatedDeclaration> {
    // Collect all member ids into the "this group" set.
    let group_ids: BTreeSet<usize> = bindings
        .iter()
        .map(|(_name, id, _ty, _body, _comment)| *id)
        .collect();

    // Build the within-group dependency map: for each member, which other
    // group members does its body reference?
    let dependency_map: BTreeMap<usize, BTreeSet<usize>> = bindings
        .iter()
        .map(|(_name, id, _ty, body, _comment)| {
            (*id, find_group_deps_in_expression(body, &group_ids))
        })
        .collect();

    // Compute SCCs in topological order (dependencies first).
    let sccs = tarjan_sccs_topological(&group_ids, &dependency_map);

    // Build an index from id to binding, preserving the original binding data.
    let binding_by_id: BTreeMap<
        usize,
        (
            String,
            usize,
            crate::core::LocatedConstructor,
            LocatedExpression,
            String,
        ),
    > = bindings
        .into_iter()
        .map(|(name, id, ty, body, comment)| (id, (name, id, ty, body, comment)))
        .collect();

    // Convert each SCC into a Declaration::Val or Declaration::ValRec.
    sccs.into_iter()
        .map(|scc| {
            // Try to demote a non-recursive singleton to DVal.
            if let Some(single_id) = non_recursive_singleton(&scc, &dependency_map) {
                let (name, id, ty, body, comment) = binding_by_id[&single_id].clone();
                Located::new(Declaration::Val(name, id, ty, body, comment), span.clone())
            } else {
                // Collect all members of this SCC in the original order.
                let scc_members: Vec<_> = binding_by_id
                    .values()
                    .filter(|(_name, id, _ty, _body, _comment)| scc.contains(id))
                    .cloned()
                    .collect();
                Located::new(Declaration::ValRec(scc_members), span.clone())
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Within-group dependency collection
// ---------------------------------------------------------------------------

/// Collect the set of group member ids referenced by `expression`.
///
/// Only [`Expression::Named`], [`Expression::Closure`], and [`Expression::ServerCall`] carry
/// global name references that could point into the group; all other
/// expression forms are transparent to this analysis.
///
/// Mirrors the `expUsed thisGroup` function in `core_untangle.sml`.
fn find_group_deps_in_expression(
    expression: &LocatedExpression,
    group_ids: &BTreeSet<usize>,
) -> BTreeSet<usize> {
    use crate::core::utilities::expression;
    expression::fold(
        expression,
        BTreeSet::new(),
        // Kinds have no named-expression references.
        &|_kind, state| state,
        // Constructors have no named-expression references.
        &|_constructor, state| state,
        // Expressions: check Named, Closure, and ServerCall ids.
        &|exp, mut state| {
            let referenced_id = match &exp.node {
                Expression::Named(id) => Some(*id),
                Expression::Closure(id, _captured) => Some(*id),
                Expression::ServerCall(id, _args, _result_ty, _mode) => Some(*id),
                _ => None,
            };
            if let Some(id) = referenced_id {
                if group_ids.contains(&id) {
                    state.insert(id);
                }
            }
            state
        },
    )
}

// ---------------------------------------------------------------------------
// Tarjan's SCC — iterative to avoid stack overflow on large groups
// ---------------------------------------------------------------------------

/// Run Tarjan's SCC algorithm and return the SCCs in topological order
/// (dependencies before dependents).
///
/// `nodes` is the set of all vertices; `successors` maps each vertex to
/// the set of vertices it has an edge to (i.e., the vertices it depends on).
/// The returned SCCs are in forward topological order: if SCC A contains a
/// function that calls functions in SCC B, B appears before A.
///
/// Mirrors the SCC computation in `core_untangle.sml` (Tarjan's algorithm,
/// then `List.rev` to get topological order).
fn tarjan_sccs_topological(
    nodes: &BTreeSet<usize>,
    successors: &BTreeMap<usize, BTreeSet<usize>>,
) -> Vec<BTreeSet<usize>> {
    // Per-node Tarjan state.
    let mut discovery_index: BTreeMap<usize, usize> = BTreeMap::new();
    let mut lowlink: BTreeMap<usize, usize> = BTreeMap::new();
    let mut on_stack: BTreeSet<usize> = BTreeSet::new();
    let mut tarjan_stack: Vec<usize> = Vec::new();
    let mut index_counter: usize = 0;
    // SCCs as completed (reverse topological order from Tarjan).
    let mut sccs_reverse_topo: Vec<BTreeSet<usize>> = Vec::new();
    let vertex_count = nodes.len();
    let edge_count: usize = successors.values().map(|s| s.len()).sum();
    let outer_step_budget = vertex_count
        .saturating_add(edge_count)
        .max(1)
        .saturating_mul(64)
        .saturating_add(1024);

    // We use an explicit worklist to avoid recursion-depth limits.
    // The worklist holds (node, iterator_position) pairs where
    // iterator_position tracks which successor we're currently exploring.
    let sorted_nodes: Vec<usize> = nodes.iter().copied().collect();

    for &start_node in &sorted_nodes {
        if discovery_index.contains_key(&start_node) {
            continue; // already visited
        }
        // Iterative DFS using an explicit stack of (node, successors_remaining).
        // Each frame is (node_id, list_of_remaining_successors).
        let empty_set = BTreeSet::new();
        let start_succs: Vec<usize> = successors
            .get(&start_node)
            .unwrap_or(&empty_set)
            .iter()
            .copied()
            .collect();

        // DFS frames: (node, remaining_successors_to_visit)
        let mut dfs_stack: Vec<(usize, Vec<usize>)> = vec![(start_node, start_succs)];

        // Initialize the start node.
        discovery_index.insert(start_node, index_counter);
        lowlink.insert(start_node, index_counter);
        index_counter += 1;
        on_stack.insert(start_node);
        tarjan_stack.push(start_node);

        let successor_pop_cap = vertex_count.saturating_add(1);
        for _outer_step in 0..outer_step_budget {
            // Defer `dfs_stack.push` until after any `last_mut` borrow ends (tree edge).
            let mut next_dfs_frame: Option<(usize, Vec<usize>)> = None;
            let current_node = {
                let Some((current_node, ref mut remaining_succs)) = dfs_stack.last_mut() else {
                    break;
                };
                let current_node = *current_node;

                // Process the next unvisited or on-stack successor (bounded pops per frame).
                for _succ_step in 0..successor_pop_cap {
                    let Some(successor) = remaining_succs.pop() else {
                        break;
                    };
                    if let std::collections::btree_map::Entry::Vacant(e) =
                        discovery_index.entry(successor)
                    {
                        // Tree edge: recurse into successor (push after this block).
                        let successor_succs: Vec<usize> = successors
                            .get(&successor)
                            .unwrap_or(&empty_set)
                            .iter()
                            .copied()
                            .collect();
                        e.insert(index_counter);
                        lowlink.insert(successor, index_counter);
                        index_counter += 1;
                        on_stack.insert(successor);
                        tarjan_stack.push(successor);
                        next_dfs_frame = Some((successor, successor_succs));
                        break;
                    } else if on_stack.contains(&successor) {
                        // Back edge: update lowlink.
                        let successor_index = discovery_index[&successor];
                        let current_ll = lowlink[&current_node];
                        lowlink.insert(current_node, current_ll.min(successor_index));
                    }
                    // Cross/forward edges: ignore (already finished, not on stack).
                }
                current_node
            };
            if let Some(frame) = next_dfs_frame {
                dfs_stack.push(frame);
                continue;
            }

            // All successors processed: check if current_node is an SCC root.
            let current_index = discovery_index[&current_node];
            if lowlink[&current_node] == current_index {
                // Pop an SCC off the tarjan_stack.
                let mut scc = BTreeSet::new();
                let mut hit_root = false;
                let stack_pop_cap = vertex_count.saturating_add(1);
                for _stack_pop in 0..stack_pop_cap {
                    let Some(popped) = tarjan_stack.pop() else {
                        break;
                    };
                    on_stack.remove(&popped);
                    scc.insert(popped);
                    if popped == current_node {
                        hit_root = true;
                        break;
                    }
                }
                if !hit_root {
                    scc.insert(current_node);
                }
                sccs_reverse_topo.push(scc);
            }

            // Pop this frame and update parent's lowlink.
            dfs_stack.pop();
            if let Some((parent_node, _)) = dfs_stack.last() {
                let parent_node = *parent_node;
                let parent_ll = lowlink[&parent_node];
                let current_ll = lowlink[&current_node];
                lowlink.insert(parent_node, parent_ll.min(current_ll));
            }
        }
    }

    // Tarjan produces SCCs in reverse topological order; reverse to get
    // dependencies first (matching `List.rev (!sccsAcc)` in the SML).
    sccs_reverse_topo.reverse();
    sccs_reverse_topo
}

// ---------------------------------------------------------------------------
// Non-recursive singleton detection
// ---------------------------------------------------------------------------

/// If `scc` is a singleton `{id}` and `id` has no self-reference in the
/// dependency map, return `Some(id)`.  Otherwise return `None`.
///
/// A self-reference means the function directly or indirectly calls itself
/// within the same binding group — which requires the recursive `DValRec`
/// form to remain.
///
/// Mirrors the `isNonrec` function in `core_untangle.sml`.
fn non_recursive_singleton(
    scc: &BTreeSet<usize>,
    dependency_map: &BTreeMap<usize, BTreeSet<usize>>,
) -> Option<usize> {
    if scc.len() != 1 {
        return None;
    }
    let single_id = *scc.iter().next()?;
    let empty_set = BTreeSet::new();
    let self_deps = dependency_map.get(&single_id).unwrap_or(&empty_set);
    if self_deps.contains(&single_id) {
        None // self-recursive → must stay as DValRec
    } else {
        Some(single_id) // non-recursive singleton → can be DVal
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{
        Constructor, Declaration, Expression, Kind, LocatedConstructor, LocatedExpression,
    };
    use crate::error_types::{Located, Span};
    use crate::primitives::{Prim, StringMode};

    fn dummy_span() -> Span {
        Span::dummy()
    }

    fn unit_con() -> LocatedConstructor {
        Located::new(Constructor::Unit, dummy_span())
    }

    fn prim_exp() -> LocatedExpression {
        Located::new(
            Expression::Prim(Prim::String(StringMode::Normal, String::new())),
            dummy_span(),
        )
    }

    fn named_exp(id: usize) -> LocatedExpression {
        Located::new(Expression::Named(id), dummy_span())
    }

    fn closure_exp(id: usize) -> LocatedExpression {
        Located::new(Expression::Closure(id, vec![]), dummy_span())
    }

    fn simple_val(id: usize, body: LocatedExpression) -> LocatedDeclaration {
        Located::new(
            Declaration::Val(format!("f{id}"), id, unit_con(), body, String::new()),
            dummy_span(),
        )
    }

    fn val_rec(members: Vec<(usize, LocatedExpression)>) -> LocatedDeclaration {
        let bindings = members
            .into_iter()
            .map(|(id, body)| (format!("f{id}"), id, unit_con(), body, String::new()))
            .collect();
        Located::new(Declaration::ValRec(bindings), dummy_span())
    }

    // -----------------------------------------------------------------------
    // Non-recursive singleton → DVal
    // -----------------------------------------------------------------------

    #[test]
    fn single_non_recursive_binding_becomes_val() {
        // Catches mutant: non-recursive singletons remain as DValRec.
        let file = vec![val_rec(vec![(1, prim_exp())])];
        let result = untangle(file);
        assert_eq!(result.len(), 1);
        assert!(
            matches!(&result[0].node, Declaration::Val(_, 1, _, _, _)),
            "non-recursive singleton must be demoted to DVal"
        );
    }

    #[test]
    fn self_recursive_singleton_stays_val_rec() {
        // Catches mutant: self-recursive functions are demoted to DVal.
        // f1 calls f1 → must stay ValRec.
        let file = vec![val_rec(vec![(1, named_exp(1))])];
        let result = untangle(file);
        assert_eq!(result.len(), 1);
        assert!(
            matches!(&result[0].node, Declaration::ValRec(_)),
            "self-recursive function must stay as DValRec"
        );
    }

    // -----------------------------------------------------------------------
    // Two independent functions → two DVal nodes
    // -----------------------------------------------------------------------

    #[test]
    fn two_independent_functions_become_two_vals() {
        // Catches mutant: independent functions stay as a single DValRec.
        let file = vec![val_rec(vec![(1, prim_exp()), (2, prim_exp())])];
        let result = untangle(file);
        let val_count = result
            .iter()
            .filter(|d| matches!(&d.node, Declaration::Val(_, _, _, _, _)))
            .count();
        assert_eq!(val_count, 2, "both independent functions must become DVal");
    }

    // -----------------------------------------------------------------------
    // Dependency detection — both directions become separate DVal nodes
    // -----------------------------------------------------------------------

    #[test]
    fn one_way_dependency_splits_into_two_vals() {
        // Catches mutant: a one-way dep within the group creates a cycle (both
        // treated as DValRec) or fails to split them at all.
        // f2 depends on f1 → they are in separate SCCs → both become DVal.
        // (Tarjan + reverse gives "dependents first" ordering, so f2 may
        // appear before f1; we only assert both become DVal.)
        let file = vec![val_rec(vec![(1, prim_exp()), (2, named_exp(1))])];
        let result = untangle(file);
        assert_eq!(result.len(), 2, "two SCCs expected — one per function");
        let both_are_val = result
            .iter()
            .all(|d| matches!(&d.node, Declaration::Val(_, _, _, _, _)));
        assert!(both_are_val, "one-way dep: both functions must become DVal");
    }

    // -----------------------------------------------------------------------
    // True mutual recursion stays together
    // -----------------------------------------------------------------------

    #[test]
    fn mutual_recursion_stays_as_val_rec() {
        // Catches mutant: mutually recursive functions are split into DVal.
        // f1 calls f2, f2 calls f1 → one DValRec.
        let file = vec![val_rec(vec![(1, named_exp(2)), (2, named_exp(1))])];
        let result = untangle(file);
        assert_eq!(result.len(), 1, "one SCC expected for mutual recursion");
        assert!(
            matches!(&result[0].node, Declaration::ValRec(_)),
            "mutually recursive pair must remain as DValRec"
        );
    }

    // -----------------------------------------------------------------------
    // Mixed: independent + mutually recursive
    // -----------------------------------------------------------------------

    #[test]
    fn mixed_group_split_correctly() {
        // Catches mutant: the whole mixed group stays as one DValRec.
        // f1 is independent; f2 and f3 are mutually recursive.
        // Expected: DVal(f1), DValRec([f2, f3]).
        let file = vec![val_rec(vec![
            (1, prim_exp()),   // independent
            (2, named_exp(3)), // f2 calls f3
            (3, named_exp(2)), // f3 calls f2
        ])];
        let result = untangle(file);
        assert_eq!(result.len(), 2, "expected two declaration nodes");
        let val_count = result
            .iter()
            .filter(|d| matches!(&d.node, Declaration::Val(_, _, _, _, _)))
            .count();
        let val_rec_count = result
            .iter()
            .filter(|d| matches!(&d.node, Declaration::ValRec(_)))
            .count();
        assert_eq!(val_count, 1, "one independent function must become DVal");
        assert_eq!(val_rec_count, 1, "mutual pair must stay as DValRec");
    }

    // -----------------------------------------------------------------------
    // Closure references count as deps
    // -----------------------------------------------------------------------

    #[test]
    fn closure_reference_treated_as_dependency() {
        // Catches mutant: Expression::Closure id is not collected as a group dep,
        // which would cause both to be incorrectly treated as mutually recursive
        // (staying as a DValRec) instead of independent (becoming two DVal).
        // f2 is a closure wrapping f1; the Closure reference creates a one-way
        // dep edge f2→f1, so they fall into separate SCCs → both become DVal.
        let file = vec![val_rec(vec![(1, prim_exp()), (2, closure_exp(1))])];
        let result = untangle(file);
        let both_are_val = result
            .iter()
            .all(|d| matches!(&d.node, Declaration::Val(_, _, _, _, _)));
        assert!(
            result.len() == 2 && both_are_val,
            "Closure dep must create a one-way edge → two separate DVal nodes"
        );
    }

    // -----------------------------------------------------------------------
    // ServerCall references count as deps
    // -----------------------------------------------------------------------

    #[test]
    fn server_call_reference_treated_as_dependency() {
        // Catches mutant: Expression::ServerCall id is not collected as a group dep,
        // which would leave both in the same SCC (as DValRec) instead of
        // splitting them into two DVal nodes (one-way dep → separate SCCs).
        let server_call_exp = Located::new(
            Expression::ServerCall(1, vec![], unit_con(), crate::settings::FailureMode::Error),
            dummy_span(),
        );
        let file = vec![val_rec(vec![(1, prim_exp()), (2, server_call_exp)])];
        let result = untangle(file);
        let both_are_val = result
            .iter()
            .all(|d| matches!(&d.node, Declaration::Val(_, _, _, _, _)));
        assert!(
            result.len() == 2 && both_are_val,
            "ServerCall dep must create a one-way edge → two separate DVal nodes"
        );
    }

    // -----------------------------------------------------------------------
    // Non-ValRec declarations pass through unchanged
    // -----------------------------------------------------------------------

    #[test]
    fn non_val_rec_declarations_pass_through() {
        // Catches mutant: untangle strips or transforms non-ValRec decls.
        let file = vec![
            simple_val(10, prim_exp()),
            Located::new(
                Declaration::Constructor(
                    "T".into(),
                    20,
                    Located::new(Kind::Type, dummy_span()),
                    unit_con(),
                ),
                dummy_span(),
            ),
        ];
        let result = untangle(file);
        assert_eq!(
            result.len(),
            2,
            "non-ValRec decls must be preserved unchanged"
        );
        assert!(matches!(&result[0].node, Declaration::Val(_, 10, _, _, _)));
        assert!(matches!(
            &result[1].node,
            Declaration::Constructor(_, 20, _, _)
        ));
    }

    // -----------------------------------------------------------------------
    // Empty ValRec
    // -----------------------------------------------------------------------

    #[test]
    fn empty_val_rec_produces_no_output() {
        // Catches mutant: empty ValRec inserts a phantom DVal.
        let file = vec![Located::new(Declaration::ValRec(vec![]), dummy_span())];
        let result = untangle(file);
        assert!(
            result.is_empty(),
            "empty DValRec must produce zero declarations"
        );
    }

    // -----------------------------------------------------------------------
    // Cycle safety: three-way mutual recursion
    // -----------------------------------------------------------------------

    #[test]
    fn three_way_mutual_recursion_stays_as_one_val_rec() {
        // Catches mutant: Tarjan splits a three-cycle into multiple SCCs.
        // f1 → f2 → f3 → f1 (three-cycle).
        let file = vec![val_rec(vec![
            (1, named_exp(2)),
            (2, named_exp(3)),
            (3, named_exp(1)),
        ])];
        let result = untangle(file);
        assert_eq!(result.len(), 1, "three-cycle must be one SCC");
        assert!(
            matches!(&result[0].node, Declaration::ValRec(bindings) if bindings.len() == 3),
            "the DValRec must contain all three members"
        );
    }

    // -----------------------------------------------------------------------
    // External references (outside group) are ignored
    // -----------------------------------------------------------------------

    #[test]
    fn external_named_references_do_not_create_deps() {
        // Catches mutant: Named refs outside the group create spurious deps.
        // f1 references id=99 (outside group); f2 is independent.
        let file = vec![val_rec(vec![(1, named_exp(99)), (2, prim_exp())])];
        let result = untangle(file);
        // Both should become independent DVal nodes.
        let val_count = result
            .iter()
            .filter(|d| matches!(&d.node, Declaration::Val(_, _, _, _, _)))
            .count();
        assert_eq!(
            val_count, 2,
            "external refs must not create within-group edges"
        );
    }

    // -----------------------------------------------------------------------
    // SCC helper unit tests
    // -----------------------------------------------------------------------

    #[test]
    fn tarjan_empty_graph_returns_empty() {
        // Catches mutant: Tarjan returns phantom SCCs for empty input.
        let nodes = BTreeSet::new();
        let deps = BTreeMap::new();
        let sccs = tarjan_sccs_topological(&nodes, &deps);
        assert!(sccs.is_empty());
    }

    #[test]
    fn tarjan_single_node_no_self_loop() {
        // Catches mutant: single node incorrectly shows as having a cycle.
        let nodes: BTreeSet<usize> = [1].into();
        let deps: BTreeMap<usize, BTreeSet<usize>> = [(1, BTreeSet::new())].into();
        let sccs = tarjan_sccs_topological(&nodes, &deps);
        assert_eq!(sccs.len(), 1);
        assert_eq!(sccs[0], [1].into());
    }

    #[test]
    fn tarjan_linear_chain_gives_three_singleton_sccs() {
        // Catches mutant: Tarjan merges all three nodes into one SCC (wrong)
        // or fails to detect that they are each their own SCC (acyclic chain).
        // 1 → 2 → 3 (1 depends on 2 which depends on 3); no cycles.
        // The SML algorithm (Tarjan + List.rev) produces "dependents first":
        // the node with most dependencies (1) comes first in the output.
        let nodes: BTreeSet<usize> = [1, 2, 3].into();
        let deps: BTreeMap<usize, BTreeSet<usize>> =
            [(1, [2].into()), (2, [3].into()), (3, BTreeSet::new())].into();
        let sccs = tarjan_sccs_topological(&nodes, &deps);
        assert_eq!(
            sccs.len(),
            3,
            "acyclic chain → three singleton SCCs, one per node"
        );
        // Every SCC is a singleton.
        for scc in &sccs {
            assert_eq!(
                scc.len(),
                1,
                "each node forms its own SCC in an acyclic chain"
            );
        }
        // Node 1 (most dependent: calls 2, which calls 3) must come first;
        // node 3 (leaf, called by 2) must come last.
        // This "dependents first" ordering mirrors the SML `List.rev !sccsAcc`.
        // Extract the single element from each singleton SCC; panic if any SCC is empty.
        let flat: Vec<usize> = sccs
            .iter()
            .map(|s| match s.iter().next() {
                Some(v) => *v,
                None => panic!("SCC is unexpectedly empty"),
            })
            .collect();
        // Find position of node 1 in the flattened order; panic if absent.
        let pos1 = match flat.iter().position(|&x| x == 1) {
            Some(p) => p,
            None => panic!("node 1 not found in flat SCC order"),
        };
        // Find position of node 3 in the flattened order; panic if absent.
        let pos3 = match flat.iter().position(|&x| x == 3) {
            Some(p) => p,
            None => panic!("node 3 not found in flat SCC order"),
        };
        assert!(
            pos1 < pos3,
            "node 1 (dependent) must precede node 3 (no deps) in dependents-first order: got {flat:?}"
        );
    }

    #[test]
    fn non_recursive_singleton_returns_id() {
        // Catches mutant: singleton without self-loop is not detected.
        let scc: BTreeSet<usize> = [42].into();
        let deps: BTreeMap<usize, BTreeSet<usize>> = [(42, BTreeSet::new())].into();
        assert_eq!(non_recursive_singleton(&scc, &deps), Some(42));
    }

    #[test]
    fn self_recursive_singleton_returns_none() {
        // Catches mutant: self-recursive singleton is demoted to DVal.
        let scc: BTreeSet<usize> = [42].into();
        let deps: BTreeMap<usize, BTreeSet<usize>> = [(42, [42].into())].into();
        assert_eq!(non_recursive_singleton(&scc, &deps), None);
    }

    #[test]
    fn multi_member_scc_returns_none() {
        // Catches mutant: multi-member SCC is incorrectly treated as singleton.
        let scc: BTreeSet<usize> = [1, 2].into();
        let deps: BTreeMap<usize, BTreeSet<usize>> = [(1, [2].into()), (2, [1].into())].into();
        assert_eq!(non_recursive_singleton(&scc, &deps), None);
    }
}
