//! Specialize — monomorphize polymorphic Core datatypes.
//!
//! This pass finds uses of polymorphic datatypes applied to closed (concrete)
//! constructor arguments and generates specialized (monomorphic) copies. It
//! mirrors `specialize.sml`.
//!
//! **Algorithm outline**:
//!
//! 1. Build `fancy_datatypes`: the set of datatype ids that appear at the root
//!    of a `CApp(_, c2)` where `c2` is open (has a free `CRel`). These cannot
//!    be monomorphized.
//! 2. Walk declarations. For each `DDatatype` not in `fancy_datatypes`:
//!    register the datatypes/constructors in state so later references can be
//!    specialized.  Merge any accumulated specialization decls into the output.
//! 3. For all other declarations: run the specialization rewrite (which rewrites
//!    constructor expressions and patterns), then prepend any newly generated
//!    `DDatatype` specialization decls.

use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap, HashSet};

use crate::core::local_reduction::reduce_con;
use crate::core::unpoly::sub_con_in_con;
use crate::core::utilities::constructor as con_util;
use crate::core::utilities::file as file_util;
use crate::core::*;
use crate::error_types::{Located, Span};

// ---------------------------------------------------------------------------
// is_open — any CRel anywhere (not binder-aware, mirrors SML isOpen)
// ---------------------------------------------------------------------------

/// Returns `true` if the constructor contains *any* `Constructor::Rel(_)` node,
/// regardless of depth. This is deliberately not binder-aware — it matches the
/// SML `isOpen` which just tests for any CRel occurrence.
fn is_open(c: &LocatedConstructor) -> bool {
    match &c.node {
        Constructor::Rel(_) => true,
        Constructor::Named(_)
        | Constructor::Ffi(_, _)
        | Constructor::Name(_)
        | Constructor::Unit
        | Constructor::Map(_, _) => false,
        Constructor::TFun(a, b) => is_open(a) || is_open(b),
        Constructor::TCFun(_, _, b) => is_open(b),
        Constructor::TRecord(inner) => is_open(inner),
        Constructor::App(f, a) => is_open(f) || is_open(a),
        Constructor::Abs(_, _, b) => is_open(b),
        Constructor::KAbs(_, b) => is_open(b),
        Constructor::KApp(c, _) => is_open(c),
        Constructor::TKFun(_, b) => is_open(b),
        Constructor::Record(_, pairs) => pairs.iter().any(|(n, v)| is_open(n) || is_open(v)),
        Constructor::Concat(a, b) => is_open(a) || is_open(b),
        Constructor::Tuple(cs) => cs.iter().any(is_open),
        Constructor::Proj(c, _) => is_open(c),
    }
}

// ---------------------------------------------------------------------------
// find_app — unravel CApp spine to find (Named(n), [args...])
// ---------------------------------------------------------------------------

/// Unravels `CApp(CApp(Named(n), a1), a2)` into `Some((n, [a1, a2]))`.
/// Arguments are in left-to-right (outermost application last) order.
fn find_app(
    c: &Constructor,
    args: Vec<LocatedConstructor>,
) -> Option<(usize, Vec<LocatedConstructor>)> {
    match c {
        Constructor::App(c_inner, arg) => {
            // We collect args in reverse here then reverse at the Named base.
            // Actually we push the arg and recurse, so the final vec is
            // outermost-arg-last. The SML does: findApp(c', arg :: args) so
            // the first arg appended to the front is the innermost application.
            // We mirror that by prepending.
            let mut new_args = vec![*arg.clone()];
            new_args.extend(args);
            find_app(&c_inner.node, new_args)
        }
        Constructor::Named(n) => Some((*n, args)),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// ConList — BTreeMap key for specialization memoization
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct ConList(Vec<LocatedConstructor>);

impl PartialEq for ConList {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for ConList {}

impl PartialOrd for ConList {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ConList {
    fn cmp(&self, other: &Self) -> Ordering {
        let len_ord = self.0.len().cmp(&other.0.len());
        if len_ord != Ordering::Equal {
            return len_ord;
        }
        for (a, b) in self.0.iter().zip(other.0.iter()) {
            let ord = con_util::compare(a, b);
            if ord != Ordering::Equal {
                return ord;
            }
        }
        Ordering::Equal
    }
}

// ---------------------------------------------------------------------------
// State structures
// ---------------------------------------------------------------------------

/// A previously-generated specialization of a datatype.
#[derive(Clone)]
struct SpecializedDt {
    /// Id of the specialized (monomorphic) datatype.
    name: usize,
    /// Map from old constructor id → new constructor id in the specialized type.
    constructors: HashMap<usize, usize>,
}

/// Information about a registred polymorphic datatype.
#[derive(Clone)]
struct DatatypeSpec {
    /// Human-readable name of the original datatype.
    name: String,
    /// Number of type parameters.
    params: usize,
    /// Constructors of the original datatype: (name, id, optional arg type).
    constructors: Vec<(String, usize, Option<LocatedConstructor>)>,
    /// Memoized specializations: constructor arg list → specialized datatype.
    specializations: BTreeMap<ConList, SpecializedDt>,
}

/// Pass state threaded through the specialization walk.
struct State {
    /// Counter for fresh globally-unique ids.
    count: usize,
    /// Map from datatype id → its spec (for those already seen in DDatatype).
    datatypes: HashMap<usize, DatatypeSpec>,
    /// Map from constructor id → owning datatype id.
    constructors: HashMap<usize, usize>,
    /// Accumulated specialization declarations not yet emitted.
    /// Each entry is (name, id, params, constrs) for a new DDatatype group.
    new_decls: Vec<(
        String,
        usize,
        Vec<String>,
        Vec<(String, usize, Option<LocatedConstructor>)>,
    )>,
}

// ---------------------------------------------------------------------------
// consider_specialization
// ---------------------------------------------------------------------------

/// Returns `(new_dt_id, cmap, updated_state)` where `cmap` maps each old
/// constructor id to a new constructor id in the monomorphic copy.
///
/// Memoizes: if this exact `args` list has been seen before for datatype `n`,
/// returns the cached result immediately.
fn consider_specialization(
    st: &mut State,
    n: usize,
    args: Vec<LocatedConstructor>,
    dt: DatatypeSpec,
) -> (usize, HashMap<usize, usize>) {
    // Reduce all args first (mirrors `map ReduceLocal.reduceCon args`).
    let args: Vec<LocatedConstructor> = args.into_iter().map(reduce_con).collect();

    let key = ConList(args.clone());

    // Check memoization cache.
    if let Some(existing) = dt.specializations.get(&key) {
        return (existing.name, existing.constructors.clone());
    }

    // Allocate a fresh id for the specialized datatype.
    let n_prime = st.count;

    // nxs = args.len() - 1
    // For i in 0..args.len(): substitute args[i] for Rel(nxs - i) in each
    // constructor type. This maps:
    //   last arg  → Rel(0)
    //   second-to-last → Rel(1)
    //   ...
    //   first arg → Rel(nxs)
    let nxs = args.len().saturating_sub(1);
    let sub = |mut t: LocatedConstructor| -> LocatedConstructor {
        for (i, arg) in args.iter().enumerate() {
            let depth = nxs - i;
            t = sub_con_in_con(depth, arg, t);
        }
        t
    };

    // Build new constructors with substituted types and fresh ids.
    let mut cmap: HashMap<usize, usize> = HashMap::new();
    let mut count = n_prime + 1;
    let new_constrs: Vec<(String, usize, Option<LocatedConstructor>)> = dt
        .constructors
        .iter()
        .map(|(x, old_id, to)| {
            let new_id = count;
            count += 1;
            cmap.insert(*old_id, new_id);
            let new_to = to.as_ref().map(|t| sub(t.clone()));
            (x.clone(), new_id, new_to)
        })
        .collect();

    // Update state: register the specialization in the datatype's memo table
    // and update the count.
    st.count = count;
    {
        let dt_entry = st.datatypes.entry(n).or_insert_with(|| dt.clone());
        dt_entry.specializations.insert(
            key,
            SpecializedDt {
                name: n_prime,
                constructors: cmap.clone(),
            },
        );
    }

    // Recursively specialize the constructor types of the new monomorphic copy.
    let new_constrs: Vec<(String, usize, Option<LocatedConstructor>)> = new_constrs
        .into_iter()
        .map(|(x, id, to)| {
            let new_to = to.map(|t| spec_con(t, st));
            (x, id, new_to)
        })
        .collect();

    // Push new decl into accumulator.
    let specialized_name = format!("{}_s", dt.name);
    st.new_decls
        .push((specialized_name, n_prime, vec![], new_constrs));

    (n_prime, cmap)
}

// ---------------------------------------------------------------------------
// spec_con — rewrite constructors
// ---------------------------------------------------------------------------

/// Rewrites a constructor: if it is a fully-applied use of a known polymorphic
/// datatype with closed concrete arguments, replace it with the id of the
/// corresponding monomorphic specialization.
fn spec_con(c: LocatedConstructor, st: &mut State) -> LocatedConstructor {
    let span = c.span.clone();
    // First recurse into sub-constructors.
    let c = rewrite_con_children(c, st);
    // Then check whether this is an application of a known datatype.
    match find_app(&c.node.clone(), vec![]) {
        Some((n, args)) if !args.is_empty() => {
            match st.datatypes.get(&n).cloned() {
                None => c,
                Some(dt) => {
                    if args.len() != dt.params {
                        return c;
                    }
                    // Only specialize if all args are closed.
                    if args.iter().any(is_open) {
                        return c;
                    }
                    let (n_prime, _cmap) = consider_specialization(st, n, args, dt);
                    Located::new(Constructor::Named(n_prime), span)
                }
            }
        }
        _ => c,
    }
}

/// Recursively applies `spec_con` to all children of a constructor node.
fn rewrite_con_children(c: LocatedConstructor, st: &mut State) -> LocatedConstructor {
    let span = c.span.clone();
    match c.node {
        Constructor::Rel(_)
        | Constructor::Named(_)
        | Constructor::Ffi(_, _)
        | Constructor::Name(_)
        | Constructor::Unit
        | Constructor::Map(_, _) => c,
        Constructor::TFun(a, b) => Located::new(
            Constructor::TFun(Box::new(spec_con(*a, st)), Box::new(spec_con(*b, st))),
            span,
        ),
        Constructor::TCFun(x, k, b) => {
            Located::new(Constructor::TCFun(x, k, Box::new(spec_con(*b, st))), span)
        }
        Constructor::TRecord(inner) => {
            Located::new(Constructor::TRecord(Box::new(spec_con(*inner, st))), span)
        }
        Constructor::App(f, a) => Located::new(
            Constructor::App(Box::new(spec_con(*f, st)), Box::new(spec_con(*a, st))),
            span,
        ),
        Constructor::Abs(x, k, b) => {
            Located::new(Constructor::Abs(x, k, Box::new(spec_con(*b, st))), span)
        }
        Constructor::KAbs(x, b) => {
            Located::new(Constructor::KAbs(x, Box::new(spec_con(*b, st))), span)
        }
        Constructor::KApp(inner, k) => {
            Located::new(Constructor::KApp(Box::new(spec_con(*inner, st)), k), span)
        }
        Constructor::TKFun(x, b) => {
            Located::new(Constructor::TKFun(x, Box::new(spec_con(*b, st))), span)
        }
        Constructor::Record(k, pairs) => {
            let pairs = pairs
                .into_iter()
                .map(|(n, v)| (spec_con(n, st), spec_con(v, st)))
                .collect();
            Located::new(Constructor::Record(k, pairs), span)
        }
        Constructor::Concat(a, b) => Located::new(
            Constructor::Concat(Box::new(spec_con(*a, st)), Box::new(spec_con(*b, st))),
            span,
        ),
        Constructor::Tuple(cs) => Located::new(
            Constructor::Tuple(cs.into_iter().map(|c| spec_con(c, st)).collect()),
            span,
        ),
        Constructor::Proj(c, i) => {
            Located::new(Constructor::Proj(Box::new(spec_con(*c, st)), i), span)
        }
    }
}

// ---------------------------------------------------------------------------
// walk_pat — rewrite patterns
// ---------------------------------------------------------------------------

/// Rewrites patterns: specializes constructor patterns with closed concrete
/// type arguments. Mirrors the SML `pat` function.
fn walk_pat(p: LocatedPattern, st: &mut State) -> LocatedPattern {
    let span = p.span.clone();
    match p.node {
        Pattern::Var(_, _) | Pattern::Prim(_) => p,
        Pattern::Constructor(dk, PatternConstructor::Var(pn), args, po) if !args.is_empty() => {
            // Recurse into sub-pattern first.
            let po = po.map(|inner| Box::new(walk_pat(*inner, st)));
            let p_rebuilt = Located::new(
                Pattern::Constructor(dk, PatternConstructor::Var(pn), args.clone(), po.clone()),
                span.clone(),
            );
            // Only specialize if no arg is open.
            if args.iter().any(is_open) {
                return p_rebuilt;
            }
            // Look up which datatype owns this constructor.
            let dt_id = match st.constructors.get(&pn).copied() {
                None => return p_rebuilt,
                Some(id) => id,
            };
            let dt = match st.datatypes.get(&dt_id).cloned() {
                None => return p_rebuilt,
                Some(dt) => dt,
            };
            let (_n_prime, cmap) = consider_specialization(st, dt_id, args, dt);
            let Some(&new_pn) = cmap.get(&pn) else {
                return p_rebuilt;
            };
            Located::new(
                Pattern::Constructor(dk, PatternConstructor::Var(new_pn), vec![], po),
                span,
            )
        }
        // Non-Var PatternConstructor with a sub-pattern: just recurse into sub-pattern.
        Pattern::Constructor(dk, pc, args, Some(p_inner)) => {
            let p_inner = walk_pat(*p_inner, st);
            Located::new(
                Pattern::Constructor(dk, pc, args, Some(Box::new(p_inner))),
                span,
            )
        }
        Pattern::Constructor(_, _, _, None) => p,
        Pattern::Record(fields) => {
            let fields = fields
                .into_iter()
                .map(|(name, inner_p, ty)| (name, walk_pat(inner_p, st), ty))
                .collect();
            Located::new(Pattern::Record(fields), span)
        }
    }
}

// ---------------------------------------------------------------------------
// walk_exp — rewrite expressions
// ---------------------------------------------------------------------------

/// Rewrites expressions: specializes `Constructor` expressions with closed
/// concrete type arguments, and recurses into `Case` arm patterns. Also
/// rewrites constructor (type) annotations embedded in all expression forms.
fn walk_exp(e: LocatedExpression, st: &mut State) -> LocatedExpression {
    let span = e.span.clone();
    match e.node {
        Expression::Constructor(dk, PatternConstructor::Var(pn), args, eo) if !args.is_empty() => {
            // Recurse into argument expression.
            let eo = eo.map(|inner| Box::new(walk_exp_structural(*inner, st)));
            let e_rebuilt = Located::new(
                Expression::Constructor(dk, PatternConstructor::Var(pn), args.clone(), eo.clone()),
                span.clone(),
            );
            if args.iter().any(is_open) {
                return e_rebuilt;
            }
            let dt_id = match st.constructors.get(&pn).copied() {
                None => return e_rebuilt,
                Some(id) => id,
            };
            let dt = match st.datatypes.get(&dt_id).cloned() {
                None => return e_rebuilt,
                Some(dt) => dt,
            };
            let (_, cmap) = consider_specialization(st, dt_id, args, dt);
            let Some(&new_pn) = cmap.get(&pn) else {
                return e_rebuilt;
            };
            Located::new(
                Expression::Constructor(dk, PatternConstructor::Var(new_pn), vec![], eo),
                span,
            )
        }
        Expression::Case(disc, arms, meta) => {
            // Walk the discriminant and each arm expression structurally, and
            // walk each arm pattern for constructor specialization.
            let disc = Box::new(walk_exp_structural(*disc, st));
            let arms = arms
                .into_iter()
                .map(|(pat, arm_e)| {
                    let pat = walk_pat(pat, st);
                    let arm_e = walk_exp_structural(arm_e, st);
                    (pat, arm_e)
                })
                .collect();
            let meta = CaseMeta {
                disc: spec_con(meta.disc, st),
                result: spec_con(meta.result, st),
            };
            Located::new(Expression::Case(disc, arms, meta), span)
        }
        // All other expression forms: delegate to structural walker.
        _ => walk_exp_structural(Located::new(e.node, span), st),
    }
}

/// Structurally walks an expression, applying `spec_con` to embedded
/// constructor (type) terms and `walk_exp` to sub-expressions.
fn walk_exp_structural(e: LocatedExpression, st: &mut State) -> LocatedExpression {
    let span = e.span.clone();
    match e.node {
        Expression::Prim(_) | Expression::Rel(_) | Expression::Named(_) | Expression::Ffi(_, _) => {
            e
        }
        Expression::Constructor(dk, pc, cs, arg) => {
            let cs = cs.into_iter().map(|c| spec_con(c, st)).collect();
            let arg = arg.map(|inner| Box::new(walk_exp(*inner, st)));
            Located::new(Expression::Constructor(dk, pc, cs, arg), span)
        }
        Expression::FfiApp(m, f, args) => {
            let args = args
                .into_iter()
                .map(|(expr, c)| (walk_exp_structural(expr, st), spec_con(c, st)))
                .collect();
            Located::new(Expression::FfiApp(m, f, args), span)
        }
        Expression::App(f, a) => Located::new(
            Expression::App(Box::new(walk_exp(*f, st)), Box::new(walk_exp(*a, st))),
            span,
        ),
        Expression::Abs(x, dom, ran, body) => Located::new(
            Expression::Abs(
                x,
                spec_con(dom, st),
                spec_con(ran, st),
                Box::new(walk_exp(*body, st)),
            ),
            span,
        ),
        Expression::CApp(f, c) => Located::new(
            Expression::CApp(Box::new(walk_exp(*f, st)), spec_con(c, st)),
            span,
        ),
        Expression::CAbs(x, k, body) => {
            Located::new(Expression::CAbs(x, k, Box::new(walk_exp(*body, st))), span)
        }
        Expression::KAbs(x, body) => {
            Located::new(Expression::KAbs(x, Box::new(walk_exp(*body, st))), span)
        }
        Expression::KApp(f, k) => {
            Located::new(Expression::KApp(Box::new(walk_exp(*f, st)), k), span)
        }
        Expression::Record(fields) => {
            let fields = fields
                .into_iter()
                .map(|(name_c, val_e, ty_c)| {
                    (
                        spec_con(name_c, st),
                        walk_exp(val_e, st),
                        spec_con(ty_c, st),
                    )
                })
                .collect();
            Located::new(Expression::Record(fields), span)
        }
        Expression::Field(record, field_c, meta) => Located::new(
            Expression::Field(
                Box::new(walk_exp(*record, st)),
                spec_con(field_c, st),
                FieldMeta {
                    field: spec_con(meta.field, st),
                    rest: spec_con(meta.rest, st),
                },
            ),
            span,
        ),
        Expression::Concat(le, lc, re, rc) => Located::new(
            Expression::Concat(
                Box::new(walk_exp(*le, st)),
                spec_con(lc, st),
                Box::new(walk_exp(*re, st)),
                spec_con(rc, st),
            ),
            span,
        ),
        Expression::Cut(record, field_c, meta) => Located::new(
            Expression::Cut(
                Box::new(walk_exp(*record, st)),
                spec_con(field_c, st),
                FieldMeta {
                    field: spec_con(meta.field, st),
                    rest: spec_con(meta.rest, st),
                },
            ),
            span,
        ),
        Expression::CutMulti(record, field_c, rest_meta) => Located::new(
            Expression::CutMulti(
                Box::new(walk_exp(*record, st)),
                spec_con(field_c, st),
                RestMeta {
                    rest: spec_con(rest_meta.rest, st),
                },
            ),
            span,
        ),
        Expression::Case(disc, arms, meta) => {
            let disc = Box::new(walk_exp(*disc, st));
            let arms = arms
                .into_iter()
                .map(|(pat, arm_e)| (walk_pat(pat, st), walk_exp(arm_e, st)))
                .collect();
            let meta = CaseMeta {
                disc: spec_con(meta.disc, st),
                result: spec_con(meta.result, st),
            };
            Located::new(Expression::Case(disc, arms, meta), span)
        }
        Expression::Write(inner) => {
            Located::new(Expression::Write(Box::new(walk_exp(*inner, st))), span)
        }
        Expression::Closure(id, env) => {
            let env = env.into_iter().map(|e| walk_exp(e, st)).collect();
            Located::new(Expression::Closure(id, env), span)
        }
        Expression::Let(x, ty, e1, e2) => Located::new(
            Expression::Let(
                x,
                spec_con(ty, st),
                Box::new(walk_exp(*e1, st)),
                Box::new(walk_exp(*e2, st)),
            ),
            span,
        ),
        Expression::ServerCall(id, args, result_ty, mode) => {
            let args = args.into_iter().map(|e| walk_exp(e, st)).collect();
            Located::new(
                Expression::ServerCall(id, args, spec_con(result_ty, st), mode),
                span,
            )
        }
    }
}

// ---------------------------------------------------------------------------
// walk_decl — apply specialization rewrite to a declaration
// ---------------------------------------------------------------------------

/// Applies `spec_con` and `walk_exp` throughout a declaration.
fn walk_decl(d: LocatedDeclaration, st: &mut State) -> LocatedDeclaration {
    let span = d.span.clone();
    match d.node {
        Declaration::Constructor(name, id, k, c) => {
            Located::new(Declaration::Constructor(name, id, k, spec_con(c, st)), span)
        }
        Declaration::Datatype(dts) => {
            let dts = dts
                .into_iter()
                .map(|dt| DatatypeDecl {
                    name: dt.name,
                    id: dt.id,
                    params: dt.params,
                    constrs: dt
                        .constrs
                        .into_iter()
                        .map(|(n, id, to)| (n, id, to.map(|t| spec_con(t, st))))
                        .collect(),
                })
                .collect();
            Located::new(Declaration::Datatype(dts), span)
        }
        Declaration::Val(name, id, ty, expr, comment) => Located::new(
            Declaration::Val(name, id, spec_con(ty, st), walk_exp(expr, st), comment),
            span,
        ),
        Declaration::ValRec(bindings) => {
            let bindings = bindings
                .into_iter()
                .map(|(name, id, ty, expr, comment)| {
                    (name, id, spec_con(ty, st), walk_exp(expr, st), comment)
                })
                .collect();
            Located::new(Declaration::ValRec(bindings), span)
        }
        Declaration::Table {
            sql_name,
            id,
            con,
            sql_con,
            exp,
            pk_con,
            pk_exp,
            unique_con,
        } => Located::new(
            Declaration::Table {
                sql_name,
                id,
                con: spec_con(con, st),
                sql_con,
                exp: walk_exp(exp, st),
                pk_con: spec_con(pk_con, st),
                pk_exp: walk_exp(pk_exp, st),
                unique_con: spec_con(unique_con, st),
            },
            span,
        ),
        Declaration::View(name, id, sql, expr, con) => Located::new(
            Declaration::View(name, id, sql, walk_exp(expr, st), spec_con(con, st)),
            span,
        ),
        Declaration::Cookie(name, id, con, comment) => Located::new(
            Declaration::Cookie(name, id, spec_con(con, st), comment),
            span,
        ),
        Declaration::Task(e1, e2) => {
            Located::new(Declaration::Task(walk_exp(e1, st), walk_exp(e2, st)), span)
        }
        Declaration::Policy(e) => Located::new(Declaration::Policy(walk_exp(e, st)), span),
        Declaration::Index(e1, e2) => {
            Located::new(Declaration::Index(walk_exp(e1, st), walk_exp(e2, st)), span)
        }
        // Declarations that have no embedded constructors or expressions.
        Declaration::Export(_, _, _)
        | Declaration::Sequence(_, _, _)
        | Declaration::Database(_)
        | Declaration::Style(_, _, _)
        | Declaration::OnError(_) => d,
    }
}

// ---------------------------------------------------------------------------
// fancy_datatypes — find datatypes that cannot be specialized
// ---------------------------------------------------------------------------

/// Collects the ids of all datatypes `n` that appear as `Named(n)` at the root
/// of a `CApp(_, c2)` where `c2` has a free `CRel` (is open). Such datatypes
/// are parameterized in a higher-kinded or open way and cannot be monomorphized.
///
/// Before scanning, self-references within each `DDatatype` group are blinded
/// (replaced with `Unit`) so a datatype does not count itself as fancy.
fn compute_fancy_datatypes(file: &File) -> HashSet<usize> {
    // Build file' where self-references in DDatatype are replaced with CUnit.
    let file_prime: File = file
        .iter()
        .map(|d| {
            let span = d.span.clone();
            match &d.node {
                Declaration::Datatype(dts) => {
                    // Collect the ids of all datatypes in this group.
                    let dt_ids: HashSet<usize> = dts.iter().map(|dt| dt.id).collect();
                    // Rewrite constructors in each DatatypeDecl, replacing
                    // Named(n) with Unit when n is a self-reference.
                    let new_dts = dts
                        .iter()
                        .map(|dt| DatatypeDecl {
                            name: dt.name.clone(),
                            id: dt.id,
                            params: dt.params.clone(),
                            constrs: dt
                                .constrs
                                .iter()
                                .map(|(cname, cid, to)| {
                                    (
                                        cname.clone(),
                                        *cid,
                                        to.as_ref().map(|t| blind_named(&dt_ids, t.clone())),
                                    )
                                })
                                .collect(),
                        })
                        .collect();
                    Located::new(Declaration::Datatype(new_dts), span)
                }
                _ => d.clone(),
            }
        })
        .collect();

    // Walk file' and find all n where App(_, c2) with is_open(c2) and
    // find_app gives Named(n).
    let mut fancy: HashSet<usize> = HashSet::new();
    for decl in &file_prime {
        collect_fancy_in_decl(&decl.node, &mut fancy);
    }
    fancy
}

/// Replace `Constructor::Named(n)` with `Constructor::Unit` when `n` is in `ids`.
fn blind_named(ids: &HashSet<usize>, c: LocatedConstructor) -> LocatedConstructor {
    let span = c.span.clone();
    match c.node {
        Constructor::Named(n) if ids.contains(&n) => Located::new(Constructor::Unit, span),
        Constructor::Named(_)
        | Constructor::Rel(_)
        | Constructor::Ffi(_, _)
        | Constructor::Name(_)
        | Constructor::Unit
        | Constructor::Map(_, _) => c,
        Constructor::TFun(a, b) => Located::new(
            Constructor::TFun(
                Box::new(blind_named(ids, *a)),
                Box::new(blind_named(ids, *b)),
            ),
            span,
        ),
        Constructor::TCFun(x, k, b) => Located::new(
            Constructor::TCFun(x, k, Box::new(blind_named(ids, *b))),
            span,
        ),
        Constructor::TRecord(inner) => Located::new(
            Constructor::TRecord(Box::new(blind_named(ids, *inner))),
            span,
        ),
        Constructor::App(f, a) => Located::new(
            Constructor::App(
                Box::new(blind_named(ids, *f)),
                Box::new(blind_named(ids, *a)),
            ),
            span,
        ),
        Constructor::Abs(x, k, b) => {
            Located::new(Constructor::Abs(x, k, Box::new(blind_named(ids, *b))), span)
        }
        Constructor::KAbs(x, b) => {
            Located::new(Constructor::KAbs(x, Box::new(blind_named(ids, *b))), span)
        }
        Constructor::KApp(inner, k) => Located::new(
            Constructor::KApp(Box::new(blind_named(ids, *inner)), k),
            span,
        ),
        Constructor::TKFun(x, b) => {
            Located::new(Constructor::TKFun(x, Box::new(blind_named(ids, *b))), span)
        }
        Constructor::Record(k, pairs) => {
            let pairs = pairs
                .into_iter()
                .map(|(n, v)| (blind_named(ids, n), blind_named(ids, v)))
                .collect();
            Located::new(Constructor::Record(k, pairs), span)
        }
        Constructor::Concat(a, b) => Located::new(
            Constructor::Concat(
                Box::new(blind_named(ids, *a)),
                Box::new(blind_named(ids, *b)),
            ),
            span,
        ),
        Constructor::Tuple(cs) => Located::new(
            Constructor::Tuple(cs.into_iter().map(|c| blind_named(ids, c)).collect()),
            span,
        ),
        Constructor::Proj(c, i) => {
            Located::new(Constructor::Proj(Box::new(blind_named(ids, *c)), i), span)
        }
    }
}

/// Scan a constructor for `App(_, c2)` nodes where `c2` is open and the
/// root is `Named(n)`; add `n` to `fancy`.
fn collect_fancy_in_con(c: &Constructor, fancy: &mut HashSet<usize>) {
    match c {
        Constructor::App(c1, c2) => {
            // Check the whole application spine.
            if is_open(c2) {
                // Find the root named type of this application.
                let _dummy_span = Located::new(c.clone(), Span::dummy());
                if let Some((n, _)) = find_app(c, vec![]) {
                    fancy.insert(n);
                }
            }
            collect_fancy_in_con(&c1.node, fancy);
            collect_fancy_in_con(&c2.node, fancy);
        }
        Constructor::TFun(a, b) => {
            collect_fancy_in_con(&a.node, fancy);
            collect_fancy_in_con(&b.node, fancy);
        }
        Constructor::TCFun(_, _, b) => collect_fancy_in_con(&b.node, fancy),
        Constructor::TRecord(inner) => collect_fancy_in_con(&inner.node, fancy),
        Constructor::Abs(_, _, b) => collect_fancy_in_con(&b.node, fancy),
        Constructor::KAbs(_, b) => collect_fancy_in_con(&b.node, fancy),
        Constructor::KApp(inner, _) => collect_fancy_in_con(&inner.node, fancy),
        Constructor::TKFun(_, b) => collect_fancy_in_con(&b.node, fancy),
        Constructor::Record(_, pairs) => {
            for (n, v) in pairs {
                collect_fancy_in_con(&n.node, fancy);
                collect_fancy_in_con(&v.node, fancy);
            }
        }
        Constructor::Concat(a, b) => {
            collect_fancy_in_con(&a.node, fancy);
            collect_fancy_in_con(&b.node, fancy);
        }
        Constructor::Tuple(cs) => {
            for c in cs {
                collect_fancy_in_con(&c.node, fancy);
            }
        }
        Constructor::Proj(c, _) => collect_fancy_in_con(&c.node, fancy),
        Constructor::Rel(_)
        | Constructor::Named(_)
        | Constructor::Ffi(_, _)
        | Constructor::Name(_)
        | Constructor::Unit
        | Constructor::Map(_, _) => {}
    }
}

fn collect_fancy_in_exp(e: &Expression, fancy: &mut HashSet<usize>) {
    match e {
        Expression::Prim(_) | Expression::Rel(_) | Expression::Named(_) | Expression::Ffi(_, _) => {
        }
        Expression::Constructor(_, _, cs, arg) => {
            for c in cs {
                collect_fancy_in_con(&c.node, fancy);
            }
            if let Some(inner) = arg {
                collect_fancy_in_exp(&inner.node, fancy);
            }
        }
        Expression::FfiApp(_, _, args) => {
            for (expr, c) in args {
                collect_fancy_in_exp(&expr.node, fancy);
                collect_fancy_in_con(&c.node, fancy);
            }
        }
        Expression::App(f, a) => {
            collect_fancy_in_exp(&f.node, fancy);
            collect_fancy_in_exp(&a.node, fancy);
        }
        Expression::Abs(_, dom, ran, body) => {
            collect_fancy_in_con(&dom.node, fancy);
            collect_fancy_in_con(&ran.node, fancy);
            collect_fancy_in_exp(&body.node, fancy);
        }
        Expression::CApp(f, c) => {
            collect_fancy_in_exp(&f.node, fancy);
            collect_fancy_in_con(&c.node, fancy);
        }
        Expression::CAbs(_, _, body) => collect_fancy_in_exp(&body.node, fancy),
        Expression::KAbs(_, body) => collect_fancy_in_exp(&body.node, fancy),
        Expression::KApp(f, _) => collect_fancy_in_exp(&f.node, fancy),
        Expression::Record(fields) => {
            for (name_c, val_e, ty_c) in fields {
                collect_fancy_in_con(&name_c.node, fancy);
                collect_fancy_in_exp(&val_e.node, fancy);
                collect_fancy_in_con(&ty_c.node, fancy);
            }
        }
        Expression::Field(record, field_c, meta) => {
            collect_fancy_in_exp(&record.node, fancy);
            collect_fancy_in_con(&field_c.node, fancy);
            collect_fancy_in_con(&meta.field.node, fancy);
            collect_fancy_in_con(&meta.rest.node, fancy);
        }
        Expression::Concat(le, lc, re, rc) => {
            collect_fancy_in_exp(&le.node, fancy);
            collect_fancy_in_con(&lc.node, fancy);
            collect_fancy_in_exp(&re.node, fancy);
            collect_fancy_in_con(&rc.node, fancy);
        }
        Expression::Cut(record, field_c, meta) => {
            collect_fancy_in_exp(&record.node, fancy);
            collect_fancy_in_con(&field_c.node, fancy);
            collect_fancy_in_con(&meta.field.node, fancy);
            collect_fancy_in_con(&meta.rest.node, fancy);
        }
        Expression::CutMulti(record, field_c, rest_meta) => {
            collect_fancy_in_exp(&record.node, fancy);
            collect_fancy_in_con(&field_c.node, fancy);
            collect_fancy_in_con(&rest_meta.rest.node, fancy);
        }
        Expression::Case(disc, arms, meta) => {
            collect_fancy_in_exp(&disc.node, fancy);
            for (pat, arm_e) in arms {
                collect_fancy_in_pat(&pat.node, fancy);
                collect_fancy_in_exp(&arm_e.node, fancy);
            }
            collect_fancy_in_con(&meta.disc.node, fancy);
            collect_fancy_in_con(&meta.result.node, fancy);
        }
        Expression::Write(inner) => collect_fancy_in_exp(&inner.node, fancy),
        Expression::Closure(_, env) => {
            for e in env {
                collect_fancy_in_exp(&e.node, fancy);
            }
        }
        Expression::Let(_, ty, e1, e2) => {
            collect_fancy_in_con(&ty.node, fancy);
            collect_fancy_in_exp(&e1.node, fancy);
            collect_fancy_in_exp(&e2.node, fancy);
        }
        Expression::ServerCall(_, args, result_ty, _) => {
            for e in args {
                collect_fancy_in_exp(&e.node, fancy);
            }
            collect_fancy_in_con(&result_ty.node, fancy);
        }
    }
}

fn collect_fancy_in_pat(p: &Pattern, fancy: &mut HashSet<usize>) {
    match p {
        Pattern::Var(_, ty) => collect_fancy_in_con(&ty.node, fancy),
        Pattern::Prim(_) => {}
        Pattern::Constructor(_, _, cs, po) => {
            for c in cs {
                collect_fancy_in_con(&c.node, fancy);
            }
            if let Some(inner) = po {
                collect_fancy_in_pat(&inner.node, fancy);
            }
        }
        Pattern::Record(fields) => {
            for (_, p, ty) in fields {
                collect_fancy_in_pat(&p.node, fancy);
                collect_fancy_in_con(&ty.node, fancy);
            }
        }
    }
}

fn collect_fancy_in_decl(d: &Declaration, fancy: &mut HashSet<usize>) {
    match d {
        Declaration::Constructor(_, _, _, c) => collect_fancy_in_con(&c.node, fancy),
        Declaration::Datatype(dts) => {
            for dt in dts {
                for (_, _, to) in &dt.constrs {
                    if let Some(t) = to {
                        collect_fancy_in_con(&t.node, fancy);
                    }
                }
            }
        }
        Declaration::Val(_, _, ty, expr, _) => {
            collect_fancy_in_con(&ty.node, fancy);
            collect_fancy_in_exp(&expr.node, fancy);
        }
        Declaration::ValRec(bindings) => {
            for (_, _, ty, expr, _) in bindings {
                collect_fancy_in_con(&ty.node, fancy);
                collect_fancy_in_exp(&expr.node, fancy);
            }
        }
        Declaration::Table {
            con,
            exp,
            pk_con,
            pk_exp,
            unique_con,
            ..
        } => {
            collect_fancy_in_con(&con.node, fancy);
            collect_fancy_in_exp(&exp.node, fancy);
            collect_fancy_in_con(&pk_con.node, fancy);
            collect_fancy_in_exp(&pk_exp.node, fancy);
            collect_fancy_in_con(&unique_con.node, fancy);
        }
        Declaration::View(_, _, _, expr, con) => {
            collect_fancy_in_exp(&expr.node, fancy);
            collect_fancy_in_con(&con.node, fancy);
        }
        Declaration::Cookie(_, _, con, _) => collect_fancy_in_con(&con.node, fancy),
        Declaration::Task(e1, e2) => {
            collect_fancy_in_exp(&e1.node, fancy);
            collect_fancy_in_exp(&e2.node, fancy);
        }
        Declaration::Policy(e) => collect_fancy_in_exp(&e.node, fancy),
        Declaration::Index(e1, e2) => {
            collect_fancy_in_exp(&e1.node, fancy);
            collect_fancy_in_exp(&e2.node, fancy);
        }
        Declaration::Export(_, _, _)
        | Declaration::Sequence(_, _, _)
        | Declaration::Database(_)
        | Declaration::Style(_, _, _)
        | Declaration::OnError(_) => {}
    }
}

// ---------------------------------------------------------------------------
// do_decl — process one declaration
// ---------------------------------------------------------------------------

/// Processes a single declaration in the specialization pass.
///
/// Returns a vec of output declarations (possibly including newly-generated
/// specialization decls prepended before the original).
fn do_decl(
    d: LocatedDeclaration,
    st: &mut State,
    fancy_datatypes: &HashSet<usize>,
) -> Vec<LocatedDeclaration> {
    let span = d.span.clone();

    // First apply the specDecl rewrite (spec_con + walk_exp throughout).
    let d = walk_decl(d, st);

    match d.node.clone() {
        Declaration::Datatype(ref dts) => {
            // Is any of the datatypes in this group fancy?
            let is_fancy = dts.iter().any(|dt| fancy_datatypes.contains(&dt.id));
            if is_fancy {
                // Do not register; just emit as-is.
                return vec![d];
            }

            // Take accumulated new_decls, drain them.
            let accumulated: Vec<_> = std::mem::take(&mut st.new_decls);

            // Register these datatypes and their constructors in state.
            for dt in dts {
                let dt_id = dt.id;
                let spec = DatatypeSpec {
                    name: dt.name.clone(),
                    params: dt.params.len(),
                    constructors: dt.constrs.clone(),
                    specializations: BTreeMap::new(),
                };
                st.datatypes.insert(dt_id, spec);
                for (_, con_id, _) in &dt.constrs {
                    st.constructors.insert(*con_id, dt_id);
                }
            }

            // Merge accumulated specialization decls with the current DDatatype.
            if accumulated.is_empty() {
                vec![d]
            } else {
                // Build a single DDatatype with all specialization decls + current dts.
                let mut merged_dts: Vec<DatatypeDecl> = accumulated
                    .into_iter()
                    .map(|(name, id, params, constrs)| DatatypeDecl {
                        name,
                        id,
                        params,
                        constrs,
                    })
                    .collect();
                // Append the original datatypes.
                if let Declaration::Datatype(orig_dts) = &d.node {
                    merged_dts.extend(orig_dts.clone());
                }
                vec![Located::new(Declaration::Datatype(merged_dts), span)]
            }
        }
        _ => {
            // Non-datatype declaration: prepend any accumulated specialization decls.
            let accumulated: Vec<_> = std::mem::take(&mut st.new_decls);
            if accumulated.is_empty() {
                vec![d]
            } else {
                let spec_dt: Vec<DatatypeDecl> = accumulated
                    .into_iter()
                    .map(|(name, id, params, constrs)| DatatypeDecl {
                        name,
                        id,
                        params,
                        constrs,
                    })
                    .collect();
                let spec_decl = Located::new(Declaration::Datatype(spec_dt), span);
                vec![spec_decl, d]
            }
        }
    }
}

// ---------------------------------------------------------------------------
// specialize — top-level entry point
// ---------------------------------------------------------------------------

/// Monomorphizes polymorphic datatype uses in a Core file.
///
/// For each use of a polymorphic datatype with concrete (closed) type
/// arguments, generates a monomorphic copy and replaces the use with it.
pub fn specialize(file: File) -> File {
    let fancy_datatypes = compute_fancy_datatypes(&file);

    let mut st = State {
        count: file_util::max_name(&file) + 1,
        datatypes: HashMap::new(),
        constructors: HashMap::new(),
        new_decls: vec![],
    };

    let mut output: File = Vec::new();
    for d in file {
        let result = do_decl(d, &mut st, &fancy_datatypes);
        output.extend(result);
    }
    output
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::datatype_kind::DatatypeKind;
    use crate::error_types::Located;

    fn dummy<T>(node: T) -> Located<T> {
        Located::dummy(node)
    }

    /// Build a simple monomorphic datatype (no params).
    #[test]
    fn test_monomorphic_datatype_passes_through() {
        // datatype Bool = True | False
        let dt = DatatypeDecl {
            name: "Bool".to_string(),
            id: 1,
            params: vec![],
            constrs: vec![
                ("True".to_string(), 2, None),
                ("False".to_string(), 3, None),
            ],
        };
        let file: File = vec![dummy(Declaration::Datatype(vec![dt.clone()]))];
        let result = specialize(file);
        // Monomorphic datatype: should be registered but the decl passes through.
        assert_eq!(result.len(), 1);
        if let Declaration::Datatype(dts) = &result[0].node {
            assert_eq!(dts.len(), 1);
            assert_eq!(dts[0].name, "Bool");
        } else {
            panic!("Expected Datatype declaration");
        }
    }

    /// is_open detects Rel in a simple position.
    #[test]
    fn test_is_open_rel() {
        let c = dummy(Constructor::Rel(0));
        assert!(is_open(&c));
    }

    /// is_open returns false for a named type.
    #[test]
    fn test_is_open_named() {
        let c = dummy(Constructor::Named(42));
        assert!(!is_open(&c));
    }

    /// is_open returns true if Rel is nested inside TFun.
    #[test]
    fn test_is_open_nested() {
        let c = dummy(Constructor::TFun(
            Box::new(dummy(Constructor::Rel(0))),
            Box::new(dummy(Constructor::Unit)),
        ));
        assert!(is_open(&c));
    }

    /// find_app correctly unravels CApp spine.
    #[test]
    fn test_find_app_basic() {
        // App(Named(5), Unit) → Some((5, [Unit]))
        let inner = Constructor::App(
            Box::new(dummy(Constructor::Named(5))),
            Box::new(dummy(Constructor::Unit)),
        );
        let result = find_app(&inner, vec![]);
        assert!(result.is_some());
        let (n, args) = result.unwrap();
        assert_eq!(n, 5);
        assert_eq!(args.len(), 1);
    }

    /// find_app on nested CApp returns all args.
    #[test]
    fn test_find_app_nested() {
        // App(App(Named(7), Named(1)), Named(2))
        // → (7, [Named(1), Named(2)])
        let inner = Constructor::App(
            Box::new(dummy(Constructor::App(
                Box::new(dummy(Constructor::Named(7))),
                Box::new(dummy(Constructor::Named(1))),
            ))),
            Box::new(dummy(Constructor::Named(2))),
        );
        let result = find_app(&inner, vec![]);
        assert!(result.is_some());
        let (n, args) = result.unwrap();
        assert_eq!(n, 7);
        assert_eq!(args.len(), 2);
    }

    /// A polymorphic datatype used with a concrete type arg gets specialized.
    #[test]
    fn test_specialize_simple_option_like() {
        // Datatype Option a = None | Some a    (id=10, None=11, Some=12, param=["a"])
        let dt = DatatypeDecl {
            name: "Option".to_string(),
            id: 10,
            params: vec!["a".to_string()],
            constrs: vec![
                ("None".to_string(), 11, None),
                (
                    "Some".to_string(),
                    12,
                    Some(dummy(Constructor::Rel(0))), // the type param 'a'
                ),
            ],
        };
        // A value: val x : Option<Unit> = None
        //   Type: App(Named(10), Unit)
        //   Expr: Constructor(Enum, Var(11), [Unit], None)
        let val_ty = dummy(Constructor::App(
            Box::new(dummy(Constructor::Named(10))),
            Box::new(dummy(Constructor::Unit)),
        ));
        let val_expr = dummy(Expression::Constructor(
            DatatypeKind::Option,
            PatternConstructor::Var(11),
            vec![dummy(Constructor::Unit)],
            None,
        ));

        let file: File = vec![
            dummy(Declaration::Datatype(vec![dt])),
            dummy(Declaration::Val(
                "x".to_string(),
                20,
                val_ty,
                val_expr,
                String::new(),
            )),
        ];

        let result = specialize(file);

        // We expect:
        // 1. The original Datatype decl (Option registered in state).
        // 2. A new Datatype decl for Option_s (the monomorphic specialization)
        //    followed by the Val decl, OR merged.
        // The exact structure depends on ordering. Check that we have at least one
        // specialized datatype and that the Val's expr no longer has type args.
        let mut found_specialized = false;
        let mut found_val = false;
        for d in &result {
            match &d.node {
                Declaration::Datatype(dts) => {
                    for dt in dts {
                        if dt.name.contains("_s") {
                            found_specialized = true;
                            // The Some constructor's arg type should now be Unit (Rel(0) → Unit).
                            for (cname, _, to) in &dt.constrs {
                                if cname == "Some" {
                                    if let Some(t) = to {
                                        assert!(
                                            matches!(t.node, Constructor::Unit),
                                            "Some arg should be Unit after specialization"
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
                Declaration::Val(name, _, _, expr, _) if name == "x" => {
                    found_val = true;
                    // The expression should have empty type args now.
                    if let Expression::Constructor(_, PatternConstructor::Var(_), args, _) =
                        &expr.node
                    {
                        assert!(
                            args.is_empty(),
                            "Constructor expression should have no type args after specialization"
                        );
                    }
                }
                _ => {}
            }
        }
        assert!(found_specialized, "Expected a specialized datatype");
        assert!(found_val, "Expected the Val declaration");
    }

    /// An empty file passes through unchanged.
    #[test]
    fn test_empty_file() {
        let file: File = vec![];
        let result = specialize(file);
        assert!(result.is_empty());
    }
}
