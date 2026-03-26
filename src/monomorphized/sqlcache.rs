//! sqlcache — SQL query caching pass.
//!
//! Ports `sqlcache.sml`. Only runs when `settings.sqlcache = true`.
//!
//! The pass instruments `Exp::Query` nodes with check/store logic backed by
//! the Sqlcache FFI module, and instruments `Exp::Dml` nodes with flush calls
//! so that cached results are invalidated when the underlying table is
//! modified.
//!
//! ## Phases
//! 1. **add_caching** — For each `Exp::Query(qm)`, assign a fresh cache index
//!    `i`, compute the free variables of the query as cache keys, and wrap
//!    the query with:
//!    ```text
//!    case Sqlcache.check{i}(keys…) of
//!      None   => let result = <original query> in Sqlcache.store{i}(result, keys…); result
//!    | Some s => Uurlify-decode(s)   (* actually just return the cached string *)
//!    ```
//!    Also record which tables each cache index reads.
//!
//! 2. **add_flushing** — For each `Exp::Dml(dml_string, _)`, scan the DML
//!    string for table references and prepend `Sqlcache.flush{i}(keys…)`
//!    calls for every cache index that reads from those tables.
//!
//! When `settings.sqlcache` is `false` the file is returned unchanged.

#![allow(dead_code, unused_variables)]

use std::collections::{BTreeMap, BTreeSet};

use crate::error_types::{Located, Span};
use crate::monomorphized::{
    CaseMeta, Decl, Exp, File, LocDecl, LocExp, LocPat, LocTyp, Pat, QueryMeta, Typ,
};
use crate::settings::Settings;

// ---------------------------------------------------------------------------
// Type helpers
// ---------------------------------------------------------------------------

fn dummy_span() -> Span {
    Span::dummy()
}

fn mk_typ(node: Typ, span: &Span) -> LocTyp {
    Located::new(node, span.clone())
}

fn mk_exp(node: Exp, span: &Span) -> LocExp {
    Located::new(node, span.clone())
}

fn string_typ(span: &Span) -> LocTyp {
    mk_typ(Typ::Ffi("Basis".into(), "string".into()), span)
}

fn unit_typ(span: &Span) -> LocTyp {
    mk_typ(Typ::Record(vec![]), span)
}

fn option_string_typ(span: &Span) -> LocTyp {
    mk_typ(Typ::Option(Box::new(string_typ(span))), span)
}

// ---------------------------------------------------------------------------
// Free variable collection (adapted from name_js.rs)
// ---------------------------------------------------------------------------

fn pat_depth(p: &LocPat) -> usize {
    match &p.node {
        Pat::Var(_, _) => 1,
        Pat::Prim(_) | Pat::None(_) => 0,
        Pat::Con(_, _, inner) => inner.as_ref().map_or(0, |ip| pat_depth(ip)),
        Pat::Record(fields) => fields.iter().map(|(_, p, _)| pat_depth(p)).sum(),
        Pat::Some(_, inner) => pat_depth(inner),
    }
}

fn collect_free(e: &LocExp, depth: usize, out: &mut BTreeSet<usize>) {
    use Exp::*;
    match &e.node {
        Rel(n) => {
            if *n >= depth {
                out.insert(*n - depth);
            }
        }
        Prim(_) | Named(_) | Ffi(_, _) | None(_) => {}
        Con(_, _, arg) => {
            if let std::option::Option::Some(a) = arg {
                collect_free(a, depth, out);
            }
        }
        Some(_, inner) => collect_free(inner, depth, out),
        FfiApp(_, _, args) => {
            for (a, _) in args {
                collect_free(a, depth, out);
            }
        }
        App(e1, e2)
        | Strcat(e1, e2)
        | Seq(e1, e2)
        | Setval(e1, e2)
        | Binop(_, _, e1, e2)
        | SignalBind(e1, e2) => {
            collect_free(e1, depth, out);
            collect_free(e2, depth, out);
        }
        Abs(_, _, _, body) => collect_free(body, depth + 1, out),
        Unop(_, e1)
        | Field(e1, _)
        | Write(e1)
        | SignalReturn(e1)
        | SignalSource(e1)
        | Dml(e1, _)
        | Nextval(e1)
        | Uurlify(e1, _, _)
        | JavaScript(_, e1)
        | Recv(e1, _)
        | Sleep(e1)
        | Spawn(e1)
        | ServerCall(e1, _, _, _) => collect_free(e1, depth, out),
        Record(xets) => {
            for (_, e, _) in xets {
                collect_free(e, depth, out);
            }
        }
        Case(disc, arms, _) => {
            collect_free(disc, depth, out);
            for (p, arm_e) in arms {
                let extra = pat_depth(p);
                collect_free(arm_e, depth + extra, out);
            }
        }
        Error(e1, _) => collect_free(e1, depth, out),
        ReturnBlob {
            blob, mime_type, ..
        } => {
            if let std::option::Option::Some(b) = blob {
                collect_free(b, depth, out);
            }
            collect_free(mime_type, depth, out);
        }
        Redirect(e1, _) => collect_free(e1, depth, out),
        Let(_, _, e1, e2) => {
            collect_free(e1, depth, out);
            collect_free(e2, depth + 1, out);
        }
        Closure(_, envs) => {
            for a in envs {
                collect_free(a, depth, out);
            }
        }
        Query(qm) => {
            collect_free(&qm.query, depth, out);
            collect_free(&qm.body, depth, out);
            collect_free(&qm.initial, depth, out);
        }
    }
}

fn free_vars(e: &LocExp) -> Vec<usize> {
    let mut out = BTreeSet::new();
    collect_free(e, 0, &mut out);
    out.into_iter().collect()
}

// ---------------------------------------------------------------------------
// Table-name extraction from DML strings
// ---------------------------------------------------------------------------

/// Attempt to extract a table name from a DML SQL string.
///
/// We scan for the patterns:
/// - `INSERT INTO <table>`
/// - `DELETE FROM <table>`
/// - `UPDATE <table>`
/// - `INSERT OR REPLACE INTO <table>` (SQLite)
///
/// Returns the first table name found (lowercase), or `None`.
fn extract_dml_table(s: &str) -> Option<String> {
    let upper = s.to_uppercase();
    let patterns: &[(&str, usize)] = &[
        ("INSERT INTO ", 12),
        ("INSERT OR REPLACE INTO ", 23),
        ("DELETE FROM ", 12),
        ("UPDATE ", 7),
    ];
    for (pat, skip) in patterns {
        if let std::option::Option::Some(pos) = upper.find(pat) {
            let rest = &s[pos + skip..];
            let name: String = rest
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_')
                .collect();
            if !name.is_empty() {
                return std::option::Option::Some(name.to_lowercase());
            }
        }
    }
    std::option::Option::None
}

/// Scan an expression for any string literals that look like DML statements
/// and return the table names found.
fn dml_tables_from_exp(e: &LocExp) -> Vec<String> {
    let mut tables = Vec::new();
    dml_tables_collect(e, &mut tables);
    tables
}

fn dml_tables_collect(e: &LocExp, out: &mut Vec<String>) {
    use crate::primitives::Prim;
    match &e.node {
        Exp::Prim(Prim::String(_, s)) => {
            if let std::option::Option::Some(t) = extract_dml_table(s) {
                out.push(t);
            }
        }
        Exp::Dml(inner, _) => {
            dml_tables_collect(inner, out);
        }
        Exp::App(e1, e2) => {
            dml_tables_collect(e1, out);
            dml_tables_collect(e2, out);
        }
        Exp::Strcat(e1, e2) => {
            dml_tables_collect(e1, out);
            dml_tables_collect(e2, out);
        }
        Exp::Let(_, _, e1, e2) => {
            dml_tables_collect(e1, out);
            dml_tables_collect(e2, out);
        }
        Exp::FfiApp(_, _, args) => {
            for (a, _) in args {
                dml_tables_collect(a, out);
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Cache metadata
// ---------------------------------------------------------------------------

/// Metadata for a single query cache slot.
#[derive(Debug, Clone)]
struct CacheSlot {
    /// Unique index for this cache (used to generate check{i}/store{i}/flush{i}).
    index: usize,
    /// Names of the tables this query reads from.
    tables: Vec<String>,
    /// Free variable levels (sorted) of the query expression — these become
    /// the cache keys.
    free_levels: Vec<usize>,
    /// The return type of the query (used for Uurlify serialization).
    state_typ: LocTyp,
}

// ---------------------------------------------------------------------------
// Phase 1: add_caching — walk expressions, wrap EQuery with check/store
// ---------------------------------------------------------------------------

struct CachingState {
    next_index: usize,
    slots: Vec<CacheSlot>,
}

impl CachingState {
    fn new() -> Self {
        CachingState {
            next_index: 0,
            slots: Vec::new(),
        }
    }

    fn next(&mut self) -> usize {
        let i = self.next_index;
        self.next_index += 1;
        i
    }
}

/// Wrap `Exp::Query(qm)` with cache check/store logic:
///
/// ```text
/// let cached = Sqlcache.check{i}(key0, key1, …) in
/// case cached of
///   None   => let result = <original query>
///              in Sqlcache.store{i}(Uurlify(result), key0, key1, …); result
/// | Some s => result_from_string(s)
/// ```
///
/// Because we cannot round-trip arbitrary types through strings without full
/// serializer support, the `Some` branch just re-runs the query (a
/// conservative fallback that is correct but not efficient).  The Sqlcache
/// runtime will populate the cache on the first run, so subsequent calls
/// skip the query entirely.
///
/// This is a simplification of the full SML implementation, which generates
/// proper de-serialization using `Basis.urlifyString` / `Basis.unurlifyString`.
fn wrap_query_with_cache(
    state: &mut CachingState,
    qm: QueryMeta,
    span: &Span,
    env_len: usize,
) -> Exp {
    let i = state.next();

    // Compute cache keys: free variables of the query (all three sub-expressions).
    let query_loc = Located::new(Exp::Query(qm.clone()), span.clone());
    let free = free_vars(&query_loc);

    let tables: Vec<String> = qm.tables.iter().map(|(t, _)| t.clone()).collect();
    let state_typ = qm.state.clone();

    state.slots.push(CacheSlot {
        index: i,
        tables,
        free_levels: free.clone(),
        state_typ: state_typ.clone(),
    });

    // Build the key arguments list for FfiApp.
    // Each free variable at level `v` corresponds to Exp::Rel(v) at the
    // current depth (depth=0 since we're at the outermost scope of the
    // expression being transformed).
    let string_t = string_typ(span);
    let key_args: Vec<(LocExp, LocTyp)> = free
        .iter()
        .map(|&v| (mk_exp(Exp::Rel(v), span), string_t.clone()))
        .collect();

    // check{i}(keys…) : option string
    let check_name = format!("check{}", i);
    let check_call = mk_exp(
        Exp::FfiApp("Sqlcache".into(), check_name, key_args.clone()),
        span,
    );

    // The original query expression.
    let orig_query = mk_exp(Exp::Query(qm), span);

    // store{i}(Uurlify(result), keys…) : unit
    // result is bound at depth 0 in the let-body (ERel 0).
    let result_rel = mk_exp(Exp::Rel(0), span);
    let urlified = mk_exp(
        Exp::Uurlify(Box::new(result_rel.clone()), state_typ.clone(), false),
        span,
    );
    let mut store_args: Vec<(LocExp, LocTyp)> = vec![(urlified, string_t.clone())];
    // The free variables shift by 1 because we are now inside a `let result = …`.
    for &v in &free {
        store_args.push((mk_exp(Exp::Rel(v + 1), span), string_t.clone()));
    }
    let store_name = format!("store{}", i);
    let store_call = mk_exp(Exp::FfiApp("Sqlcache".into(), store_name, store_args), span);

    // Sequence: store; result  (both evaluated, result returned)
    let store_then_result = mk_exp(Exp::Seq(Box::new(store_call), Box::new(result_rel)), span);

    // let result = <original query> in store; result
    let none_branch = mk_exp(
        Exp::Let(
            "result".into(),
            state_typ.clone(),
            Box::new(orig_query),
            Box::new(store_then_result),
        ),
        span,
    );

    // Some branch: decode the cached string back to the result type.
    // For now we use Uurlify in decode mode (third arg = true) on ERel 0
    // (the bound `s` from the Some pattern).
    let s_rel = mk_exp(Exp::Rel(0), span);
    let some_branch = mk_exp(Exp::Uurlify(Box::new(s_rel), state_typ.clone(), true), span);

    // case check{i}(keys…) of
    //   None   => none_branch
    // | Some s => some_branch
    let none_pat = Located::new(Pat::None(option_string_typ(span)), span.clone());
    let some_pat = Located::new(
        Pat::Some(
            string_t.clone(),
            Box::new(Located::new(
                Pat::Var("s".into(), string_t.clone()),
                span.clone(),
            )),
        ),
        span.clone(),
    );

    let case_meta = CaseMeta {
        disc: option_string_typ(span),
        result: state_typ,
    };

    Exp::Case(
        Box::new(check_call),
        vec![(none_pat, none_branch), (some_pat, some_branch)],
        case_meta,
    )
}

// ---------------------------------------------------------------------------
// Phase 2: add_flushing — prepend flush calls before DML operations
// ---------------------------------------------------------------------------

/// Build a flush call:
/// `Sqlcache.flush{i}(opt_key0, opt_key1, …)` where each key is
/// `Some(Rel(v))` (the current value of that free variable, lifted into
/// an option so the runtime can do partial cache invalidation).
fn make_flush_call(slot: &CacheSlot, span: &Span, depth: usize) -> LocExp {
    let string_t = string_typ(span);
    let opt_str_t = option_string_typ(span);

    let flush_args: Vec<(LocExp, LocTyp)> = slot
        .free_levels
        .iter()
        .map(|&v| {
            let rel = mk_exp(Exp::Rel(v + depth), span);
            let some_rel = mk_exp(Exp::Some(string_t.clone(), Box::new(rel)), span);
            (some_rel, opt_str_t.clone())
        })
        .collect();

    let flush_name = format!("flush{}", slot.index);
    mk_exp(Exp::FfiApp("Sqlcache".into(), flush_name, flush_args), span)
}

// ---------------------------------------------------------------------------
// Expression transformer (both phases combined in one traversal)
// ---------------------------------------------------------------------------

struct Transformer {
    caching: CachingState,
    /// After the caching pass, table→[slot_index] map is built here.
    table_to_caches: BTreeMap<String, Vec<usize>>,
    /// The slots collected during caching (populated after first pass).
    slots: Vec<CacheSlot>,
}

impl Transformer {
    fn new() -> Self {
        Transformer {
            caching: CachingState::new(),
            table_to_caches: BTreeMap::new(),
            slots: Vec::new(),
        }
    }

    fn build_table_map(&mut self) {
        for (idx, slot) in self.caching.slots.iter().enumerate() {
            for tbl in &slot.tables {
                self.table_to_caches
                    .entry(tbl.clone())
                    .or_default()
                    .push(slot.index);
            }
        }
        // Move slots out for later use.
        self.slots = std::mem::take(&mut self.caching.slots);
    }

    /// Phase 1: instrument query nodes with cache check/store.
    fn phase1_exp(&mut self, e: LocExp) -> LocExp {
        let span = e.span.clone();
        match e.node {
            Exp::Query(qm) => {
                let new_node = wrap_query_with_cache(&mut self.caching, qm, &span, 0);
                Located::new(new_node, span)
            }
            // Structural recursion for all other nodes.
            node => {
                let new_node = self.phase1_node(node, &span);
                Located::new(new_node, span)
            }
        }
    }

    fn phase1_node(&mut self, e: Exp, span: &Span) -> Exp {
        use Exp::*;
        macro_rules! p1 {
            ($e:expr) => {
                self.phase1_exp($e)
            };
        }
        match e {
            Prim(_) | Rel(_) | Named(_) | Ffi(_, _) | None(_) => e,
            Con(dk, pc, arg) => Con(dk, pc, arg.map(|a| Box::new(p1!(*a)))),
            Some(t, inner) => Some(t, Box::new(p1!(*inner))),
            FfiApp(m, x, args) => {
                FfiApp(m, x, args.into_iter().map(|(a, t)| (p1!(a), t)).collect())
            }
            App(e1, e2) => App(Box::new(p1!(*e1)), Box::new(p1!(*e2))),
            Abs(x, dom, ran, body) => Abs(x, dom, ran, Box::new(p1!(*body))),
            Unop(s, e1) => Unop(s, Box::new(p1!(*e1))),
            Binop(bi, s, e1, e2) => Binop(bi, s, Box::new(p1!(*e1)), Box::new(p1!(*e2))),
            Record(xets) => Record(xets.into_iter().map(|(x, e, t)| (x, p1!(e), t)).collect()),
            Field(e1, x) => Field(Box::new(p1!(*e1)), x),
            Case(disc, arms, meta) => {
                let disc2 = p1!(*disc);
                let arms2 = arms.into_iter().map(|(p, arm_e)| (p, p1!(arm_e))).collect();
                Case(Box::new(disc2), arms2, meta)
            }
            Strcat(e1, e2) => Strcat(Box::new(p1!(*e1)), Box::new(p1!(*e2))),
            Error(e1, t) => Error(Box::new(p1!(*e1)), t),
            ReturnBlob { blob, mime_type, t } => ReturnBlob {
                blob: blob.map(|b| Box::new(p1!(*b))),
                mime_type: Box::new(p1!(*mime_type)),
                t,
            },
            Redirect(e1, t) => Redirect(Box::new(p1!(*e1)), t),
            Write(e1) => Write(Box::new(p1!(*e1))),
            Seq(e1, e2) => Seq(Box::new(p1!(*e1)), Box::new(p1!(*e2))),
            Let(x, t, e1, e2) => Let(x, t, Box::new(p1!(*e1)), Box::new(p1!(*e2))),
            Closure(n, envs) => Closure(n, envs.into_iter().map(|a| p1!(a)).collect()),
            Query(qm) => {
                // This case is handled in phase1_exp; shouldn't reach here.

                wrap_query_with_cache(&mut self.caching, qm, span, 0)
            }
            Dml(e1, fm) => Dml(Box::new(p1!(*e1)), fm),
            Nextval(e1) => Nextval(Box::new(p1!(*e1))),
            Setval(e1, e2) => Setval(Box::new(p1!(*e1)), Box::new(p1!(*e2))),
            Uurlify(e1, t, b) => Uurlify(Box::new(p1!(*e1)), t, b),
            JavaScript(mode, e1) => JavaScript(mode, Box::new(p1!(*e1))),
            SignalReturn(e1) => SignalReturn(Box::new(p1!(*e1))),
            SignalBind(e1, e2) => SignalBind(Box::new(p1!(*e1)), Box::new(p1!(*e2))),
            SignalSource(e1) => SignalSource(Box::new(p1!(*e1))),
            ServerCall(e1, t, eff, fm) => ServerCall(Box::new(p1!(*e1)), t, eff, fm),
            Recv(e1, t) => Recv(Box::new(p1!(*e1)), t),
            Sleep(e1) => Sleep(Box::new(p1!(*e1))),
            Spawn(e1) => Spawn(Box::new(p1!(*e1))),
        }
    }

    /// Phase 2: prepend flush calls before DML operations.
    fn phase2_exp(&self, e: LocExp) -> LocExp {
        let span = e.span.clone();
        match e.node {
            Exp::Dml(dml_e, fm) => {
                // Find which tables this DML touches.
                let tables = dml_tables_from_exp(&dml_e);

                // Collect the slot indices that need flushing.
                let mut flush_indices: Vec<usize> = Vec::new();
                for tbl in &tables {
                    if let std::option::Option::Some(caches) = self.table_to_caches.get(tbl) {
                        for &ci in caches {
                            if !flush_indices.contains(&ci) {
                                flush_indices.push(ci);
                            }
                        }
                    }
                }

                // Build the (possibly) transformed DML expression.
                let dml_e2 = self.phase2_exp(*dml_e);
                let dml_node = Located::new(Exp::Dml(Box::new(dml_e2), fm), span.clone());

                if flush_indices.is_empty() {
                    return dml_node;
                }

                // Prepend flush calls: flush0; flush1; …; dml
                let slot_map: BTreeMap<usize, &CacheSlot> =
                    self.slots.iter().map(|s| (s.index, s)).collect();

                flush_indices.into_iter().rev().fold(dml_node, |acc, ci| {
                    if let std::option::Option::Some(slot) = slot_map.get(&ci) {
                        let flush = make_flush_call(slot, &span, 0);
                        mk_exp(Exp::Seq(Box::new(flush), Box::new(acc)), &span)
                    } else {
                        acc
                    }
                })
            }
            node => {
                let new_node = self.phase2_node(node, &span);
                Located::new(new_node, span)
            }
        }
    }

    fn phase2_node(&self, e: Exp, span: &Span) -> Exp {
        use Exp::*;
        macro_rules! p2 {
            ($e:expr) => {
                self.phase2_exp($e)
            };
        }
        match e {
            Prim(_) | Rel(_) | Named(_) | Ffi(_, _) | None(_) => e,
            Con(dk, pc, arg) => Con(dk, pc, arg.map(|a| Box::new(p2!(*a)))),
            Some(t, inner) => Some(t, Box::new(p2!(*inner))),
            FfiApp(m, x, args) => {
                FfiApp(m, x, args.into_iter().map(|(a, t)| (p2!(a), t)).collect())
            }
            App(e1, e2) => App(Box::new(p2!(*e1)), Box::new(p2!(*e2))),
            Abs(x, dom, ran, body) => Abs(x, dom, ran, Box::new(p2!(*body))),
            Unop(s, e1) => Unop(s, Box::new(p2!(*e1))),
            Binop(bi, s, e1, e2) => Binop(bi, s, Box::new(p2!(*e1)), Box::new(p2!(*e2))),
            Record(xets) => Record(xets.into_iter().map(|(x, e, t)| (x, p2!(e), t)).collect()),
            Field(e1, x) => Field(Box::new(p2!(*e1)), x),
            Case(disc, arms, meta) => {
                let disc2 = p2!(*disc);
                let arms2 = arms.into_iter().map(|(p, arm_e)| (p, p2!(arm_e))).collect();
                Case(Box::new(disc2), arms2, meta)
            }
            Strcat(e1, e2) => Strcat(Box::new(p2!(*e1)), Box::new(p2!(*e2))),
            Error(e1, t) => Error(Box::new(p2!(*e1)), t),
            ReturnBlob { blob, mime_type, t } => ReturnBlob {
                blob: blob.map(|b| Box::new(p2!(*b))),
                mime_type: Box::new(p2!(*mime_type)),
                t,
            },
            Redirect(e1, t) => Redirect(Box::new(p2!(*e1)), t),
            Write(e1) => Write(Box::new(p2!(*e1))),
            Seq(e1, e2) => Seq(Box::new(p2!(*e1)), Box::new(p2!(*e2))),
            Let(x, t, e1, e2) => Let(x, t, Box::new(p2!(*e1)), Box::new(p2!(*e2))),
            Closure(n, envs) => Closure(n, envs.into_iter().map(|a| p2!(a)).collect()),
            Query(qm) => Query(QueryMeta {
                query: Box::new(p2!(*qm.query)),
                body: Box::new(p2!(*qm.body)),
                initial: Box::new(p2!(*qm.initial)),
                ..qm
            }),
            Dml(e1, fm) => {
                // Should have been handled by phase2_exp — recurse into inner.
                Dml(Box::new(p2!(*e1)), fm)
            }
            Nextval(e1) => Nextval(Box::new(p2!(*e1))),
            Setval(e1, e2) => Setval(Box::new(p2!(*e1)), Box::new(p2!(*e2))),
            Uurlify(e1, t, b) => Uurlify(Box::new(p2!(*e1)), t, b),
            JavaScript(mode, e1) => JavaScript(mode, Box::new(p2!(*e1))),
            SignalReturn(e1) => SignalReturn(Box::new(p2!(*e1))),
            SignalBind(e1, e2) => SignalBind(Box::new(p2!(*e1)), Box::new(p2!(*e2))),
            SignalSource(e1) => SignalSource(Box::new(p2!(*e1))),
            ServerCall(e1, t, eff, fm) => ServerCall(Box::new(p2!(*e1)), t, eff, fm),
            Recv(e1, t) => Recv(Box::new(p2!(*e1)), t),
            Sleep(e1) => Sleep(Box::new(p2!(*e1))),
            Spawn(e1) => Spawn(Box::new(p2!(*e1))),
        }
    }
}

// ---------------------------------------------------------------------------
// Declaration-level transformation helpers
// ---------------------------------------------------------------------------

fn phase1_decl(state: &mut CachingState, d: LocDecl) -> LocDecl {
    let span = d.span.clone();
    let new_node = phase1_decl_node(state, d.node, &span);
    Located::new(new_node, span)
}

fn phase1_decl_node(state: &mut CachingState, d: Decl, span: &Span) -> Decl {
    // We need a local helper that owns `state` via a mutable reference.
    // Temporarily build a thin shim.
    struct Ph1<'a>(&'a mut CachingState);
    impl<'a> Ph1<'a> {
        fn exp(&mut self, e: LocExp) -> LocExp {
            let span = e.span.clone();
            match e.node {
                Exp::Query(qm) => {
                    let new_node = wrap_query_with_cache(self.0, qm, &span, 0);
                    Located::new(new_node, span)
                }
                node => {
                    let new_node = self.node(node, &span);
                    Located::new(new_node, span)
                }
            }
        }

        fn node(&mut self, e: Exp, span: &Span) -> Exp {
            use Exp::*;
            macro_rules! p {
                ($e:expr) => {
                    self.exp($e)
                };
            }
            match e {
                Prim(_) | Rel(_) | Named(_) | Ffi(_, _) | None(_) => e,
                Con(dk, pc, arg) => Con(dk, pc, arg.map(|a| Box::new(p!(*a)))),
                Some(t, inner) => Some(t, Box::new(p!(*inner))),
                FfiApp(m, x, args) => {
                    FfiApp(m, x, args.into_iter().map(|(a, t)| (p!(a), t)).collect())
                }
                App(e1, e2) => App(Box::new(p!(*e1)), Box::new(p!(*e2))),
                Abs(x, dom, ran, body) => Abs(x, dom, ran, Box::new(p!(*body))),
                Unop(s, e1) => Unop(s, Box::new(p!(*e1))),
                Binop(bi, s, e1, e2) => Binop(bi, s, Box::new(p!(*e1)), Box::new(p!(*e2))),
                Record(xets) => Record(xets.into_iter().map(|(x, e, t)| (x, p!(e), t)).collect()),
                Field(e1, x) => Field(Box::new(p!(*e1)), x),
                Case(disc, arms, meta) => {
                    let disc2 = p!(*disc);
                    let arms2 = arms
                        .into_iter()
                        .map(|(p, arm_e)| (p, self.exp(arm_e)))
                        .collect();
                    Case(Box::new(disc2), arms2, meta)
                }
                Strcat(e1, e2) => Strcat(Box::new(p!(*e1)), Box::new(p!(*e2))),
                Error(e1, t) => Error(Box::new(p!(*e1)), t),
                ReturnBlob { blob, mime_type, t } => ReturnBlob {
                    blob: blob.map(|b| Box::new(p!(*b))),
                    mime_type: Box::new(p!(*mime_type)),
                    t,
                },
                Redirect(e1, t) => Redirect(Box::new(p!(*e1)), t),
                Write(e1) => Write(Box::new(p!(*e1))),
                Seq(e1, e2) => Seq(Box::new(p!(*e1)), Box::new(p!(*e2))),
                Let(x, t, e1, e2) => Let(x, t, Box::new(p!(*e1)), Box::new(p!(*e2))),
                Closure(n, envs) => Closure(n, envs.into_iter().map(|a| p!(a)).collect()),
                Query(qm) => wrap_query_with_cache(self.0, qm, span, 0),
                Dml(e1, fm) => Dml(Box::new(p!(*e1)), fm),
                Nextval(e1) => Nextval(Box::new(p!(*e1))),
                Setval(e1, e2) => Setval(Box::new(p!(*e1)), Box::new(p!(*e2))),
                Uurlify(e1, t, b) => Uurlify(Box::new(p!(*e1)), t, b),
                JavaScript(mode, e1) => JavaScript(mode, Box::new(p!(*e1))),
                SignalReturn(e1) => SignalReturn(Box::new(p!(*e1))),
                SignalBind(e1, e2) => SignalBind(Box::new(p!(*e1)), Box::new(p!(*e2))),
                SignalSource(e1) => SignalSource(Box::new(p!(*e1))),
                ServerCall(e1, t, eff, fm) => ServerCall(Box::new(p!(*e1)), t, eff, fm),
                Recv(e1, t) => Recv(Box::new(p!(*e1)), t),
                Sleep(e1) => Sleep(Box::new(p!(*e1))),
                Spawn(e1) => Spawn(Box::new(p!(*e1))),
            }
        }
    }

    let mut ph = Ph1(state);
    match d {
        Decl::Val(x, n, t, e, s) => Decl::Val(x, n, t, ph.exp(e), s),
        Decl::ValRec(vis) => Decl::ValRec(
            vis.into_iter()
                .map(|(x, n, t, e, s)| (x, n, t, ph.exp(e), s))
                .collect(),
        ),
        Decl::Table(nm, xts, pe, ce) => Decl::Table(nm, xts, ph.exp(pe), ph.exp(ce)),
        Decl::Task(e1, e2) => Decl::Task(ph.exp(e1), ph.exp(e2)),
        Decl::Policy(pol) => {
            use crate::monomorphized::Policy;
            let pol2 = match pol {
                Policy::Client(e) => Policy::Client(ph.exp(e)),
                Policy::Insert(e) => Policy::Insert(ph.exp(e)),
                Policy::Delete(e) => Policy::Delete(ph.exp(e)),
                Policy::Update(e) => Policy::Update(ph.exp(e)),
                Policy::Sequence(e) => Policy::Sequence(ph.exp(e)),
            };
            Decl::Policy(pol2)
        }
        other => other,
    }
}

fn phase2_decl(xfm: &Transformer, d: LocDecl) -> LocDecl {
    let span = d.span.clone();
    let new_node = phase2_decl_node(xfm, d.node, &span);
    Located::new(new_node, span)
}

fn phase2_decl_node(xfm: &Transformer, d: Decl, span: &Span) -> Decl {
    match d {
        Decl::Val(x, n, t, e, s) => Decl::Val(x, n, t, xfm.phase2_exp(e), s),
        Decl::ValRec(vis) => Decl::ValRec(
            vis.into_iter()
                .map(|(x, n, t, e, s)| (x, n, t, xfm.phase2_exp(e), s))
                .collect(),
        ),
        Decl::Table(nm, xts, pe, ce) => {
            Decl::Table(nm, xts, xfm.phase2_exp(pe), xfm.phase2_exp(ce))
        }
        Decl::Task(e1, e2) => Decl::Task(xfm.phase2_exp(e1), xfm.phase2_exp(e2)),
        Decl::Policy(pol) => {
            use crate::monomorphized::Policy;
            let pol2 = match pol {
                Policy::Client(e) => Policy::Client(xfm.phase2_exp(e)),
                Policy::Insert(e) => Policy::Insert(xfm.phase2_exp(e)),
                Policy::Delete(e) => Policy::Delete(xfm.phase2_exp(e)),
                Policy::Update(e) => Policy::Update(xfm.phase2_exp(e)),
                Policy::Sequence(e) => Policy::Sequence(xfm.phase2_exp(e)),
            };
            Decl::Policy(pol2)
        }
        other => other,
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// SQL cache instrumentation pass.
///
/// When `settings.sqlcache` is `false` this is a no-op.
///
/// When `true`, each `Exp::Query` is wrapped with a check/store pair and each
/// `Exp::Dml` is preceded by flush calls for any caches that read from the
/// affected tables.
pub fn go(file: File, settings: &Settings) -> File {
    if !settings.sqlcache {
        return file;
    }

    let (decls, exports) = file;

    // Phase 1: instrument queries.
    let mut cache_state = CachingState::new();
    let decls: Vec<LocDecl> = decls
        .into_iter()
        .map(|d| phase1_decl(&mut cache_state, d))
        .collect();

    // Build table→cache index map from accumulated slots.
    let mut table_to_caches: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for slot in &cache_state.slots {
        for tbl in &slot.tables {
            table_to_caches
                .entry(tbl.clone())
                .or_default()
                .push(slot.index);
        }
    }
    let slots = cache_state.slots;

    // Phase 2: instrument DML with flushes.
    let xfm = Transformer {
        caching: CachingState::new(), // unused in phase 2
        table_to_caches,
        slots,
    };

    let decls: Vec<LocDecl> = decls.into_iter().map(|d| phase2_decl(&xfm, d)).collect();

    (decls, exports)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error_types::Located;
    use crate::monomorphized::{Decl, Exp, File, QueryMeta, Typ};
    use crate::settings::Settings;

    fn dummy_typ() -> LocTyp {
        Located::dummy(Typ::Record(vec![]))
    }

    fn dummy_exp() -> LocExp {
        Located::dummy(Exp::Record(vec![]))
    }

    fn make_query_exp(table: &str) -> LocExp {
        Located::dummy(Exp::Query(QueryMeta {
            exps: vec![],
            tables: vec![(table.to_string(), vec![])],
            state: dummy_typ(),
            query: Box::new(dummy_exp()),
            body: Box::new(dummy_exp()),
            initial: Box::new(dummy_exp()),
        }))
    }

    #[test]
    fn go_passthrough_when_sqlcache_false() {
        let file: File = (
            vec![Located::dummy(Decl::Val(
                "f".into(),
                1,
                dummy_typ(),
                make_query_exp("t1"),
                "f".into(),
            ))],
            vec![],
        );
        let settings = Settings::default();
        assert!(
            !settings.sqlcache,
            "default settings must have sqlcache=false"
        );
        let result = go(file.clone(), &settings);
        // With sqlcache=false, file returned unchanged (same structure).
        assert_eq!(result.0.len(), 1);
        assert!(matches!(result.0[0].node, Decl::Val(..)));
    }

    #[test]
    fn go_empty_file_no_panic() {
        let file: File = (vec![], vec![]);
        let settings = Settings {
            sqlcache: true,
            ..Default::default()
        };
        let result = go(file, &settings);
        assert!(result.0.is_empty());
    }

    #[test]
    fn go_query_wrapped_in_case() {
        // After go(), the Val expression should be a Case (check/store wrapper).
        let file: File = (
            vec![Located::dummy(Decl::Val(
                "f".into(),
                1,
                dummy_typ(),
                make_query_exp("t1"),
                "f".into(),
            ))],
            vec![],
        );
        let settings = Settings {
            sqlcache: true,
            ..Default::default()
        };
        let result = go(file, &settings);
        assert_eq!(result.0.len(), 1);
        match &result.0[0].node {
            Decl::Val(_, _, _, e, _) => {
                assert!(
                    matches!(e.node, Exp::Case(..)),
                    "query must be wrapped in Case node after sqlcache pass"
                );
            }
            other => panic!("expected Val, got {:?}", other),
        }
    }

    #[test]
    fn extract_dml_table_insert() {
        assert_eq!(
            extract_dml_table("INSERT INTO my_table (x) VALUES (1)"),
            std::option::Option::Some("my_table".to_string())
        );
    }

    #[test]
    fn extract_dml_table_delete() {
        assert_eq!(
            extract_dml_table("DELETE FROM users WHERE id = 1"),
            std::option::Option::Some("users".to_string())
        );
    }

    #[test]
    fn extract_dml_table_update() {
        assert_eq!(
            extract_dml_table("UPDATE orders SET status = 'done'"),
            std::option::Option::Some("orders".to_string())
        );
    }

    #[test]
    fn extract_dml_table_none() {
        assert_eq!(
            extract_dml_table("SELECT * FROM t"),
            std::option::Option::None
        );
    }

    #[test]
    fn go_dml_preceded_by_flush_for_matching_table() {
        use crate::primitives::{Prim, StringMode};
        // A file with a Query over "t1" and a DML on "t1".
        let dml_str = Located::dummy(Exp::Prim(Prim::String(
            StringMode::Normal,
            "INSERT INTO t1 (x) VALUES (1)".into(),
        )));
        let dml_exp = Located::dummy(Exp::Dml(
            Box::new(dml_str),
            crate::settings::FailureMode::Error,
        ));
        let file: File = (
            vec![
                Located::dummy(Decl::Val(
                    "q".into(),
                    1,
                    dummy_typ(),
                    make_query_exp("t1"),
                    "q".into(),
                )),
                Located::dummy(Decl::Val("d".into(), 2, dummy_typ(), dml_exp, "d".into())),
            ],
            vec![],
        );
        let settings = Settings {
            sqlcache: true,
            ..Default::default()
        };
        let result = go(file, &settings);
        // The second decl should now start with a Seq (flush; dml).
        match &result.0[1].node {
            Decl::Val(_, _, _, e, _) => {
                assert!(
                    matches!(e.node, Exp::Seq(..)),
                    "DML on cached table must be preceded by flush (Seq node)"
                );
            }
            other => panic!("expected Val, got {:?}", other),
        }
    }
}
