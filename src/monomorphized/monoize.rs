//! Monoize pass: Core → Mono conversion.
//!
//! Eliminates polymorphism by specializing every polymorphic function and
//! datatype at its call sites. Translates Core types/expressions/declarations
//! to their Mono counterparts.
//!
//! Mirrors `monoize.sml`.

use std::collections::{HashMap, HashSet, VecDeque};
use std::fs;
use std::sync::{Arc, Mutex, OnceLock};

use crate::core::{
    self, Constructor as CC, Declaration as CD, Expression as CE, LocatedConstructor,
    LocatedDeclaration, LocatedExpression, LocatedPattern, Pattern as CP,
    PatternConstructor as CPC,
};
use crate::datatype_kind::DatatypeKind;
use crate::db::DatabaseBackend;
use crate::error_types::{Located, Span};
use crate::monomorphized::utilities::classify_datatype as classify_datatype_mono;
use crate::monomorphized::{
    self as mono, BinopIntness, CaseMeta, DatatypeDecl as MonoDatatypeDecl, DatatypeDef,
    DatatypeRef, Decl, Exp, JavaScriptMode, LocDecl, LocExp, LocPat, LocTyp, Pat, PatCon, Policy,
    Typ,
};
use crate::primitives::Prim;
use crate::settings::{FailureMode, Settings};

// ---------------------------------------------------------------------------
// Environment for monoize (includes de Bruijn expression stack)
// ---------------------------------------------------------------------------

/// The type environment threaded through monoize.
///
/// Tracks both named (global) and relative (de Bruijn) value bindings,
/// so that we can look up types of Core expressions during translation.
#[derive(Clone)]
struct Env {
    /// De Bruijn expression variable types (innermost first).
    rel_e: Vec<LocatedConstructor>,
    /// Named values: id → (name, type, source_path).
    named_e: HashMap<usize, (String, LocatedConstructor, String)>,
    /// Datatypes: id → (name, type_params, constructors).
    datatypes: HashMap<
        usize,
        (
            String,
            Vec<String>,
            Vec<(String, usize, Option<LocatedConstructor>)>,
        ),
    >,
    /// Named constructors: id → optional definition.
    named_c: HashMap<usize, Option<LocatedConstructor>>,
}

impl Env {
    fn empty() -> Self {
        Env {
            rel_e: Vec::new(),
            named_e: HashMap::new(),
            datatypes: HashMap::new(),
            named_c: HashMap::new(),
        }
    }

    fn push_e_rel(mut self, typ: LocatedConstructor) -> Self {
        self.rel_e.push(typ);
        self
    }

    fn push_e_named(
        mut self,
        name: String,
        id: usize,
        typ: LocatedConstructor,
        src: String,
    ) -> Self {
        self.named_e.insert(id, (name, typ, src));
        self
    }

    fn lookup_e_named(&self, id: usize) -> Option<&(String, LocatedConstructor, String)> {
        self.named_e.get(&id)
    }

    fn push_datatype(
        mut self,
        id: usize,
        name: String,
        params: Vec<String>,
        constrs: Vec<(String, usize, Option<LocatedConstructor>)>,
    ) -> Self {
        self.datatypes.insert(id, (name, params, constrs));
        self
    }

    fn lookup_datatype(
        &self,
        id: usize,
    ) -> Option<&(
        String,
        Vec<String>,
        Vec<(String, usize, Option<LocatedConstructor>)>,
    )> {
        self.datatypes.get(&id)
    }

    fn push_c_named(mut self, id: usize, def: Option<LocatedConstructor>) -> Self {
        self.named_c.insert(id, def);
        self
    }

    /// Extend the environment with all bindings introduced by a Core declaration.
    fn decl_binds(self, decl: &LocatedDeclaration) -> Self {
        let loc = decl.span.clone();
        match &decl.node {
            CD::Constructor(_, id, _, c) => self.push_c_named(*id, Some(c.clone())),
            CD::Datatype(dts) => dts.iter().fold(self, |env, dt| {
                let env = env.push_datatype(
                    dt.id,
                    dt.name.clone(),
                    dt.params.clone(),
                    dt.constrs.clone(),
                );
                env.push_c_named(dt.id, None)
            }),
            CD::Val(x, n, t, _, s) => self.push_e_named(x.clone(), *n, t.clone(), s.clone()),
            CD::ValRec(vis) => vis.iter().fold(self, |env, (x, n, t, _, s)| {
                env.push_e_named(x.clone(), *n, t.clone(), s.clone())
            }),
            CD::Export(_, _, _) => self,
            CD::Table { sql_name, id, .. } => {
                // Table value type: Basis.string
                let t = Located::new(CC::Ffi("Basis".into(), "string".into()), loc.clone());
                self.push_e_named(sql_name.clone(), *id, t, sql_name.clone())
            }
            CD::Sequence(x, n, s) => {
                let t = Located::new(CC::Ffi("Basis".into(), "sql_sequence".into()), loc.clone());
                self.push_e_named(x.clone(), *n, t, s.clone())
            }
            CD::View(x, n, s, _, _) => {
                let t = Located::new(CC::Ffi("Basis".into(), "sql_view".into()), loc.clone());
                self.push_e_named(x.clone(), *n, t, s.clone())
            }
            CD::Cookie(x, n, _, s) => {
                let t = Located::new(CC::Ffi("Basis".into(), "string".into()), loc.clone());
                self.push_e_named(x.clone(), *n, t, s.clone())
            }
            CD::Style(x, n, s) => {
                let t = Located::new(CC::Ffi("Basis".into(), "string".into()), loc.clone());
                self.push_e_named(x.clone(), *n, t, s.clone())
            }
            CD::Index(_, _) | CD::Database(_) | CD::Task(_, _) | CD::Policy(_) | CD::OnError(_) => {
                self
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Fm: function-map for generated helper functions (MonoFooify.Fm)
// ---------------------------------------------------------------------------

/// A record for one generated helper function (DValRec entry).
type FmDecl = (String, usize, LocTyp, LocExp, String);

type QueryCacheKey = (String, usize);

#[derive(Clone)]
struct QueryCacheEntry {
    query: LocExp,
    signature: String,
}

fn query_cache_key(span: &Span) -> QueryCacheKey {
    (span.file.clone(), span.first.line as usize)
}

fn query_row_signature(mut exps: Vec<String>, mut tables: Vec<(String, Vec<String>)>) -> String {
    exps.sort();
    tables.sort_by(|(left, _), (right, _)| left.cmp(right));
    let table_sig = tables
        .into_iter()
        .map(|(table, mut fields)| {
            fields.sort();
            format!("{table}({})", fields.join(","))
        })
        .collect::<Vec<_>>()
        .join(";");
    format!("E[{}]|T[{table_sig}]", exps.join(","))
}

fn query_row_signature_from_mono(
    exps: &[(String, LocTyp)],
    tables: &[(String, Vec<(String, LocTyp)>)],
) -> String {
    query_row_signature(
        exps.iter().map(|(name, _)| name.clone()).collect(),
        tables
            .iter()
            .map(|(table, fields)| {
                (
                    table.clone(),
                    fields.iter().map(|(name, _)| name.clone()).collect(),
                )
            })
            .collect(),
    )
}

fn sql_query_cache() -> &'static Mutex<HashMap<QueryCacheKey, QueryCacheEntry>> {
    static CACHE: OnceLock<Mutex<HashMap<QueryCacheKey, QueryCacheEntry>>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(HashMap::new()))
}

fn queued_sql_queries() -> &'static Mutex<VecDeque<QueryCacheEntry>> {
    static QUEUE: OnceLock<Mutex<VecDeque<QueryCacheEntry>>> = OnceLock::new();
    QUEUE.get_or_init(|| Mutex::new(VecDeque::new()))
}

fn reset_monoize_caches() {
    if let Ok(mut cache) = sql_query_cache().lock() {
        cache.clear();
    }
    if let Ok(mut queue) = queued_sql_queries().lock() {
        queue.clear();
    }
}

/// Simplified version of MonoFooify.Fm.
///
/// Accumulates lazily-generated helper functions (for URL/attribute encoding
/// of polymorphic types). Each call to monoExp may extend the Fm.
#[derive(Clone)]
struct Fm {
    count: usize,
    decls: Vec<FmDecl>,
}

impl Fm {
    fn empty(start: usize) -> Self {
        Fm {
            count: start,
            decls: Vec::new(),
        }
    }

    /// Allocate a fresh function id.
    fn fresh_name(&mut self) -> usize {
        let n = self.count;
        self.count += 1;
        n
    }

    /// Drain accumulated declarations as a single DValRec (if any), resetting the list.
    fn drain_decls(&mut self, loc: &Span) -> Vec<LocDecl> {
        if self.decls.is_empty() {
            Vec::new()
        } else {
            let ds = std::mem::take(&mut self.decls);
            vec![Located::new(Decl::ValRec(ds), loc.clone())]
        }
    }
}

// ---------------------------------------------------------------------------
// Name extraction
// ---------------------------------------------------------------------------

/// Extract a string field name from a Core constructor (should be CName s).
fn mono_name(con: &LocatedConstructor) -> String {
    match &con.node {
        CC::Name(s) => s.clone(),
        _ => "?".to_string(),
    }
}

fn expand_named_constructor_inner(
    env: &Env,
    con: LocatedConstructor,
    visiting: &mut HashSet<usize>,
) -> LocatedConstructor {
    let span = con.span.clone();
    let expanded = match con.node {
        CC::Named(n) => {
            let Some(Some(def)) = env.named_c.get(&n) else {
                return Located::new(CC::Named(n), span);
            };
            if !visiting.insert(n) {
                return Located::new(CC::Named(n), span);
            }
            let expanded = expand_named_constructor_inner(env, def.clone(), visiting);
            visiting.remove(&n);
            expanded
        }
        CC::TFun(left, right) => Located::new(
            CC::TFun(
                Box::new(expand_named_constructor_inner(env, *left, visiting)),
                Box::new(expand_named_constructor_inner(env, *right, visiting)),
            ),
            span,
        ),
        CC::TCFun(name, kind, body) => Located::new(
            CC::TCFun(
                name,
                kind,
                Box::new(expand_named_constructor_inner(env, *body, visiting)),
            ),
            span,
        ),
        CC::TRecord(inner) => Located::new(
            CC::TRecord(Box::new(expand_named_constructor_inner(
                env, *inner, visiting,
            ))),
            span,
        ),
        CC::App(function, argument) => Located::new(
            CC::App(
                Box::new(expand_named_constructor_inner(env, *function, visiting)),
                Box::new(expand_named_constructor_inner(env, *argument, visiting)),
            ),
            span,
        ),
        CC::Abs(name, kind, body) => Located::new(
            CC::Abs(
                name,
                kind,
                Box::new(expand_named_constructor_inner(env, *body, visiting)),
            ),
            span,
        ),
        CC::KAbs(name, body) => Located::new(
            CC::KAbs(
                name,
                Box::new(expand_named_constructor_inner(env, *body, visiting)),
            ),
            span,
        ),
        CC::KApp(constructor, kind) => Located::new(
            CC::KApp(
                Box::new(expand_named_constructor_inner(env, *constructor, visiting)),
                kind,
            ),
            span,
        ),
        CC::TKFun(name, body) => Located::new(
            CC::TKFun(
                name,
                Box::new(expand_named_constructor_inner(env, *body, visiting)),
            ),
            span,
        ),
        CC::Record(kind, fields) => Located::new(
            CC::Record(
                kind,
                fields
                    .into_iter()
                    .map(|(name, value)| {
                        (
                            expand_named_constructor_inner(env, name, visiting),
                            expand_named_constructor_inner(env, value, visiting),
                        )
                    })
                    .collect(),
            ),
            span,
        ),
        CC::Concat(left, right) => Located::new(
            CC::Concat(
                Box::new(expand_named_constructor_inner(env, *left, visiting)),
                Box::new(expand_named_constructor_inner(env, *right, visiting)),
            ),
            span,
        ),
        CC::Tuple(items) => Located::new(
            CC::Tuple(
                items
                    .into_iter()
                    .map(|item| expand_named_constructor_inner(env, item, visiting))
                    .collect(),
            ),
            span,
        ),
        CC::Proj(inner, index) => Located::new(
            CC::Proj(
                Box::new(expand_named_constructor_inner(env, *inner, visiting)),
                index,
            ),
            span,
        ),
        other => Located::new(other, span),
    };
    crate::core::local_reduction::reduce_con(expanded)
}

fn normalize_constructor_for_mono(env: &Env, con: &LocatedConstructor) -> LocatedConstructor {
    let mut visiting = HashSet::new();
    expand_named_constructor_inner(env, con.clone(), &mut visiting)
}

// ---------------------------------------------------------------------------
// Type translation: mono_type
// ---------------------------------------------------------------------------

/// Compute the head function and all arguments of a nested App chain.
///
/// Returns (head, args) where args[0] is the first applied argument.
fn strip_apps<'a>(
    con: &'a core::Constructor,
    args: &mut Vec<&'a LocatedConstructor>,
) -> &'a core::Constructor {
    match con {
        CC::App(f, arg) => {
            // We collect in reverse; caller must reverse.
            args.push(arg.as_ref());
            strip_apps(&f.node, args)
        }
        other => other,
    }
}

/// Translate a Core constructor (type) to a Mono type.
///
/// `dtmap` prevents infinite loops when translating recursive datatypes.
///
/// Mirrors `monoType` in `monoize.sml`.
fn mono_type(
    env: &Env,
    dtmap: &mut HashMap<usize, DatatypeRef>,
    con: &LocatedConstructor,
) -> LocTyp {
    let normalized = normalize_constructor_for_mono(env, con);
    let loc = normalized.span.clone();
    use CC::*;
    match &normalized.node {
        // TFun → Mono.TFun
        TFun(c1, c2) => Located::new(
            Typ::Fun(
                Box::new(mono_type(env, dtmap, c1)),
                Box::new(mono_type(env, dtmap, c2)),
            ),
            loc,
        ),

        // Polymorphic TFun — error (shouldn't appear after monomorphisation)
        TCFun(_, _, _) => dummy_typ(&loc),

        // TRecord: rows of kind KType → Mono.TRecord
        TRecord(row) => mono_type_row(env, dtmap, row, &loc),

        // Some reduced nested record types arrive as bare Record(Type, ...),
        // rather than TRecord(Record(...)). Preserve their fields instead of
        // collapsing them to unit.
        Record(kind, _) if matches!(kind.node, crate::core::Kind::Type) => {
            mono_type_row(env, dtmap, &normalized, &loc)
        }

        // Named datatype application
        Named(n) => {
            if let Some(r) = dtmap.get(n) {
                return Located::new(Typ::Datatype(*n, r.clone()), loc);
            }
            let r: DatatypeRef = Arc::new(Mutex::new(DatatypeDef {
                kind: DatatypeKind::Default,
                constrs: Vec::new(),
            }));
            dtmap.insert(*n, r.clone());
            if let Some((_, xs, xncs)) = env.lookup_datatype(*n) {
                if xs.is_empty() {
                    let constrs: Vec<_> = xncs
                        .iter()
                        .map(|(x, cn, to)| {
                            (
                                x.clone(),
                                *cn,
                                to.as_ref().map(|t| mono_type(env, dtmap, t)),
                            )
                        })
                        .collect();
                    let kind = classify_datatype_mono(&constrs);
                    *crate::compiler_diagnostics::lock_for_compile(
                        r.as_ref(),
                        "monoize datatype unification cell",
                    ) = DatatypeDef { kind, constrs };
                }
            }
            Located::new(Typ::Datatype(*n, r), loc)
        }

        // FFI types
        Ffi(m, x) => mono_type_ffi(m, x, &loc),

        // App chain: peel off all arguments, check head
        App(function, argument) => {
            if let App(map_fn, mapper) = &function.node {
                if let Map(domain_kind, range_kind) = &map_fn.node {
                    if matches!(range_kind.node, crate::core::Kind::Type)
                        && matches!(
                            domain_kind.node,
                            crate::core::Kind::Record(ref inner)
                                if matches!(inner.node, crate::core::Kind::Type)
                        )
                        && matches!(
                            mapper.node,
                            Abs(_, ref mapper_kind, ref body)
                                if matches!(
                                    mapper_kind.node,
                                    crate::core::Kind::Record(ref inner)
                                        if matches!(inner.node, crate::core::Kind::Type)
                                ) && matches!(
                                    body.node,
                                    TRecord(ref row) if matches!(row.node, Rel(0))
                                )
                        )
                    {
                        return mono_type(env, dtmap, argument);
                    }
                }
            }
            let mut args = Vec::new();
            let head = strip_apps(&normalized.node, &mut args);
            args.reverse(); // args[0] = first applied
            mono_type_app(env, dtmap, head, &args, &loc)
        }

        // Anything else is a poly error (Rel, Name, Record, Concat, etc.)
        _ => dummy_typ(&loc),
    }
}

/// Translate a record row constructor to Mono.TRecord.
fn mono_type_row(
    env: &Env,
    dtmap: &mut HashMap<usize, DatatypeRef>,
    row: &LocatedConstructor,
    loc: &Span,
) -> LocTyp {
    let mut xcs = mono_row_fields(env, dtmap, row).unwrap_or_default();
    xcs.sort_by(|(a, _), (b, _)| a.cmp(b));
    Located::new(Typ::Record(xcs), loc.clone())
}

fn mono_row_fields(
    env: &Env,
    dtmap: &mut HashMap<usize, DatatypeRef>,
    row: &LocatedConstructor,
) -> Option<Vec<(String, LocTyp)>> {
    let normalized = normalize_constructor_for_mono(env, row);
    mono_row_fields_normalized(env, dtmap, &normalized)
}

fn mono_row_fields_normalized(
    env: &Env,
    dtmap: &mut HashMap<usize, DatatypeRef>,
    row: &LocatedConstructor,
) -> Option<Vec<(String, LocTyp)>> {
    match &row.node {
        CC::Record(_, fields) => Some(
            fields
                .iter()
                .map(|(name_con, t)| (mono_name(name_con), mono_type(env, dtmap, t)))
                .collect(),
        ),
        CC::Concat(left, right) => {
            let mut fields = mono_row_fields_normalized(env, dtmap, left)?;
            fields.extend(mono_row_fields_normalized(env, dtmap, right)?);
            Some(fields)
        }
        CC::Unit => Some(Vec::new()),
        _ => None,
    }
}

fn mono_project_row_parts(
    record_exp: &LocExp,
    row_fields: &[(String, LocTyp)],
    loc: &Span,
) -> Vec<(String, LocExp, LocTyp)> {
    row_fields
        .iter()
        .map(|(name, typ)| {
            (
                name.clone(),
                Located::new(
                    Exp::Field(Box::new(record_exp.clone()), name.clone()),
                    loc.clone(),
                ),
                typ.clone(),
            )
        })
        .collect()
}

fn mono_record_fields_from_type(
    env: &Env,
    dtmap: &mut HashMap<usize, DatatypeRef>,
    typ: &LocatedConstructor,
) -> Option<Vec<(String, LocTyp)>> {
    match mono_type(env, dtmap, typ).node {
        Typ::Record(fields) => Some(fields),
        _ => None,
    }
}

fn mono_record_fields_from_exp_type(
    env: &Env,
    dtmap: &mut HashMap<usize, DatatypeRef>,
    exp: &LocatedExpression,
) -> Option<Vec<(String, LocTyp)>> {
    match &exp.node {
        CE::Rel(n) => env
            .rel_e
            .get(env.rel_e.len().checked_sub(n + 1)?)
            .and_then(|typ| mono_record_fields_from_type(env, dtmap, typ)),
        CE::Named(n) => env
            .lookup_e_named(*n)
            .and_then(|(_, typ, _)| mono_record_fields_from_type(env, dtmap, typ)),
        _ => None,
    }
}

/// Translate a bare FFI type name to a Mono type.
fn mono_type_ffi(m: &str, x: &str, loc: &Span) -> LocTyp {
    if m != "Basis" {
        return Located::new(Typ::Ffi(m.to_string(), x.to_string()), loc.clone());
    }
    match x {
        "unit" => Located::new(Typ::Record(Vec::new()), loc.clone()),
        // Types that become Basis.string
        "page" | "xhead" | "xbody" | "xtable" | "xtr" | "xform" | "url" | "mimeType"
        | "css_class" | "css_value" | "css_property" | "css_style" | "id" | "requestHeader"
        | "responseHeader" | "envVar" | "meta" | "data_attr_kind" | "data_attr" | "dml"
        | "sql_sequence" | "sql_relop" | "sql_direction" | "sql_limit" | "sql_offset" => {
            Located::new(
                Typ::Ffi("Basis".to_string(), "string".to_string()),
                loc.clone(),
            )
        }
        _ => Located::new(Typ::Ffi(m.to_string(), x.to_string()), loc.clone()),
    }
}

/// Translate a type-application chain (head applied to args) to a Mono type.
fn mono_type_app(
    env: &Env,
    dtmap: &mut HashMap<usize, DatatypeRef>,
    head: &core::Constructor,
    args: &[&LocatedConstructor],
    loc: &Span,
) -> LocTyp {
    let last = args.last();
    match head {
        CC::Ffi(m, x) if m == "Basis" => {
            let string_t = || {
                Located::new(
                    Typ::Ffi("Basis".to_string(), "string".to_string()),
                    loc.clone(),
                )
            };
            let unit_t = || Located::new(Typ::Record(Vec::new()), loc.clone());
            match x.as_str() {
                "option" => {
                    let inner = last
                        .map(|t| mono_type(env, dtmap, t))
                        .unwrap_or(dummy_typ(loc));
                    Located::new(Typ::Option(Box::new(inner)), loc.clone())
                }
                "list" => {
                    let inner = last
                        .map(|t| mono_type(env, dtmap, t))
                        .unwrap_or(dummy_typ(loc));
                    Located::new(Typ::List(Box::new(inner)), loc.clone())
                }
                "transaction" => {
                    // Map Basis.transaction applied to its result type to the
                    // dedicated Typ::Transaction variant so the mono pipeline can
                    // reason about error-bearing computations structurally.
                    let inner = last
                        .map(|t| mono_type(env, dtmap, t))
                        .unwrap_or(dummy_typ(loc));
                    Located::new(Typ::Transaction(Box::new(inner)), loc.clone())
                }
                "source" => Located::new(Typ::Source, loc.clone()),
                "signal" => {
                    let inner = last
                        .map(|t| mono_type(env, dtmap, t))
                        .unwrap_or(dummy_typ(loc));
                    Located::new(Typ::Signal(Box::new(inner)), loc.clone())
                }
                "http_cookie" => string_t(),
                "channel" => Located::new(
                    Typ::Ffi("Basis".to_string(), "channel".to_string()),
                    loc.clone(),
                ),
                // Types that map to string regardless of arguments
                "xml"
                | "xhtml"
                | "sql_table"
                | "sql_view"
                | "sql_query"
                | "sql_query1"
                | "sql_from_items"
                | "sql_exp"
                | "sql_expw"
                | "sql_window_function"
                | "primary_key"
                | "sql_constraints"
                | "sql_constraint"
                | "linkable"
                | "sql_order_by"
                | "propagation_mode"
                | "serialized"
                | "sql_unary"
                | "sql_binary"
                | "sql_aggregate"
                | "sql_nfunc"
                | "sql_ufunc"
                | "sql_bfunc"
                | "sql_partition"
                | "sql_window" => string_t(),
                "sql_injectable_prim" | "sql_injectable" => {
                    let t = last
                        .map(|t| mono_type(env, dtmap, t))
                        .unwrap_or(dummy_typ(loc));
                    Located::new(Typ::Fun(Box::new(t), Box::new(string_t())), loc.clone())
                }
                "trigrammable" => {
                    let t = last
                        .map(|t| mono_type(env, dtmap, t))
                        .unwrap_or(dummy_typ(loc));
                    Located::new(Typ::Fun(Box::new(t), Box::new(unit_t())), loc.clone())
                }
                // Types that map to unit record
                "monad" | "sql_subset" | "sql_summable" | "sql_maxable" | "sql_arith"
                | "nullify" | "fieldsOf" => unit_t(),
                // eq: t -> t -> bool
                "eq" => {
                    let t = last
                        .map(|t| mono_type(env, dtmap, t))
                        .unwrap_or(dummy_typ(loc));
                    let bool_t = Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
                    let inner =
                        Located::new(Typ::Fun(Box::new(t.clone()), Box::new(bool_t)), loc.clone());
                    Located::new(Typ::Fun(Box::new(t), Box::new(inner)), loc.clone())
                }
                // num: record with arithmetic operations
                "num" => {
                    let t = last
                        .map(|t| mono_type(env, dtmap, t))
                        .unwrap_or(dummy_typ(loc));
                    num_ty(t, loc)
                }
                // ord: record with comparison operations
                "ord" => {
                    let t = last
                        .map(|t| mono_type(env, dtmap, t))
                        .unwrap_or(dummy_typ(loc));
                    ord_ty(t, loc)
                }
                // show: t -> string
                "show" => {
                    let t = last
                        .map(|t| mono_type(env, dtmap, t))
                        .unwrap_or(dummy_typ(loc));
                    let s = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
                    Located::new(Typ::Fun(Box::new(t), Box::new(s)), loc.clone())
                }
                // read: {Read: string -> option t, ReadError: string -> t}
                "read" => {
                    let t = last
                        .map(|t| mono_type(env, dtmap, t))
                        .unwrap_or(dummy_typ(loc));
                    read_ty(t, loc)
                }
                // matching: (string * string)
                "matching" => {
                    let s = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
                    Located::new(
                        Typ::Record(vec![("1".into(), s.clone()), ("2".into(), s)]),
                        loc.clone(),
                    )
                }
                _ => dummy_typ(loc),
            }
        }
        // Named(n) applied to args — polymorphic datatype, not supported
        _ => dummy_typ(loc),
    }
}

fn num_ty(t: LocTyp, loc: &Span) -> LocTyp {
    let ft = || {
        Located::new(
            Typ::Fun(Box::new(t.clone()), Box::new(t.clone())),
            loc.clone(),
        )
    };
    let ft2 = || Located::new(Typ::Fun(Box::new(t.clone()), Box::new(ft())), loc.clone());
    Located::new(
        Typ::Record(vec![
            ("Zero".into(), t.clone()),
            ("Neg".into(), ft()),
            ("Plus".into(), ft2()),
            ("Minus".into(), ft2()),
            ("Times".into(), ft2()),
            ("Div".into(), ft2()),
            ("Mod".into(), ft2()),
            ("Pow".into(), ft2()),
        ]),
        loc.clone(),
    )
}

fn ord_ty(t: LocTyp, loc: &Span) -> LocTyp {
    let bool_t = Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
    let cmp_t = || {
        Located::new(
            Typ::Fun(
                Box::new(t.clone()),
                Box::new(Located::new(
                    Typ::Fun(Box::new(t.clone()), Box::new(bool_t.clone())),
                    loc.clone(),
                )),
            ),
            loc.clone(),
        )
    };
    Located::new(
        Typ::Record(vec![("Lt".into(), cmp_t()), ("Le".into(), cmp_t())]),
        loc.clone(),
    )
}

fn read_ty(t: LocTyp, loc: &Span) -> LocTyp {
    let s = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
    let opt_t = Located::new(Typ::Option(Box::new(t.clone())), loc.clone());
    let read_fn = Located::new(Typ::Fun(Box::new(s.clone()), Box::new(opt_t)), loc.clone());
    let read_err_fn = Located::new(Typ::Fun(Box::new(s), Box::new(t)), loc.clone());
    Located::new(
        Typ::Record(vec![
            ("Read".into(), read_fn),
            ("ReadError".into(), read_err_fn),
        ]),
        loc.clone(),
    )
}

fn dummy_typ(loc: &Span) -> LocTyp {
    // Use a zero-element record as the dummy type (unit in Mono)
    Located::new(Typ::Record(Vec::new()), loc.clone())
}

// ---------------------------------------------------------------------------
// Pattern translation
// ---------------------------------------------------------------------------

fn mono_pat_con(pc: &CPC) -> PatCon {
    match pc {
        CPC::Var(n) => PatCon::Var(*n),
        CPC::Ffi {
            module,
            datatyp,
            params: _,
            con,
            arg,
            kind: _,
        } => PatCon::Ffi {
            module: module.clone(),
            datatyp: datatyp.clone(),
            con: con.clone(),
            arg: arg
                .as_ref()
                .map(|_t| Located::new(Typ::Record(Vec::new()), Span::dummy())), // simplified
        },
    }
}

/// Translate a Core pattern to a Mono pattern.
///
/// Mirrors `monoPat` in `monoize.sml`.
fn mono_pat(env: &Env, dtmap: &mut HashMap<usize, DatatypeRef>, pat: &LocatedPattern) -> LocPat {
    let loc = pat.span.clone();
    match &pat.node {
        CP::Var(x, t) => Located::new(Pat::Var(x.clone(), mono_type(env, dtmap, t)), loc),
        CP::Prim(p) => Located::new(Pat::Prim(p.clone()), loc),
        CP::Constructor(dk, pc, targs, po) => {
            if targs.is_empty() {
                // Nullary or payload constructor without type args
                let mo = po.as_ref().map(|p| Box::new(mono_pat(env, dtmap, p)));
                Located::new(Pat::Con(*dk, mono_pat_con(pc), mo), loc)
            } else if targs.len() == 1 {
                // Option-like or list-like patterns
                match pc {
                    CPC::Ffi {
                        module,
                        datatyp,
                        con,
                        ..
                    } if module == "Basis" && datatyp == "list" => {
                        // list None pattern → PNone(listify t)
                        let inner_t = mono_type(env, dtmap, &targs[0]);
                        let lt = listify(inner_t, &loc);
                        if let Some(p) = po {
                            let p = mono_pat(env, dtmap, p);
                            Located::new(Pat::Some(lt, Box::new(p)), loc)
                        } else {
                            Located::new(Pat::None(lt), loc)
                        }
                    }
                    _ => {
                        // Option pattern
                        let t = mono_type(env, dtmap, &targs[0]);
                        if let Some(p) = po {
                            let p = mono_pat(env, dtmap, p);
                            Located::new(Pat::Some(t, Box::new(p)), loc)
                        } else {
                            Located::new(Pat::None(t), loc)
                        }
                    }
                }
            } else {
                // Polymorphic constructor — error
                Located::new(Pat::Prim(Prim::Int(0)), loc)
            }
        }
        CP::Record(fields) => {
            let fs: Vec<_> = fields
                .iter()
                .map(|(name, p, t)| {
                    (
                        name.clone(),
                        mono_pat(env, dtmap, p),
                        mono_type(env, dtmap, t),
                    )
                })
                .collect();
            Located::new(Pat::Record(fs), loc)
        }
    }
}

fn listify(t: LocTyp, loc: &Span) -> LocTyp {
    Located::new(
        Typ::Record(vec![
            ("1".into(), t.clone()),
            (
                "2".into(),
                Located::new(Typ::List(Box::new(t)), loc.clone()),
            ),
        ]),
        loc.clone(),
    )
}

// ---------------------------------------------------------------------------
// Type class instance builders
// ---------------------------------------------------------------------------

/// Build `EBinop(Int, op, ERel(1), ERel(0))` — binary int op on two args.
fn int_binop(op: &str, loc: &Span) -> LocExp {
    Located::new(
        Exp::Binop(
            BinopIntness::Int,
            op.into(),
            Box::new(Located::new(Exp::Rel(1), loc.clone())),
            Box::new(Located::new(Exp::Rel(0), loc.clone())),
        ),
        loc.clone(),
    )
}

/// Build `EBinop(NotInt, op, ERel(1), ERel(0))` — binary float op on two args.
fn float_binop(op: &str, loc: &Span) -> LocExp {
    Located::new(
        Exp::Binop(
            BinopIntness::NotInt,
            op.into(),
            Box::new(Located::new(Exp::Rel(1), loc.clone())),
            Box::new(Located::new(Exp::Rel(0), loc.clone())),
        ),
        loc.clone(),
    )
}

/// Build `\x t. \y t. body` — a two-argument lambda with type `t`.
fn binary_abs(t: LocTyp, result_t: LocTyp, body: LocExp, loc: &Span) -> LocExp {
    let inner = Located::new(
        Exp::Abs("y".into(), t.clone(), result_t.clone(), Box::new(body)),
        loc.clone(),
    );
    Located::new(
        Exp::Abs(
            "x".into(),
            t.clone(),
            Located::new(Typ::Fun(Box::new(t), Box::new(result_t)), loc.clone()),
            Box::new(inner),
        ),
        loc.clone(),
    )
}

/// Build a num-typeclass record for type `t` with the given operations.
fn num_ex(
    t: LocTyp,
    zero: LocExp,
    neg: LocExp,
    plus: LocExp,
    minus: LocExp,
    times: LocExp,
    div: LocExp,
    modf: LocExp,
    pow: LocExp,
    loc: &Span,
) -> LocExp {
    let ft = Located::new(
        Typ::Fun(Box::new(t.clone()), Box::new(t.clone())),
        loc.clone(),
    );
    let ft2 = Located::new(
        Typ::Fun(Box::new(t.clone()), Box::new(ft.clone())),
        loc.clone(),
    );
    Located::new(
        Exp::Record(vec![
            ("Zero".into(), zero, t.clone()),
            ("Neg".into(), neg, ft.clone()),
            ("Plus".into(), plus, ft2.clone()),
            ("Minus".into(), minus, ft2.clone()),
            ("Times".into(), times, ft2.clone()),
            ("Div".into(), div, ft2.clone()),
            ("Mod".into(), modf, ft2.clone()),
            ("Pow".into(), pow, ft2),
        ]),
        loc.clone(),
    )
}

/// Build an ord-typeclass record `{Lt, Le}` for type `t`.
fn ord_ex(lt: LocExp, le: LocExp, loc: &Span) -> LocExp {
    // Placeholder type — ord records have function types but we don't track them here.
    let unit_t = Located::new(Typ::Record(vec![]), loc.clone());
    Located::new(
        Exp::Record(vec![
            ("Lt".into(), lt, unit_t.clone()),
            ("Le".into(), le, unit_t),
        ]),
        loc.clone(),
    )
}

/// Build `\x t. body_of_x` — a single-argument lambda.
fn unary_abs(x_name: &str, t: LocTyp, result_t: LocTyp, body: LocExp, loc: &Span) -> LocExp {
    Located::new(
        Exp::Abs(x_name.into(), t, result_t, Box::new(body)),
        loc.clone(),
    )
}

/// Generate the concrete `eq_X` function for a type: `\x y. x == y`.
fn make_eq_fun(t: LocTyp, op: &str, loc: &Span) -> LocExp {
    let bool_t = Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
    let body = int_binop(op, loc);
    binary_abs(t, bool_t, body, loc)
}

/// Generate the concrete `eq_string` function: `\x y. !strcmp(x, y) == 0`.
fn make_eq_string_fun(loc: &Span) -> LocExp {
    let s = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
    let bool_t = Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
    // !strcmp(x, y) — use "!strcmp" as a binop (as SML does with EBinop(NotInt, "!strcmp", ...))
    let body = Located::new(
        Exp::Binop(
            BinopIntness::NotInt,
            "!strcmp".into(),
            Box::new(Located::new(Exp::Rel(1), loc.clone())),
            Box::new(Located::new(Exp::Rel(0), loc.clone())),
        ),
        loc.clone(),
    );
    binary_abs(s, bool_t, body, loc)
}

/// Generate a concrete binary-predicate function: `\x y. ffi_func(x, y)`.
fn make_ffi_cmp_fun(m: &str, f: &str, t: LocTyp, loc: &Span) -> LocExp {
    let bool_t = Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
    let body = Located::new(
        Exp::FfiApp(
            m.into(),
            f.into(),
            vec![
                (Located::new(Exp::Rel(1), loc.clone()), t.clone()),
                (Located::new(Exp::Rel(0), loc.clone()), t.clone()),
            ],
        ),
        loc.clone(),
    );
    binary_abs(t, bool_t, body, loc)
}

/// Generate `num_int`: the num record for Basis.int.
fn make_num_int(loc: &Span) -> LocExp {
    let t = Located::new(Typ::Ffi("Basis".into(), "int".into()), loc.clone());
    let zero = Located::new(Exp::Prim(Prim::Int(0)), loc.clone());
    let neg = unary_abs(
        "x",
        t.clone(),
        t.clone(),
        Located::new(
            Exp::Unop("-".into(), Box::new(Located::new(Exp::Rel(0), loc.clone()))),
            loc.clone(),
        ),
        loc,
    );
    let b_plus = binary_abs(t.clone(), t.clone(), int_binop("+", loc), loc);
    let b_minus = binary_abs(t.clone(), t.clone(), int_binop("-", loc), loc);
    let b_times = binary_abs(t.clone(), t.clone(), int_binop("*", loc), loc);
    let b_div = binary_abs(t.clone(), t.clone(), int_binop("/", loc), loc);
    let b_mod = binary_abs(t.clone(), t.clone(), int_binop("%", loc), loc);
    let b_pow = binary_abs(t.clone(), t.clone(), int_binop("powl", loc), loc);
    num_ex(
        t, zero, neg, b_plus, b_minus, b_times, b_div, b_mod, b_pow, loc,
    )
}

/// Generate `num_float`: the num record for Basis.float.
fn make_num_float(loc: &Span) -> LocExp {
    let t = Located::new(Typ::Ffi("Basis".into(), "float".into()), loc.clone());
    let zero = Located::new(Exp::Prim(Prim::Float(0.0)), loc.clone());
    let neg = unary_abs(
        "x",
        t.clone(),
        t.clone(),
        Located::new(
            Exp::Unop("-".into(), Box::new(Located::new(Exp::Rel(0), loc.clone()))),
            loc.clone(),
        ),
        loc,
    );
    let b_plus = binary_abs(t.clone(), t.clone(), float_binop("+", loc), loc);
    let b_minus = binary_abs(t.clone(), t.clone(), float_binop("-", loc), loc);
    let b_times = binary_abs(t.clone(), t.clone(), float_binop("*", loc), loc);
    let b_div = binary_abs(t.clone(), t.clone(), float_binop("fdiv", loc), loc);
    let b_mod = binary_abs(t.clone(), t.clone(), float_binop("fmod", loc), loc);
    let b_pow = binary_abs(t.clone(), t.clone(), float_binop("powf", loc), loc);
    num_ex(
        t, zero, neg, b_plus, b_minus, b_times, b_div, b_mod, b_pow, loc,
    )
}

/// Generate `ord_int`: the ord record for Basis.int.
fn make_ord_int(loc: &Span) -> LocExp {
    let t = Located::new(Typ::Ffi("Basis".into(), "int".into()), loc.clone());
    let bool_t = Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
    let cmp = |op: &str| binary_abs(t.clone(), bool_t.clone(), int_binop(op, loc), loc);
    ord_ex(cmp("<"), cmp("<="), loc)
}

/// Generate `ord_float`: the ord record for Basis.float.
fn make_ord_float(loc: &Span) -> LocExp {
    let t = Located::new(Typ::Ffi("Basis".into(), "float".into()), loc.clone());
    let bool_t = Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
    let cmp = |op: &str| binary_abs(t.clone(), bool_t.clone(), float_binop(op, loc), loc);
    ord_ex(cmp("<"), cmp("<="), loc)
}

/// Generate `ord_bool`.
fn make_ord_bool(loc: &Span) -> LocExp {
    let t = Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
    let bool_t = t.clone();
    let cmp = |op: &str| binary_abs(t.clone(), bool_t.clone(), int_binop(op, loc), loc);
    ord_ex(cmp("<"), cmp("<="), loc)
}

/// Generate `ord_char`.
fn make_ord_char(loc: &Span) -> LocExp {
    let t = Located::new(Typ::Ffi("Basis".into(), "char".into()), loc.clone());
    let bool_t = Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
    let cmp = |op: &str| binary_abs(t.clone(), bool_t.clone(), int_binop(op, loc), loc);
    ord_ex(cmp("<"), cmp("<="), loc)
}

/// Generate `ord_string`: {Lt=\x y. strcmp(x,y)<0, Le=\x y. strcmp(x,y)<=0}.
fn make_ord_string(loc: &Span) -> LocExp {
    let s = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
    let bool_t = Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
    let zero = Located::new(Exp::Prim(Prim::Int(0)), loc.clone());
    let cmp = |op: &str| {
        // strcmp(x, y) < 0
        let strcmp_body = Located::new(
            Exp::Binop(
                BinopIntness::Int,
                op.into(),
                Box::new(Located::new(
                    Exp::Binop(
                        BinopIntness::NotInt,
                        "strcmp".into(),
                        Box::new(Located::new(Exp::Rel(1), loc.clone())),
                        Box::new(Located::new(Exp::Rel(0), loc.clone())),
                    ),
                    loc.clone(),
                )),
                Box::new(zero.clone()),
            ),
            loc.clone(),
        );
        binary_abs(s.clone(), bool_t.clone(), strcmp_body, loc)
    };
    ord_ex(cmp("<"), cmp("<="), loc)
}

/// Generate `ord_time`: {Lt=lt_time, Le=le_time}.
fn make_ord_ffi_cmp(m: &str, lt_f: &str, le_f: &str, t: LocTyp, loc: &Span) -> LocExp {
    let lt = make_ffi_cmp_fun(m, lt_f, t.clone(), loc);
    let le = make_ffi_cmp_fun(m, le_f, t, loc);
    ord_ex(lt, le, loc)
}

/// Handle `EFfi("Basis", x)` as a concrete type class instance.
/// Returns `Some(mono_exp)` for known patterns, `None` to fall through.
fn mono_basis_ffi(x: &str, loc: &Span) -> Option<LocExp> {
    match x {
        // ---- eq instances ----
        "eq_int" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "int".into()), loc.clone());
            Some(make_eq_fun(t, "==", loc))
        }
        "eq_float" | "eq_bool" | "eq_char" => {
            let ffi_name = x.strip_prefix("eq_").unwrap_or(x);
            let t = Located::new(Typ::Ffi("Basis".into(), ffi_name.into()), loc.clone());
            Some(make_eq_fun(t, "==", loc))
        }
        "eq_string" => Some(make_eq_string_fun(loc)),
        "eq_time" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "time".into()), loc.clone());
            Some(make_ffi_cmp_fun("Basis", "eq_time", t, loc))
        }
        "eq_calendardate" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "calendardate".into()), loc.clone());
            Some(make_ffi_cmp_fun("Basis", "eq_calendardate", t, loc))
        }
        "eq_clocktime" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "clocktime".into()), loc.clone());
            Some(make_ffi_cmp_fun("Basis", "eq_clocktime", t, loc))
        }

        // ---- num instances ----
        "num_int" => Some(make_num_int(loc)),
        "num_float" => Some(make_num_float(loc)),

        // ---- ord instances ----
        "ord_int" => Some(make_ord_int(loc)),
        "ord_float" => Some(make_ord_float(loc)),
        "ord_bool" => Some(make_ord_bool(loc)),
        "ord_char" => Some(make_ord_char(loc)),
        "ord_string" => Some(make_ord_string(loc)),
        "ord_time" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "time".into()), loc.clone());
            Some(make_ord_ffi_cmp("Basis", "lt_time", "le_time", t, loc))
        }
        "ord_clocktime" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "clocktime".into()), loc.clone());
            Some(make_ord_ffi_cmp(
                "Basis",
                "lt_clocktime",
                "le_clocktime",
                t,
                loc,
            ))
        }
        "ord_calendardate" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "calendardate".into()), loc.clone());
            Some(make_ord_ffi_cmp(
                "Basis",
                "lt_calendardate",
                "le_calendardate",
                t,
                loc,
            ))
        }

        "show_int" => Some(Located::new(
            Exp::Ffi("Basis".into(), "intToString".into()),
            loc.clone(),
        )),
        "show_float" => Some(Located::new(
            Exp::Ffi("Basis".into(), "floatToString".into()),
            loc.clone(),
        )),
        "show_string" | "show_queryString" | "show_url" | "show_css_class" | "show_id" => {
            let s = string_type(loc);
            Some(Located::new(
                Exp::Abs(
                    "s".into(),
                    s.clone(),
                    s,
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                ),
                loc.clone(),
            ))
        }
        "show_char" => Some(Located::new(
            Exp::Ffi("Basis".into(), "charToString".into()),
            loc.clone(),
        )),
        "show_bool" => Some(Located::new(
            Exp::Ffi("Basis".into(), "boolToString".into()),
            loc.clone(),
        )),
        "show_time" => Some(Located::new(
            Exp::Ffi("Basis".into(), "timeToString".into()),
            loc.clone(),
        )),

        // ---- CSS class/style constants that are empty strings in C ----
        "null" | "noStyle" => Some(Located::new(
            Exp::Prim(Prim::String(
                crate::primitives::StringMode::Normal,
                String::new(),
            )),
            loc.clone(),
        )),

        "mat_nil" => {
            let s = string_type(loc);
            let empty = str_n("", loc);
            Some(Located::new(
                Exp::Record(vec![
                    ("1".into(), empty.clone(), s.clone()),
                    ("2".into(), empty, s),
                ]),
                loc.clone(),
            ))
        }

        "sql_no_limit" | "sql_no_offset" => Some(str_n("", loc)),
        "sql_asc" => Some(str_n("", loc)),
        "sql_desc" => Some(str_n(" DESC", loc)),
        "sql_and" => Some(str_n("AND", loc)),
        "sql_or" => Some(str_n("OR", loc)),
        "sql_not" => Some(str_n("NOT", loc)),
        "sql_mod" => Some(str_n("%", loc)),
        "sql_concat" => Some(str_n("||", loc)),
        "sql_like" => Some(str_n("LIKE", loc)),
        "sql_summable_int" | "sql_summable_float" | "sql_arith_int" | "sql_arith_float"
        | "sql_maxable_int" | "sql_maxable_float" | "sql_maxable_string" => Some(unit_exp(loc)),
        "sql_union" => Some(str_n("UNION", loc)),
        "sql_intersect" => Some(str_n("INTERSECT", loc)),
        "sql_except" => Some(str_n("EXCEPT", loc)),
        "sql_window_normal" | "sql_window_fancy" => Some(unit_exp(loc)),

        "sql_int" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "int".into()), loc.clone());
            let s = string_type(loc);
            Some(unary_abs(
                "x",
                t.clone(),
                s.clone(),
                Located::new(
                    Exp::FfiApp(
                        "Basis".into(),
                        "sqlifyInt".into(),
                        vec![(Located::new(Exp::Rel(0), loc.clone()), t)],
                    ),
                    loc.clone(),
                ),
                loc,
            ))
        }
        "sql_float" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "float".into()), loc.clone());
            let s = string_type(loc);
            Some(unary_abs(
                "x",
                t.clone(),
                s.clone(),
                Located::new(
                    Exp::FfiApp(
                        "Basis".into(),
                        "sqlifyFloat".into(),
                        vec![(Located::new(Exp::Rel(0), loc.clone()), t)],
                    ),
                    loc.clone(),
                ),
                loc,
            ))
        }
        "sql_bool" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
            let s = string_type(loc);
            Some(unary_abs(
                "x",
                t.clone(),
                s.clone(),
                Located::new(
                    Exp::FfiApp(
                        "Basis".into(),
                        "sqlifyBool".into(),
                        vec![(Located::new(Exp::Rel(0), loc.clone()), t)],
                    ),
                    loc.clone(),
                ),
                loc,
            ))
        }
        "sql_string" | "sql_serialized" | "sql_url" => {
            let t = string_type(loc);
            let s = string_type(loc);
            Some(unary_abs(
                "x",
                t.clone(),
                s.clone(),
                Located::new(
                    Exp::FfiApp(
                        "Basis".into(),
                        "sqlifyString".into(),
                        vec![(Located::new(Exp::Rel(0), loc.clone()), t)],
                    ),
                    loc.clone(),
                ),
                loc,
            ))
        }
        "sql_char" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "char".into()), loc.clone());
            let s = string_type(loc);
            Some(unary_abs(
                "x",
                t.clone(),
                s.clone(),
                Located::new(
                    Exp::FfiApp(
                        "Basis".into(),
                        "sqlifyChar".into(),
                        vec![(Located::new(Exp::Rel(0), loc.clone()), t)],
                    ),
                    loc.clone(),
                ),
                loc,
            ))
        }

        _ => None,
    }
}

// ---------------------------------------------------------------------------
// HTML desugaring helpers (mirror monoize.sml HTML special cases)
// ---------------------------------------------------------------------------

fn str_h(s: &str, loc: &Span) -> LocExp {
    Located::new(
        Exp::Prim(Prim::String(
            crate::primitives::StringMode::Html,
            s.to_string(),
        )),
        loc.clone(),
    )
}

fn str_n(s: &str, loc: &Span) -> LocExp {
    Located::new(
        Exp::Prim(Prim::String(
            crate::primitives::StringMode::Normal,
            s.to_string(),
        )),
        loc.clone(),
    )
}

fn make_strcat(e1: LocExp, e2: LocExp) -> LocExp {
    let loc = e1.span.clone();
    Located::new(Exp::Strcat(Box::new(e1), Box::new(e2)), loc)
}

fn make_strcat_list(parts: Vec<LocExp>, loc: &Span) -> LocExp {
    let mut iter = parts.into_iter();
    let Some(first) = iter.next() else {
        return str_n("", loc);
    };
    iter.fold(first, make_strcat)
}

fn lowercase_first(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(c) => c.to_lowercase().collect::<String>() + chars.as_str(),
    }
}

fn capitalize_first(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
    }
}

fn core_unit_type(loc: &Span) -> LocatedConstructor {
    Located::new(
        CC::TRecord(Box::new(Located::new(
            CC::Record(
                Box::new(Located::new(crate::core::Kind::Type, loc.clone())),
                Vec::new(),
            ),
            loc.clone(),
        ))),
        loc.clone(),
    )
}

fn core_lift_exp_in_exp(depth: usize, e: LocatedExpression) -> LocatedExpression {
    fn lift(depth: usize, e: LocatedExpression) -> LocatedExpression {
        let span = e.span.clone();
        match e.node {
            CE::Rel(n) => Located::new(
                if n < depth {
                    CE::Rel(n)
                } else {
                    CE::Rel(n + 1)
                },
                span,
            ),
            CE::Prim(_) | CE::Named(_) | CE::Ffi(_, _) => e,
            CE::Constructor(dk, pc, cs, arg) => Located::new(
                CE::Constructor(dk, pc, cs, arg.map(|arg| Box::new(lift(depth, *arg)))),
                span,
            ),
            CE::FfiApp(module, function, args) => Located::new(
                CE::FfiApp(
                    module,
                    function,
                    args.into_iter()
                        .map(|(arg, typ)| (lift(depth, arg), typ))
                        .collect(),
                ),
                span,
            ),
            CE::App(function, argument) => Located::new(
                CE::App(
                    Box::new(lift(depth, *function)),
                    Box::new(lift(depth, *argument)),
                ),
                span,
            ),
            CE::Abs(name, dom, ran, body) => Located::new(
                CE::Abs(name, dom, ran, Box::new(lift(depth + 1, *body))),
                span,
            ),
            CE::CApp(function, constructor) => Located::new(
                CE::CApp(Box::new(lift(depth, *function)), constructor),
                span,
            ),
            CE::CAbs(name, kind, body) => {
                Located::new(CE::CAbs(name, kind, Box::new(lift(depth, *body))), span)
            }
            CE::KAbs(name, body) => {
                Located::new(CE::KAbs(name, Box::new(lift(depth, *body))), span)
            }
            CE::KApp(function, kind) => {
                Located::new(CE::KApp(Box::new(lift(depth, *function)), kind), span)
            }
            CE::Record(fields) => Located::new(
                CE::Record(
                    fields
                        .into_iter()
                        .map(|(name, exp, typ)| (name, lift(depth, exp), typ))
                        .collect(),
                ),
                span,
            ),
            CE::Field(exp, name, meta) => {
                Located::new(CE::Field(Box::new(lift(depth, *exp)), name, meta), span)
            }
            CE::Concat(left, left_t, right, right_t) => Located::new(
                CE::Concat(
                    Box::new(lift(depth, *left)),
                    left_t,
                    Box::new(lift(depth, *right)),
                    right_t,
                ),
                span,
            ),
            CE::Cut(exp, name, meta) => {
                Located::new(CE::Cut(Box::new(lift(depth, *exp)), name, meta), span)
            }
            CE::CutMulti(exp, names, meta) => {
                Located::new(CE::CutMulti(Box::new(lift(depth, *exp)), names, meta), span)
            }
            CE::Case(disc, arms, meta) => Located::new(
                CE::Case(
                    Box::new(lift(depth, *disc)),
                    arms.into_iter()
                        .map(|(pattern, body)| {
                            let binds = crate::core::environment::pat_binds_n(&pattern);
                            (pattern, lift(depth + binds, body))
                        })
                        .collect(),
                    meta,
                ),
                span,
            ),
            CE::Write(exp) => Located::new(CE::Write(Box::new(lift(depth, *exp))), span),
            CE::Closure(name, envs) => Located::new(
                CE::Closure(name, envs.into_iter().map(|env| lift(depth, env)).collect()),
                span,
            ),
            CE::Let(name, typ, exp1, exp2) => Located::new(
                CE::Let(
                    name,
                    typ,
                    Box::new(lift(depth, *exp1)),
                    Box::new(lift(depth + 1, *exp2)),
                ),
                span,
            ),
            CE::ServerCall(name, args, typ, failure_mode) => Located::new(
                CE::ServerCall(
                    name,
                    args.into_iter().map(|arg| lift(depth, arg)).collect(),
                    typ,
                    failure_mode,
                ),
                span,
            ),
        }
    }

    lift(depth, e)
}

fn maybe_transaction_core_exp(
    typ: &LocatedConstructor,
    exp: &LocatedExpression,
    loc: &Span,
) -> Option<LocatedExpression> {
    match (&typ.node, &exp.node) {
        (CC::App(function, _), _) if matches!(&function.node, CC::Ffi(module, name) if module == "Basis" && name == "transaction") =>
        {
            let lifted = core_lift_exp_in_exp(0, exp.clone());
            let unit_t = core_unit_type(loc);
            let unit_e = Located::new(CE::Record(Vec::new()), loc.clone());
            Some(Located::new(
                CE::Abs(
                    "_".into(),
                    unit_t.clone(),
                    typ.clone(),
                    Box::new(Located::new(
                        CE::App(Box::new(lifted), Box::new(unit_e)),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            ))
        }
        (CC::TFun(dom, ran), CE::Abs(name, _, _, body)) => {
            maybe_transaction_core_exp(ran, body, loc).map(|body| {
                Located::new(
                    CE::Abs(name.clone(), *dom.clone(), *ran.clone(), Box::new(body)),
                    loc.clone(),
                )
            })
        }
        _ => None,
    }
}

fn bool_pattern(con: &str, loc: &Span) -> LocPat {
    Located::new(
        Pat::Con(
            DatatypeKind::Enum,
            PatCon::Ffi {
                module: "Basis".into(),
                datatyp: "bool".into(),
                con: con.into(),
                arg: None,
            },
            None,
        ),
        loc.clone(),
    )
}

fn string_type(loc: &Span) -> LocTyp {
    Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone())
}

fn simplify_sql_expr(e: LocExp) -> LocExp {
    match e.node {
        Exp::App(f, arg) => {
            let span = e.span;
            let f = simplify_sql_expr(*f);
            let arg = simplify_sql_expr(*arg);
            match &f.node {
                Exp::Abs(_, _, _, body) => simplify_sql_expr(
                    crate::monomorphized::environment::sub_exp_in_exp(0, &arg, body),
                ),
                _ => Located::new(Exp::App(Box::new(f), Box::new(arg)), span),
            }
        }
        other => Located::new(other, e.span),
    }
}

fn ensure_sql_string_expr(e: LocExp, loc: &Span, settings: &Settings) -> LocExp {
    let e = simplify_sql_expr(e);
    match &e.node {
        Exp::Prim(Prim::Int(_)) => Located::new(
            Exp::FfiApp(
                "Basis".into(),
                "sqlifyInt".into(),
                vec![(
                    e.clone(),
                    Located::new(Typ::Ffi("Basis".into(), "int".into()), loc.clone()),
                )],
            ),
            loc.clone(),
        ),
        Exp::Prim(Prim::Float(_)) => Located::new(
            Exp::FfiApp(
                "Basis".into(),
                "sqlifyFloat".into(),
                vec![(
                    e.clone(),
                    Located::new(Typ::Ffi("Basis".into(), "float".into()), loc.clone()),
                )],
            ),
            loc.clone(),
        ),
        Exp::Prim(Prim::String(_, _)) => e,
        Exp::Con(
            DatatypeKind::Enum,
            PatCon::Ffi {
                module,
                datatyp,
                con,
                ..
            },
            None,
        ) if module == "Basis" && datatyp == "bool" => str_n(
            if con == "True" {
                sql_true_string(settings)
            } else {
                sql_false_string(settings)
            },
            loc,
        ),
        Exp::Prim(Prim::Char(_)) => Located::new(
            Exp::FfiApp(
                "Basis".into(),
                "sqlifyChar".into(),
                vec![(
                    e.clone(),
                    Located::new(Typ::Ffi("Basis".into(), "char".into()), loc.clone()),
                )],
            ),
            loc.clone(),
        ),
        _ => e,
    }
}

fn sql_true_string(settings: &Settings) -> &'static str {
    if crate::db::ProjectDbCtx::new(&settings.db_backend)
        .resolved()
        .is_sqlite()
    {
        "1"
    } else {
        "TRUE"
    }
}

fn sql_false_string(settings: &Settings) -> &'static str {
    if crate::db::ProjectDbCtx::new(&settings.db_backend)
        .resolved()
        .is_sqlite()
    {
        "0"
    } else {
        "FALSE"
    }
}

fn is_basis_bool_con(exp: &LocExp, con: &str) -> bool {
    matches!(
        &exp.node,
        Exp::Con(
            DatatypeKind::Enum,
            PatCon::Ffi {
                module,
                datatyp,
                con: exp_con,
                ..
            },
            None,
        ) if module == "Basis" && datatyp == "bool" && exp_con == con
    )
}

fn core_basis_bool(exp: &LocatedExpression, con: &str) -> bool {
    matches!(
        &exp.node,
        CE::Constructor(
            DatatypeKind::Enum,
            CPC::Ffi {
                module,
                datatyp,
                con: exp_con,
                ..
            },
            _,
            None,
        ) if module == "Basis" && datatyp == "bool" && exp_con == con
    )
}

fn combine_nonempty_sql(left: LocExp, right: LocExp, sep: &str, loc: &Span) -> LocExp {
    let s_t = string_type(loc);
    Located::new(
        Exp::Case(
            Box::new(left),
            vec![
                (
                    Located::new(
                        Pat::Prim(Prim::String(
                            crate::primitives::StringMode::Normal,
                            String::new(),
                        )),
                        loc.clone(),
                    ),
                    right.clone(),
                ),
                (
                    Located::new(Pat::Var("left".into(), s_t.clone()), loc.clone()),
                    Located::new(
                        Exp::Case(
                            Box::new(right),
                            vec![
                                (
                                    Located::new(
                                        Pat::Prim(Prim::String(
                                            crate::primitives::StringMode::Normal,
                                            String::new(),
                                        )),
                                        loc.clone(),
                                    ),
                                    Located::new(Exp::Rel(0), loc.clone()),
                                ),
                                (
                                    Located::new(
                                        Pat::Var("right".into(), s_t.clone()),
                                        loc.clone(),
                                    ),
                                    make_strcat_list(
                                        vec![
                                            Located::new(Exp::Rel(1), loc.clone()),
                                            str_n(sep, loc),
                                            Located::new(Exp::Rel(0), loc.clone()),
                                        ],
                                        loc,
                                    ),
                                ),
                            ],
                            CaseMeta {
                                disc: s_t.clone(),
                                result: s_t.clone(),
                            },
                        ),
                        loc.clone(),
                    ),
                ),
            ],
            CaseMeta {
                disc: s_t.clone(),
                result: s_t,
            },
        ),
        loc.clone(),
    )
}

fn join_nonempty_sql(
    left: LocExp,
    right: LocExp,
    join_word: &str,
    on: LocExp,
    loc: &Span,
) -> LocExp {
    let s_t = string_type(loc);
    let on_lifted = lift_exp_in_exp(0, lift_exp_in_exp(0, on));
    Located::new(
        Exp::Case(
            Box::new(left),
            vec![
                (
                    Located::new(
                        Pat::Prim(Prim::String(
                            crate::primitives::StringMode::Normal,
                            String::new(),
                        )),
                        loc.clone(),
                    ),
                    right.clone(),
                ),
                (
                    Located::new(Pat::Var("left".into(), s_t.clone()), loc.clone()),
                    Located::new(
                        Exp::Case(
                            Box::new(right),
                            vec![
                                (
                                    Located::new(
                                        Pat::Prim(Prim::String(
                                            crate::primitives::StringMode::Normal,
                                            String::new(),
                                        )),
                                        loc.clone(),
                                    ),
                                    Located::new(Exp::Rel(0), loc.clone()),
                                ),
                                (
                                    Located::new(
                                        Pat::Var("right".into(), s_t.clone()),
                                        loc.clone(),
                                    ),
                                    make_strcat_list(
                                        vec![
                                            Located::new(Exp::Rel(1), loc.clone()),
                                            str_n(&format!(" {join_word} "), loc),
                                            Located::new(Exp::Rel(0), loc.clone()),
                                            str_n(" ON ", loc),
                                            on_lifted,
                                        ],
                                        loc,
                                    ),
                                ),
                            ],
                            CaseMeta {
                                disc: s_t.clone(),
                                result: s_t.clone(),
                            },
                        ),
                        loc.clone(),
                    ),
                ),
            ],
            CaseMeta {
                disc: s_t.clone(),
                result: s_t,
            },
        ),
        loc.clone(),
    )
}

fn optional_sql_clause(exp: LocExp, prefix: &str, settings: &Settings, loc: &Span) -> LocExp {
    let exp = ensure_sql_string_expr(exp, loc, settings);
    if is_basis_bool_con(&exp, "True") {
        return str_n("", loc);
    }
    if is_basis_bool_con(&exp, "False") {
        return make_strcat(str_n(prefix, loc), str_n(sql_false_string(settings), loc));
    }

    let s_t = string_type(loc);
    let true_string = sql_true_string(settings);
    Located::new(
        Exp::Case(
            Box::new(exp),
            vec![
                (
                    Located::new(
                        Pat::Prim(Prim::String(
                            crate::primitives::StringMode::Normal,
                            true_string.into(),
                        )),
                        loc.clone(),
                    ),
                    str_n("", loc),
                ),
                (
                    Located::new(Pat::Var("frag".into(), s_t.clone()), loc.clone()),
                    make_strcat_list(
                        vec![str_n(prefix, loc), Located::new(Exp::Rel(0), loc.clone())],
                        loc,
                    ),
                ),
            ],
            CaseMeta {
                disc: s_t.clone(),
                result: s_t,
            },
        ),
        loc.clone(),
    )
}

/// Peel all App layers (not CApp), collecting value args (in order of application).
fn peel_apps_core<'a>(
    e: &'a LocatedExpression,
    args: &mut Vec<&'a LocatedExpression>,
) -> &'a LocatedExpression {
    match &e.node {
        CE::App(f, a) => {
            let head = peel_apps_core(f, args);
            args.push(a);
            head
        }
        _ => e,
    }
}

fn peel_spine<'a>(
    e: &'a LocatedExpression,
    vargs: &mut Vec<&'a LocatedExpression>,
    targs: &mut Vec<&'a LocatedConstructor>,
) -> &'a LocatedExpression {
    match &e.node {
        CE::App(f, a) => {
            let head = peel_spine(f, vargs, targs);
            vargs.push(a);
            head
        }
        CE::CApp(f, c) => {
            let head = peel_spine(f, vargs, targs);
            targs.push(c);
            head
        }
        _ => e,
    }
}

enum MixedSpineArg<'a> {
    Value(&'a LocatedExpression),
    Type(&'a LocatedConstructor),
}

fn peel_mixed_spine<'a>(
    e: &'a LocatedExpression,
    args: &mut Vec<MixedSpineArg<'a>>,
) -> &'a LocatedExpression {
    match &e.node {
        CE::App(f, a) => {
            let head = peel_mixed_spine(f, args);
            args.push(MixedSpineArg::Value(a));
            head
        }
        CE::CApp(f, c) => {
            let head = peel_mixed_spine(f, args);
            args.push(MixedSpineArg::Type(c));
            head
        }
        _ => e,
    }
}

fn decode_query_tables(
    env: &Env,
    _loc: &Span,
    con: &LocatedConstructor,
) -> Option<Vec<(String, Vec<(String, LocTyp)>)>> {
    let normalized = normalize_constructor_for_mono(env, con);
    if matches!(normalized.node, CC::Unit) {
        return Some(Vec::new());
    }
    let CC::Record(_, fields) = &normalized.node else {
        return None;
    };
    let mut out = Vec::with_capacity(fields.len());
    for (name_con, row_con) in fields {
        let name = mono_name(name_con);
        let normalized_row = normalize_constructor_for_mono(env, row_con);
        let CC::Record(_, row_fields) = &normalized_row.node else {
            return None;
        };
        let mut dtmap = HashMap::new();
        let row = row_fields
            .iter()
            .map(|(field_name, field_ty)| {
                (mono_name(field_name), mono_type(env, &mut dtmap, field_ty))
            })
            .collect();
        out.push((name, row));
    }
    Some(out)
}

fn constructor_is_sql_query(env: &Env, con: &LocatedConstructor) -> bool {
    let normalized = normalize_constructor_for_mono(env, con);
    let mut head = &normalized;
    loop {
        match &head.node {
            CC::App(function, _) => head = function,
            CC::Ffi(module, name) => {
                return module == "Basis" && matches!(name.as_str(), "sql_query" | "sql_query1");
            }
            _ => return false,
        }
    }
}

#[allow(dead_code)]
fn looks_like_sql_query_arg(env: &Env, arg: &LocatedExpression) -> bool {
    let mut vargs = Vec::new();
    let mut targs = Vec::new();
    let head = peel_spine(arg, &mut vargs, &mut targs);
    match &head.node {
        CE::Ffi(module, name) => {
            module == "Basis" && matches!(name.as_str(), "sql_query" | "sql_query1")
        }
        CE::Named(n) => env.lookup_e_named(*n).is_some_and(|(name, con, src)| {
            ((src == "Basis"
                || src.ends_with("/lib/ur/top.ur")
                || src.ends_with("/lib/ur/basis.urs")
                || src.ends_with("/lib/ur/basis.ur"))
                && matches!(name.as_str(), "sql_query" | "sql_query1"))
                || constructor_is_sql_query(env, con)
        }),
        CE::Rel(n) => env
            .rel_e
            .get(env.rel_e.len().checked_sub(n + 1).unwrap_or(usize::MAX))
            .is_some_and(|con| constructor_is_sql_query(env, con)),
        _ => false,
    }
}

fn named_builtin_head(name: &str, src: &str) -> Option<String> {
    let is_builtin_source = src.is_empty()
        || src == "Basis"
        || src.ends_with("/lib/ur/top.ur")
        || src.ends_with("/lib/ur/basis.urs")
        || src.ends_with("/lib/ur/basis.ur");
    if is_builtin_source {
        Some(name.to_string())
    } else {
        None
    }
}

fn nearest_sql_query_rel(env: &Env) -> Option<usize> {
    env.rel_e
        .iter()
        .rev()
        .enumerate()
        .find_map(|(rel, con)| constructor_is_sql_query(env, con).then_some(rel))
}

fn nearest_string_like_rel(env: &Env) -> Option<usize> {
    env.rel_e.iter().rev().enumerate().find_map(|(rel, con)| {
        let mut dtmap = HashMap::new();
        match mono_type(env, &mut dtmap, con).node {
            Typ::Ffi(ref module, ref name) if module == "Basis" && name == "string" => Some(rel),
            _ => None,
        }
    })
}

fn string_like_rel_at_callsite(env: &Env, loc: &Span) -> Option<usize> {
    env.rel_e.iter().rev().enumerate().find_map(|(rel, con)| {
        let mut dtmap = HashMap::new();
        let is_string = matches!(
            mono_type(env, &mut dtmap, con).node,
            Typ::Ffi(ref module, ref name) if module == "Basis" && name == "string"
        );
        (is_string && con.span.file == loc.file && con.span.first.line == loc.first.line)
            .then_some(rel)
    })
}

/// Extract the HTML tag name from a tag-constructor expression.
/// e.g. `App(Ffi("Basis","head"), unit)` → "head"
///      `Ffi("Basis","head")` → "head"
///      `FfiApp("Basis","head",_)` → "head"
fn extract_tag_name(e: &LocatedExpression) -> Option<String> {
    let mut dummy = vec![];
    let base = peel_apps_core(e, &mut dummy);
    let (head, _) = peel_capp(base);
    match &head.node {
        CE::Ffi(m, x) | CE::FfiApp(m, x, _) if m == "Basis" => Some(x.clone()),
        _ => None,
    }
}

fn mono_urlify_ffi_name(name: &str) -> Option<String> {
    match name {
        "unit" => Some("urlifyString".into()),
        "int" | "float" | "string" | "char" | "bool" | "time" | "clocktime" | "calendardate"
        | "channel" => Some(format!("urlify{}", capitalize_first(name))),
        _ => None,
    }
}

fn mono_attrify_ffi_name(name: &str) -> Option<String> {
    match name {
        "string" => Some("attrifyString".into()),
        "int" => Some("attrifyInt".into()),
        _ => None,
    }
}

fn mono_urlify_exp(
    env: &Env,
    settings: &Settings,
    exp: LocExp,
    typ: &LocTyp,
    loc: &Span,
) -> Option<LocExp> {
    match (&exp.node, &typ.node) {
        (Exp::Named(n), _) => {
            let (_, _, src) = env.lookup_e_named(*n)?;
            Some(str_n(&format!("{}{}", settings.url_prefix, src), loc))
        }
        (Exp::Closure(n, args), _) => {
            let (_, core_t, src) = env.lookup_e_named(*n)?;
            if args.len() == 1
                && matches!(args[0].node, Exp::Record(ref fields) if fields.is_empty())
            {
                return Some(str_n(&format!("{}{}", settings.url_prefix, src), loc));
            }

            let mut dtmap = HashMap::new();
            let mut fun_t = mono_type(env, &mut dtmap, core_t);
            let mut parts = vec![str_n(&format!("{}{}", settings.url_prefix, src), loc)];

            for arg in args {
                match &fun_t.node {
                    Typ::Fun(dom, ran) => {
                        let encoded = mono_urlify_exp(env, settings, arg.clone(), dom, loc)?;
                        parts.push(str_n("/", loc));
                        parts.push(encoded);
                        fun_t = (**ran).clone();
                    }
                    _ => return None,
                }
            }

            Some(make_strcat_list(parts, loc))
        }
        (_, Typ::Record(fields)) if fields.is_empty() => Some(str_n("_", loc)),
        (_, Typ::Record(fields)) => {
            let mut parts = Vec::with_capacity(fields.len() * 2 - 1);
            for (idx, (field, field_t)) in fields.iter().enumerate() {
                let field_exp = Located::new(
                    Exp::Field(Box::new(exp.clone()), field.clone()),
                    loc.clone(),
                );
                let encoded = mono_urlify_exp(env, settings, field_exp, field_t, loc)?;
                if idx > 0 {
                    parts.push(str_n("/", loc));
                }
                parts.push(encoded);
            }
            Some(make_strcat_list(parts, loc))
        }
        (_, Typ::Option(inner)) => {
            let some_body = mono_urlify_exp(
                env,
                settings,
                Located::new(Exp::Rel(0), loc.clone()),
                inner,
                loc,
            )?;
            Some(Located::new(
                Exp::Case(
                    Box::new(exp),
                    vec![
                        (
                            Located::new(Pat::None((**inner).clone()), loc.clone()),
                            str_n("None", loc),
                        ),
                        (
                            Located::new(
                                Pat::Some(
                                    (**inner).clone(),
                                    Box::new(Located::new(
                                        Pat::Var("x".into(), (**inner).clone()),
                                        loc.clone(),
                                    )),
                                ),
                                loc.clone(),
                            ),
                            make_strcat(str_n("Some/", loc), some_body),
                        ),
                    ],
                    CaseMeta {
                        disc: typ.clone(),
                        result: string_type(loc),
                    },
                ),
                loc.clone(),
            ))
        }
        (_, Typ::Ffi(module, name)) => {
            if !settings.may_client_to_server(&(module.clone(), name.clone())) {
                return None;
            }
            let ffi = mono_urlify_ffi_name(name)?;
            Some(Located::new(
                Exp::FfiApp(module.clone(), ffi, vec![(exp, typ.clone())]),
                loc.clone(),
            ))
        }
        _ => None,
    }
}

fn mono_attrify_exp(exp: LocExp, typ: &LocTyp, loc: &Span) -> Option<LocExp> {
    match &typ.node {
        Typ::Record(fields) if fields.is_empty() => Some(str_n("", loc)),
        Typ::Ffi(module, name) => {
            let ffi = mono_attrify_ffi_name(name)?;
            Some(Located::new(
                Exp::FfiApp(module.clone(), ffi, vec![(exp, typ.clone())]),
                loc.clone(),
            ))
        }
        _ => None,
    }
}

fn extract_tag_attrs<'a>(
    attrs_raw: &'a LocatedExpression,
) -> Vec<(String, &'a LocatedExpression, &'a LocatedConstructor)> {
    match &attrs_raw.node {
        CE::Record(entries) => entries
            .iter()
            .map(|(name, exp, typ)| (mono_name(name), exp, typ))
            .collect(),
        _ => Vec::new(),
    }
}

fn find_tag_attr<'a>(
    attrs: &'a [(String, &'a LocatedExpression, &'a LocatedConstructor)],
    name: &str,
) -> Option<(&'a LocatedExpression, &'a LocatedConstructor)> {
    attrs
        .iter()
        .find(|(field, _, _)| field == name)
        .map(|(_, exp, typ)| (*exp, *typ))
}

fn maybe_option_attr(name: &str, opt_exp: LocExp, loc: &Span) -> LocExp {
    let inner = string_type(loc);
    let option_t = Located::new(Typ::Option(Box::new(inner.clone())), loc.clone());
    Located::new(
        Exp::Case(
            Box::new(opt_exp),
            vec![
                (
                    Located::new(Pat::None(inner.clone()), loc.clone()),
                    str_n("", loc),
                ),
                (
                    Located::new(
                        Pat::Some(
                            inner.clone(),
                            Box::new(Located::new(
                                Pat::Var("x".into(), inner.clone()),
                                loc.clone(),
                            )),
                        ),
                        loc.clone(),
                    ),
                    make_strcat_list(
                        vec![
                            str_h(&format!(" {}=\"", name), loc),
                            Located::new(Exp::Rel(0), loc.clone()),
                            str_h("\"", loc),
                        ],
                        loc,
                    ),
                ),
            ],
            CaseMeta {
                disc: option_t,
                result: string_type(loc),
            },
        ),
        loc.clone(),
    )
}

fn apply_event_handler(
    handler: LocExp,
    handler_t: &LocTyp,
    attr_name: &str,
    loc: &Span,
) -> Option<LocExp> {
    let Typ::Fun(dom, _) = &handler_t.node else {
        return None;
    };

    let unit = unit_exp(loc);
    let applied = if matches!(&dom.node, Typ::Record(fields) if fields.is_empty()) {
        Located::new(Exp::App(Box::new(handler), Box::new(unit)), loc.clone())
    } else {
        let event_name = if attr_name.starts_with("Onkey") {
            "keyEvent"
        } else {
            "mouseEvent"
        };
        let event = Located::new(
            Exp::FfiApp("Basis".into(), event_name.into(), vec![]),
            loc.clone(),
        );
        let first = Located::new(Exp::App(Box::new(handler), Box::new(event)), loc.clone());
        Located::new(Exp::App(Box::new(first), Box::new(unit)), loc.clone())
    };

    Some(Located::new(
        Exp::JavaScript(JavaScriptMode::Attribute, Box::new(applied)),
        loc.clone(),
    ))
}

fn build_tag_attrs(
    env: &Env,
    fm: &mut Fm,
    settings: &Settings,
    attrs_raw: &LocatedExpression,
    tag_name: &str,
    loc: &Span,
) -> LocExp {
    let attrs = extract_tag_attrs(attrs_raw);
    let mut out = str_n("", loc);

    for (name, exp_raw, typ_raw) in attrs {
        if name == "Source" {
            continue;
        }

        let mut dtmap = HashMap::new();
        let mono_t = mono_type(env, &mut dtmap, typ_raw);
        let mono_e = mono_exp(env, fm, exp_raw, settings);

        let piece = match &mono_t.node {
            Typ::Ffi(module, bool_name) if module == "Basis" && bool_name == "bool" => {
                Located::new(
                    Exp::Case(
                        Box::new(mono_e),
                        vec![
                            (
                                bool_pattern("True", loc),
                                str_h(&format!(" {}", lowercase_first(&name)), loc),
                            ),
                            (bool_pattern("False", loc), str_n("", loc)),
                        ],
                        CaseMeta {
                            disc: mono_t.clone(),
                            result: string_type(loc),
                        },
                    ),
                    loc.clone(),
                )
            }
            Typ::Fun(_, _) if name.starts_with("On") => {
                let js = apply_event_handler(mono_e, &mono_t, &name, loc)
                    .unwrap_or_else(|| str_n("", loc));
                make_strcat_list(
                    vec![
                        str_h(
                            &format!(" {}='uw_event=event;exec(", lowercase_first(&name)),
                            loc,
                        ),
                        js,
                        str_h(")'", loc),
                    ],
                    loc,
                )
            }
            _ => {
                let encoded = if name == "Link" || name == "Action" {
                    mono_urlify_exp(env, settings, mono_e, &mono_t, loc)
                } else {
                    mono_attrify_exp(mono_e, &mono_t, loc)
                };

                let rewritten = match name.as_str() {
                    "Typ" => "Type".to_string(),
                    "Nam" => "Name".to_string(),
                    "Link" => "Href".to_string(),
                    _ => name.clone(),
                }
                .replace('_', "-");

                match encoded {
                    Some(encoded) => {
                        let encoded = if tag_name == "coption" && rewritten == "Value" {
                            make_strcat(str_h("x", loc), encoded)
                        } else {
                            encoded
                        };
                        make_strcat_list(
                            vec![
                                str_h(&format!(" {}=\"", lowercase_first(&rewritten)), loc),
                                encoded,
                                str_h("\"", loc),
                            ],
                            loc,
                        )
                    }
                    None => str_n("", loc),
                }
            }
        };

        out = make_strcat(out, piece);
    }

    out
}

fn find_submit_action<'a>(
    xml: &'a LocatedExpression,
) -> Option<(&'a LocatedExpression, &'a LocatedConstructor)> {
    let mut vargs = Vec::new();
    let base = peel_apps_core(xml, &mut vargs);
    let (head, _) = peel_capp(base);

    match &head.node {
        CE::Ffi(m, x) | CE::FfiApp(m, x, _) if m == "Basis" && x == "join" && vargs.len() >= 2 => {
            let left = find_submit_action(vargs[vargs.len() - 2]);
            let right = find_submit_action(vargs[vargs.len() - 1]);
            match (left, right) {
                (Some(found), None) | (None, Some(found)) => Some(found),
                _ => None,
            }
        }
        CE::Ffi(m, x) | CE::FfiApp(m, x, _) if m == "Basis" && x == "tag" && vargs.len() >= 7 => {
            let n = vargs.len();
            let attrs_raw = vargs[n - 3];
            let tag_fn = vargs[n - 2];
            let inner_xml = vargs[n - 1];

            if extract_tag_name(tag_fn).as_deref() == Some("submit") {
                if let CE::Record(entries) = &attrs_raw.node {
                    if let Some((_, exp, typ)) = entries
                        .iter()
                        .find(|(name, _, _)| mono_name(name) == "Action")
                    {
                        return Some((exp, typ));
                    }
                }
            }

            find_submit_action(inner_xml)
        }
        _ => None,
    }
}

/// Desugar `Basis.tag class dynClass style dynStyle attrs tagFn xml`.
fn desugar_tag(
    env: &Env,
    fm: &mut Fm,
    settings: &Settings,
    loc: &Span,
    targs: &[&LocatedConstructor],
    class_raw: &LocatedExpression,
    _dyn_class_raw: &LocatedExpression,
    style_raw: &LocatedExpression,
    _dyn_style_raw: &LocatedExpression,
    attrs_raw: &LocatedExpression,
    tag_fn: &LocatedExpression,
    xml_raw: &LocatedExpression,
) -> LocExp {
    let tag_name = extract_tag_name(tag_fn).unwrap_or_else(|| "div".to_string());
    let class_e = mono_exp(env, fm, class_raw, settings);
    let style_e = mono_exp(env, fm, style_raw, settings);
    let xml_e = mono_exp(env, fm, xml_raw, settings);
    let string_t = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
    let class_attr = Located::new(
        Exp::FfiApp(
            "Basis".into(),
            "attrOptional".into(),
            vec![
                (str_n("class", loc), string_t.clone()),
                (class_e, string_t.clone()),
            ],
        ),
        loc.clone(),
    );
    let style_attr = Located::new(
        Exp::FfiApp(
            "Basis".into(),
            "attrOptional".into(),
            vec![
                (str_n("style", loc), string_t.clone()),
                (style_e, string_t.clone()),
            ],
        ),
        loc.clone(),
    );
    let plain_attrs = build_tag_attrs(env, fm, settings, attrs_raw, &tag_name, loc);

    let open_tag = |name: &str, extra: Vec<LocExp>| {
        let mut parts = vec![
            str_h(&format!("<{}", name), loc),
            class_attr.clone(),
            style_attr.clone(),
            plain_attrs.clone(),
        ];
        parts.extend(extra);
        make_strcat_list(parts, loc)
    };

    match tag_name.as_str() {
        "body" => {
            let attrs = extract_tag_attrs(attrs_raw);
            let onload_attr = find_tag_attr(&attrs, "Onload")
                .and_then(|(exp_raw, typ_raw)| {
                    let mut dtmap = HashMap::new();
                    let mono_t = mono_type(env, &mut dtmap, typ_raw);
                    let mono_e = mono_exp(env, fm, exp_raw, settings);
                    let js = apply_event_handler(mono_e, &mono_t, "Onload", loc)?;
                    Some(make_strcat_list(
                        vec![str_h(" onload='exec(", loc), js, str_h(")'", loc)],
                        loc,
                    ))
                })
                .unwrap_or_else(|| str_n("", loc));

            let open = make_strcat_list(
                vec![
                    str_h("<body", loc),
                    class_attr,
                    style_attr,
                    onload_attr,
                    str_h(">", loc),
                ],
                loc,
            );
            make_strcat(open, make_strcat(xml_e, str_h("</body>", loc)))
        }
        "dyn" => {
            let attrs = extract_tag_attrs(attrs_raw);
            let signal_js = find_tag_attr(&attrs, "Signal")
                .map(|(exp_raw, _)| {
                    let mono_e = mono_exp(env, fm, exp_raw, settings);
                    Located::new(
                        Exp::JavaScript(JavaScriptMode::Script, Box::new(mono_e)),
                        loc.clone(),
                    )
                })
                .unwrap_or_else(|| str_n("", loc));
            make_strcat_list(
                vec![
                    str_h("<script type=\"text/javascript\">dyn(\"span\", execD(", loc),
                    signal_js,
                    str_h("))</script>", loc),
                ],
                loc,
            )
        }
        "submit" => make_strcat(
            open_tag("input type=\"submit\"", vec![str_h(" />", loc)]),
            str_n("", loc),
        ),
        "textbox" => {
            let name = targs.last().and_then(|t| match &t.node {
                CC::Name(name) => Some(name.clone()),
                _ => None,
            });
            match name {
                Some(name) => make_strcat_list(
                    vec![
                        str_h("<input", loc),
                        class_attr,
                        style_attr,
                        plain_attrs,
                        str_h(&format!(" type=\"text\" name=\"{}\" />", name), loc),
                    ],
                    loc,
                ),
                None => open_tag("div", vec![str_h("></div>", loc)]),
            }
        }
        "ctextbox" => {
            let attrs = extract_tag_attrs(attrs_raw);
            match find_tag_attr(&attrs, "Source") {
                Some((src_raw, _)) => {
                    let mono_src = mono_exp(env, fm, src_raw, settings);
                    let src_js = Located::new(
                        Exp::JavaScript(JavaScriptMode::Script, Box::new(mono_src)),
                        loc.clone(),
                    );
                    make_strcat_list(
                        vec![
                            str_h("<script type=\"text/javascript\">inp(exec(", loc),
                            src_js,
                            str_h("))</script>", loc),
                        ],
                        loc,
                    )
                }
                None => make_strcat_list(
                    vec![
                        str_h("<input", loc),
                        class_attr,
                        style_attr,
                        plain_attrs,
                        str_h(" type=\"text\" />", loc),
                    ],
                    loc,
                ),
            }
        }
        "tabl" => {
            let open = make_strcat(open_tag("table", vec![str_h(">", loc)]), str_n("", loc));
            make_strcat(open, make_strcat(xml_e, str_h("</table>", loc)))
        }
        _ => {
            let open = make_strcat(open_tag(&tag_name, vec![str_h(">", loc)]), str_n("", loc));
            let close = str_h(&format!("</{}>", tag_name), loc);
            make_strcat(open, make_strcat(xml_e, close))
        }
    }
}

fn desugar_form(
    env: &Env,
    fm: &mut Fm,
    settings: &Settings,
    loc: &Span,
    id_raw: &LocatedExpression,
    class_raw: &LocatedExpression,
    xml_raw: &LocatedExpression,
) -> LocExp {
    let id_e = mono_exp(env, fm, id_raw, settings);
    let class_e = mono_exp(env, fm, class_raw, settings);
    let xml_e = mono_exp(env, fm, xml_raw, settings);

    let action_attr = find_submit_action(xml_raw)
        .and_then(|(action_raw, action_t_raw)| {
            let mut dtmap = HashMap::new();
            let mono_t = mono_type(env, &mut dtmap, action_t_raw);
            let mono_e = mono_exp(env, fm, action_raw, settings);
            mono_urlify_exp(env, settings, mono_e, &mono_t, loc)
        })
        .map(|url| make_strcat_list(vec![str_h(" action=\"", loc), url, str_h("\"", loc)], loc))
        .unwrap_or_else(|| str_n("", loc));

    let open = make_strcat_list(
        vec![
            str_h("<form method=\"post\"", loc),
            maybe_option_attr("id", id_e, loc),
            action_attr,
            maybe_option_attr("class", class_e, loc),
            str_h(">", loc),
        ],
        loc,
    );

    make_strcat(open, make_strcat(xml_e, str_h("</form>", loc)))
}

/// Maximum `ECApp` / `CApp` layers peeled by [`peel_capp`] (matches other IR chain caps).
const MAX_PEEL_CAPP_DEPTH: usize = 65_536;

/// Peel `CApp` layers: returns `(innermost_expr, type_args_innermost_first)`.
fn peel_capp(e: &LocatedExpression) -> (&LocatedExpression, Vec<&LocatedConstructor>) {
    let mut inner = e;
    let mut args = Vec::new();
    for _peel_step in 0..MAX_PEEL_CAPP_DEPTH {
        let CE::CApp(inner_e, c) = &inner.node else {
            break;
        };
        args.push(c as &LocatedConstructor);
        inner = inner_e;
    }
    if matches!(&inner.node, CE::CApp(..)) {
        panic!("peel_capp exceeded {MAX_PEEL_CAPP_DEPTH} (internal limit)");
    }
    // args is [outermost_type_arg, ..., innermost_type_arg] — reverse so [0] = first applied
    args.reverse();
    (inner, args)
}

/// Handle ECApp chains over `EFfi("Basis", x)`.
/// Returns `Some(mono_exp)` for known patterns, `None` to fall through.
fn mono_basis_capp(
    env: &Env,
    settings: &Settings,
    x: &str,
    targs: &[&LocatedConstructor],
    loc: &Span,
) -> Option<LocExp> {
    let last_t = targs.last();
    let bool_t = || Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
    let string_t = || Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());

    fn core_is_blobby(t: &LocatedConstructor) -> bool {
        matches!(
            &t.node,
            CC::Ffi(module, name)
                if module == "Basis" && (name == "string" || name == "blob")
        )
    }

    let text_keys_need_lengths = crate::db::ProjectDbCtx::new(&settings.db_backend)
        .resolved()
        .is_mysql();

    match x {
        "no_primary_key" => Some(str_n("", loc)),

        "primary_key" => {
            let unique = match &targs.last()?.node {
                CC::Record(_, fields) => fields,
                _ => return None,
            };
            let nm = *targs.get(targs.len().checked_sub(2)?)?;
            let t = *targs.get(targs.len().checked_sub(3)?)?;

            let mut fields: Vec<(&LocatedConstructor, &LocatedConstructor)> =
                Vec::with_capacity(unique.len() + 1);
            fields.push((nm, t));
            fields.extend(unique.iter().map(|(name, typ)| (name, typ)));

            let witness_t = Located::new(
                Typ::Record(
                    fields
                        .iter()
                        .map(|(name, _)| (mono_name(name), unit_typ(loc)))
                        .collect(),
                ),
                loc.clone(),
            );

            let cols = fields
                .iter()
                .map(|(name, typ)| {
                    let mut col = settings.mangle_sql(&mono_name(name));
                    if text_keys_need_lengths && core_is_blobby(typ) {
                        col.push_str("(255)");
                    }
                    col
                })
                .collect::<Vec<_>>()
                .join(", ");

            Some(Located::new(
                Exp::Abs(
                    "_".into(),
                    witness_t,
                    string_t(),
                    Box::new(str_n(&cols, loc)),
                ),
                loc.clone(),
            ))
        }

        "no_constraint" => Some(unit_exp(loc)),

        "one_constraint" => {
            let name = match &targs.last()?.node {
                CC::Name(name) => name.clone(),
                _ => return None,
            };
            let param_t = string_t();
            let body = Located::new(
                Exp::Record(vec![(
                    name,
                    Located::new(Exp::Rel(0), loc.clone()),
                    param_t.clone(),
                )]),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("c".into(), param_t.clone(), string_t(), Box::new(body)),
                loc.clone(),
            ))
        }

        "join_constraints" => {
            let constraints_t = string_t();
            let body = Located::new(
                Exp::Strcat(
                    Box::new(Located::new(Exp::Rel(1), loc.clone())),
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                ),
                loc.clone(),
            );
            let inner = Located::new(
                Exp::Abs(
                    "cs2".into(),
                    constraints_t.clone(),
                    constraints_t.clone(),
                    Box::new(body),
                ),
                loc.clone(),
            );
            let outer_t = Located::new(
                Typ::Fun(
                    Box::new(constraints_t.clone()),
                    Box::new(constraints_t.clone()),
                ),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("cs1".into(), constraints_t, outer_t, Box::new(inner)),
                loc.clone(),
            ))
        }

        "unique" => {
            let unique = match &targs.last()?.node {
                CC::Record(_, fields) => fields,
                _ => return None,
            };
            let nm = *targs.get(targs.len().checked_sub(2)?)?;
            let t = *targs.get(targs.len().checked_sub(3)?)?;

            let mut fields: Vec<(&LocatedConstructor, &LocatedConstructor)> =
                Vec::with_capacity(unique.len() + 1);
            fields.push((nm, t));
            fields.extend(unique.iter().map(|(name, typ)| (name, typ)));

            let cols = fields
                .iter()
                .map(|(name, typ)| {
                    let mut col = settings.mangle_sql(&mono_name(name));
                    if text_keys_need_lengths && core_is_blobby(typ) {
                        col.push_str("(255)");
                    }
                    col
                })
                .collect::<Vec<_>>()
                .join(", ");

            Some(str_n(&format!("UNIQUE ({cols})"), loc))
        }

        "linkable_same" | "linkable_from_nullable" | "linkable_to_nullable" => Some(unit_exp(loc)),

        "restrict" => Some(str_n("RESTRICT", loc)),
        "cascade" => Some(str_n("CASCADE", loc)),
        "no_action" => Some(str_n("NO ACTION", loc)),
        "set_null" => Some(str_n("SET NULL", loc)),

        "sql_prim" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let tf = Located::new(Typ::Fun(Box::new(t), Box::new(string_t())), loc.clone());
            Some(Located::new(
                Exp::Abs(
                    "f".into(),
                    tf.clone(),
                    tf,
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                ),
                loc.clone(),
            ))
        }

        "nullify_option" => Some(unit_exp(loc)),
        "nullify_prim" => {
            let un = unit_typ(loc);
            Some(Located::new(
                Exp::Abs(
                    "proof".into(),
                    un.clone(),
                    un.clone(),
                    Box::new(unit_exp(loc)),
                ),
                loc.clone(),
            ))
        }

        "fieldsOf_table" | "fieldsOf_view" | "sql_subset" | "sql_subset_all" => Some(unit_exp(loc)),
        "sql_subset_concat" => {
            let un = unit_typ(loc);
            let inner = Located::new(
                Exp::Abs(
                    "right".into(),
                    un.clone(),
                    un.clone(),
                    Box::new(unit_exp(loc)),
                ),
                loc.clone(),
            );
            let outer_t = Located::new(
                Typ::Fun(Box::new(un.clone()), Box::new(un.clone())),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("left".into(), un, outer_t, Box::new(inner)),
                loc.clone(),
            ))
        }

        "sql_from_nil" => Some(str_n("", loc)),
        "sql_order_by_Nil" => Some(str_n("", loc)),
        "sql_order_by_random" => {
            let random_fn = if crate::db::ProjectDbCtx::new(&settings.db_backend).is_mysql() {
                "RAND()"
            } else {
                "RANDOM()"
            };
            Some(str_n(random_fn, loc))
        }
        "sql_eq" => Some(str_n("=", loc)),
        "sql_ne" => Some(str_n("<>", loc)),
        "sql_lt" => Some(str_n("<", loc)),
        "sql_le" => Some(str_n("<=", loc)),
        "sql_gt" => Some(str_n(">", loc)),
        "sql_ge" => Some(str_n(">=", loc)),
        "sql_plus" => {
            let un = unit_typ(loc);
            Some(Located::new(
                Exp::Abs(
                    "_".into(),
                    un.clone(),
                    string_type(loc),
                    Box::new(str_n("+", loc)),
                ),
                loc.clone(),
            ))
        }
        "sql_minus" => {
            let un = unit_typ(loc);
            Some(Located::new(
                Exp::Abs(
                    "_".into(),
                    un.clone(),
                    string_type(loc),
                    Box::new(str_n("-", loc)),
                ),
                loc.clone(),
            ))
        }
        "sql_times" => {
            let un = unit_typ(loc);
            Some(Located::new(
                Exp::Abs(
                    "_".into(),
                    un.clone(),
                    string_type(loc),
                    Box::new(str_n("*", loc)),
                ),
                loc.clone(),
            ))
        }
        "sql_div" => {
            let un = unit_typ(loc);
            Some(Located::new(
                Exp::Abs(
                    "_".into(),
                    un.clone(),
                    string_type(loc),
                    Box::new(str_n("/", loc)),
                ),
                loc.clone(),
            ))
        }
        "sql_neg" => {
            let un = unit_typ(loc);
            Some(Located::new(
                Exp::Abs(
                    "_".into(),
                    un.clone(),
                    string_type(loc),
                    Box::new(str_n("-", loc)),
                ),
                loc.clone(),
            ))
        }
        "sql_count" => Some(str_n("COUNT(*)", loc)),
        "sql_count_col" => Some(str_n("COUNT", loc)),
        "sql_aggregate" => {
            let s = string_type(loc);
            let inner = Located::new(
                Exp::Abs(
                    "e1".into(),
                    s.clone(),
                    s.clone(),
                    Box::new(make_strcat_list(
                        vec![
                            Located::new(Exp::Rel(1), loc.clone()),
                            str_n("(", loc),
                            Located::new(Exp::Rel(0), loc.clone()),
                            str_n(")", loc),
                        ],
                        loc,
                    )),
                ),
                loc.clone(),
            );
            let inner_t = Located::new(
                Typ::Fun(Box::new(s.clone()), Box::new(s.clone())),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("c".into(), s, inner_t, Box::new(inner)),
                loc.clone(),
            ))
        }
        "sql_summable_option" | "sql_arith_option" | "sql_maxable_option" => {
            let un = unit_typ(loc);
            Some(Located::new(
                Exp::Abs("_".into(), un.clone(), un.clone(), Box::new(unit_exp(loc))),
                loc.clone(),
            ))
        }
        "sql_avg" => {
            let un = unit_typ(loc);
            Some(Located::new(
                Exp::Abs(
                    "_".into(),
                    un,
                    string_type(loc),
                    Box::new(str_n("AVG", loc)),
                ),
                loc.clone(),
            ))
        }
        "sql_sum" => {
            let un = unit_typ(loc);
            let inner = Located::new(
                Exp::Abs(
                    "_".into(),
                    un.clone(),
                    string_type(loc),
                    Box::new(str_n("SUM", loc)),
                ),
                loc.clone(),
            );
            let inner_t = Located::new(
                Typ::Fun(Box::new(un.clone()), Box::new(string_type(loc))),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("_".into(), un, inner_t, Box::new(inner)),
                loc.clone(),
            ))
        }
        "sql_max" => {
            let un = unit_typ(loc);
            let inner = Located::new(
                Exp::Abs(
                    "_".into(),
                    un.clone(),
                    string_type(loc),
                    Box::new(str_n("MAX", loc)),
                ),
                loc.clone(),
            );
            let inner_t = Located::new(
                Typ::Fun(Box::new(un.clone()), Box::new(string_type(loc))),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("_".into(), un, inner_t, Box::new(inner)),
                loc.clone(),
            ))
        }
        "sql_min" => {
            let un = unit_typ(loc);
            let inner = Located::new(
                Exp::Abs(
                    "_".into(),
                    un.clone(),
                    string_type(loc),
                    Box::new(str_n("MIN", loc)),
                ),
                loc.clone(),
            );
            let inner_t = Located::new(
                Typ::Fun(Box::new(un.clone()), Box::new(string_type(loc))),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("_".into(), un, inner_t, Box::new(inner)),
                loc.clone(),
            ))
        }

        "sql_field" => {
            let table = match &targs.get(targs.len().checked_sub(2)?)?.node {
                CC::Name(name) => name.clone(),
                _ => return None,
            };
            let field = match &targs.get(targs.len().checked_sub(1)?)?.node {
                CC::Name(name) => lowercase_first(name),
                _ => return None,
            };
            Some(str_n(
                &format!("T_{table}.{}", settings.mangle_sql(&field)),
                loc,
            ))
        }

        "sql_exp" => {
            let field = match &targs.last()?.node {
                CC::Name(name) => lowercase_first(name),
                _ => return None,
            };
            Some(str_n(&settings.mangle_sql(&field), loc))
        }

        // ECApp(EFfi("Basis", "eq"), t) → \f: t->t->bool. f
        "eq" | "mkEq" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let eq_t = Located::new(
                Typ::Fun(
                    Box::new(t.clone()),
                    Box::new(Located::new(
                        Typ::Fun(Box::new(t), Box::new(bool_t())),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs(
                    "f".into(),
                    eq_t.clone(),
                    eq_t,
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                ),
                loc.clone(),
            ))
        }

        // ECApp(EFfi("Basis", "ne"), t) → \f x y. !(f x y)
        "ne" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let b = bool_t();
            let b2 = Located::new(
                Typ::Fun(Box::new(t.clone()), Box::new(b.clone())),
                loc.clone(),
            );
            let eq_t = Located::new(
                Typ::Fun(Box::new(t.clone()), Box::new(b2.clone())),
                loc.clone(),
            );
            // \f. \x. \y. !(f x y)
            let _app_fy = Located::new(
                Exp::App(
                    Box::new(Located::new(Exp::Rel(1), loc.clone())),
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                ),
                loc.clone(),
            );
            let app_fx = Located::new(
                Exp::App(
                    Box::new(Located::new(Exp::Rel(2), loc.clone())),
                    Box::new(Located::new(Exp::Rel(1), loc.clone())),
                ),
                loc.clone(),
            );
            let body = Located::new(
                Exp::App(
                    Box::new(app_fx),
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                ),
                loc.clone(),
            );
            let not_body = Located::new(Exp::Unop("!".into(), Box::new(body)), loc.clone());
            let inner_y = Located::new(
                Exp::Abs("y".into(), t.clone(), b.clone(), Box::new(not_body)),
                loc.clone(),
            );
            let inner_x = Located::new(
                Exp::Abs("x".into(), t.clone(), b2, Box::new(inner_y)),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("f".into(), eq_t.clone(), eq_t, Box::new(inner_x)),
                loc.clone(),
            ))
        }

        // ECApp(EFfi("Basis", "zero"), t) → \r: num t. r.Zero
        "zero" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let num_t = num_ty(t.clone(), loc);
            let body = Located::new(
                Exp::Field(
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                    "Zero".into(),
                ),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("r".into(), num_t, t, Box::new(body)),
                loc.clone(),
            ))
        }
        "neg" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let num_t = num_ty(t.clone(), loc);
            let ft = Located::new(Typ::Fun(Box::new(t.clone()), Box::new(t)), loc.clone());
            let body = Located::new(
                Exp::Field(
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                    "Neg".into(),
                ),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("r".into(), num_t, ft, Box::new(body)),
                loc.clone(),
            ))
        }
        "plus" | "minus" | "times" | "divide" | "mod" | "pow" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let num_t = num_ty(t.clone(), loc);
            let ft2 = Located::new(
                Typ::Fun(
                    Box::new(t.clone()),
                    Box::new(Located::new(
                        Typ::Fun(Box::new(t.clone()), Box::new(t)),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            );
            let field_name = match x {
                "plus" => "Plus",
                "minus" => "Minus",
                "times" => "Times",
                "divide" => "Div",
                "mod" => "Mod",
                "pow" => "Pow",
                _ => "Plus",
            };
            let body = Located::new(
                Exp::Field(
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                    field_name.into(),
                ),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("r".into(), num_t, ft2, Box::new(body)),
                loc.clone(),
            ))
        }

        // ECApp(EFfi("Basis", "lt"), t) → \r: ord t. r.Lt
        "lt" | "le" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let ord_t = ord_ty(t.clone(), loc);
            let b = bool_t();
            let cmp_t = Located::new(
                Typ::Fun(
                    Box::new(t.clone()),
                    Box::new(Located::new(
                        Typ::Fun(Box::new(t), Box::new(b)),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            );
            let field = if x == "lt" { "Lt" } else { "Le" };
            let body = Located::new(
                Exp::Field(
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                    field.into(),
                ),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("r".into(), ord_t, cmp_t, Box::new(body)),
                loc.clone(),
            ))
        }

        // ECApp(EFfi("Basis", "gt"), t) → \f x y. !(f.Le x y)
        "gt" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let ord_t = ord_ty(t.clone(), loc);
            let b = bool_t();
            let cmp_t = Located::new(
                Typ::Fun(
                    Box::new(t.clone()),
                    Box::new(Located::new(
                        Typ::Fun(Box::new(t.clone()), Box::new(b.clone())),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            );
            let ret_t = Located::new(
                Typ::Fun(Box::new(t.clone()), Box::new(b.clone())),
                loc.clone(),
            );
            // \f: ord t. \x. \y. !(f.Le x y)
            let le = Located::new(
                Exp::Field(
                    Box::new(Located::new(Exp::Rel(2), loc.clone())),
                    "Le".into(),
                ),
                loc.clone(),
            );
            let app_le_x = Located::new(
                Exp::App(
                    Box::new(le),
                    Box::new(Located::new(Exp::Rel(1), loc.clone())),
                ),
                loc.clone(),
            );
            let app_le_x_y = Located::new(
                Exp::App(
                    Box::new(app_le_x),
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                ),
                loc.clone(),
            );
            let not_body = Located::new(Exp::Unop("!".into(), Box::new(app_le_x_y)), loc.clone());
            let inner_y = Located::new(
                Exp::Abs("y".into(), t.clone(), b, Box::new(not_body)),
                loc.clone(),
            );
            let inner_x = Located::new(
                Exp::Abs("x".into(), t, ret_t, Box::new(inner_y)),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("f".into(), ord_t, cmp_t, Box::new(inner_x)),
                loc.clone(),
            ))
        }

        // ECApp(EFfi("Basis", "ge"), t) → \f x y. !(f.Lt x y)
        "ge" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let ord_t = ord_ty(t.clone(), loc);
            let b = bool_t();
            let cmp_t = Located::new(
                Typ::Fun(
                    Box::new(t.clone()),
                    Box::new(Located::new(
                        Typ::Fun(Box::new(t.clone()), Box::new(b.clone())),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            );
            let ret_t = Located::new(
                Typ::Fun(Box::new(t.clone()), Box::new(b.clone())),
                loc.clone(),
            );
            let lt = Located::new(
                Exp::Field(
                    Box::new(Located::new(Exp::Rel(2), loc.clone())),
                    "Lt".into(),
                ),
                loc.clone(),
            );
            let app_lt_x = Located::new(
                Exp::App(
                    Box::new(lt),
                    Box::new(Located::new(Exp::Rel(1), loc.clone())),
                ),
                loc.clone(),
            );
            let app_lt_x_y = Located::new(
                Exp::App(
                    Box::new(app_lt_x),
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                ),
                loc.clone(),
            );
            let not_body = Located::new(Exp::Unop("!".into(), Box::new(app_lt_x_y)), loc.clone());
            let inner_y = Located::new(
                Exp::Abs("y".into(), t.clone(), b, Box::new(not_body)),
                loc.clone(),
            );
            let inner_x = Located::new(
                Exp::Abs("x".into(), t, ret_t, Box::new(inner_y)),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("f".into(), ord_t, cmp_t, Box::new(inner_x)),
                loc.clone(),
            ))
        }

        // ECApp(EFfi("Basis", "show"), t) → \f: t->string. f
        "show" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let s = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
            let show_t = Located::new(Typ::Fun(Box::new(t), Box::new(s)), loc.clone());
            Some(Located::new(
                Exp::Abs(
                    "f".into(),
                    show_t.clone(),
                    show_t,
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                ),
                loc.clone(),
            ))
        }

        "show_xml" | "show_sql_query" => {
            let s = string_type(loc);
            Some(Located::new(
                Exp::Abs(
                    "s".into(),
                    s.clone(),
                    s,
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                ),
                loc.clone(),
            ))
        }

        // ECApp(EFfi("Basis", "read"), t) → \f: read_t. f
        "read" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let read_t = read_ty(t, loc);
            Some(Located::new(
                Exp::Abs(
                    "f".into(),
                    read_t.clone(),
                    read_t,
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                ),
                loc.clone(),
            ))
        }

        "channel" => {
            let un = unit_typ(loc);
            let channel_t = Located::new(Typ::Ffi("Basis".into(), "channel".into()), loc.clone());
            Some(Located::new(
                Exp::Abs(
                    "_".into(),
                    un.clone(),
                    channel_t.clone(),
                    Box::new(Located::new(
                        Exp::FfiApp(
                            "Basis".into(),
                            "new_channel".into(),
                            vec![(unit_exp(loc), un)],
                        ),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            ))
        }

        "send" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let channel_t = Located::new(Typ::Ffi("Basis".into(), "channel".into()), loc.clone());
            let unit_t = unit_typ(loc);
            let encoded = mono_urlify_exp(
                env,
                settings,
                Located::new(Exp::Rel(1), loc.clone()),
                &t,
                loc,
            )?;
            let send_call = Located::new(
                Exp::FfiApp(
                    "Basis".into(),
                    "send".into(),
                    vec![
                        (Located::new(Exp::Rel(2), loc.clone()), channel_t.clone()),
                        (encoded, string_t()),
                    ],
                ),
                loc.clone(),
            );
            let inner = Located::new(
                Exp::Abs(
                    "_".into(),
                    unit_t.clone(),
                    unit_t.clone(),
                    Box::new(send_call),
                ),
                loc.clone(),
            );
            let inner_t = Located::new(
                Typ::Fun(Box::new(unit_t.clone()), Box::new(unit_t.clone())),
                loc.clone(),
            );
            let middle = Located::new(
                Exp::Abs("v".into(), t.clone(), inner_t.clone(), Box::new(inner)),
                loc.clone(),
            );
            let middle_t = Located::new(Typ::Fun(Box::new(t), Box::new(inner_t)), loc.clone());
            Some(Located::new(
                Exp::Abs("ch".into(), channel_t, middle_t, Box::new(middle)),
                loc.clone(),
            ))
        }

        // ECApp(EFfi("Basis", "transaction_return"), t) → fn x => fn _ => x
        // Mirrors SML monoize.sml: transaction_return becomes pure lambda.
        "transaction_return" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let un = Located::new(Typ::Record(Vec::new()), loc.clone());
            // fn x: t => fn _: unit => x
            // Inner abs: Rel(1) refers to x (depth 1 from inside inner abs)
            let inner = Located::new(
                Exp::Abs(
                    "_".into(),
                    un.clone(),
                    t.clone(),
                    Box::new(Located::new(Exp::Rel(1), loc.clone())),
                ),
                loc.clone(),
            );
            let ran = Located::new(Typ::Fun(Box::new(un), Box::new(t.clone())), loc.clone());
            Some(Located::new(
                Exp::Abs("x".into(), t, ran, Box::new(inner)),
                loc.clone(),
            ))
        }

        // ECApp(EFfi("Basis", "error"), t) → fn s : string => error s
        // Mirrors SML monoize.sml: lower directly to the aborting IR node so
        // later reducers can recognize this as non-returning.
        "error" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let s = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
            Some(Located::new(
                Exp::Abs(
                    "s".into(),
                    s.clone(),
                    t.clone(),
                    Box::new(Located::new(
                        Exp::Error(Box::new(Located::new(Exp::Rel(0), loc.clone())), t),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            ))
        }

        // ECApp(ECApp(EFfi("Basis", "transaction_bind"), t1), t2)
        //   → fn m1 => fn m2 => fn _ => let r = m1 {} in (m2 r) {}
        // Mirrors SML monoize.sml: transaction_bind becomes a pure lambda.
        "transaction_bind" if targs.len() >= 2 => {
            let t1 = {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, targs[targs.len() - 2])
            };
            let t2 = {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, targs[targs.len() - 1])
            };
            let un = Located::new(Typ::Record(Vec::new()), loc.clone());
            // mt1 = unit -> t1  (the type of a transaction t1)
            let mt1 = Located::new(
                Typ::Fun(Box::new(un.clone()), Box::new(t1.clone())),
                loc.clone(),
            );
            // mt2 = unit -> t2
            let mt2 = Located::new(
                Typ::Fun(Box::new(un.clone()), Box::new(t2.clone())),
                loc.clone(),
            );
            // In fn _ body (depth 2 from outer):
            //   Rel(0) = "_", Rel(1) = "m2", Rel(2) = "m1"
            // In let body (depth 3 from outer):
            //   Rel(0) = "r", Rel(1) = "_", Rel(2) = "m2", Rel(3) = "m1"
            // app_m1_unit = App(Rel(2), {})   i.e. m1 {} (in fn _ body, before let)
            let app_m1_unit = Located::new(
                Exp::App(
                    Box::new(Located::new(Exp::Rel(2), loc.clone())),
                    Box::new(Located::new(Exp::Record(Vec::new()), loc.clone())),
                ),
                loc.clone(),
            );
            // (m2 r) = App(Rel(2), Rel(0))
            let m2_r = Located::new(
                Exp::App(
                    Box::new(Located::new(Exp::Rel(2), loc.clone())),
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                ),
                loc.clone(),
            );
            // (m2 r) {} = App(m2_r, {})
            let m2_r_unit = Located::new(
                Exp::App(
                    Box::new(m2_r),
                    Box::new(Located::new(Exp::Record(Vec::new()), loc.clone())),
                ),
                loc.clone(),
            );
            // let r = m1 {} in (m2 r) {}
            let let_r = Located::new(
                Exp::Let(
                    "r".into(),
                    t1.clone(),
                    Box::new(app_m1_unit),
                    Box::new(m2_r_unit),
                ),
                loc.clone(),
            );
            // fn _: unit => let r = m1 {} in (m2 r) {}
            let inner_abs = Located::new(
                Exp::Abs("_".into(), un.clone(), un.clone(), Box::new(let_r)),
                loc.clone(),
            );
            // type of m2_f: t1 -> (unit -> t2)
            let m2_t = Located::new(Typ::Fun(Box::new(t1), Box::new(mt2.clone())), loc.clone());
            // return type of the whole bind: unit -> unit (transaction unit)
            let bind_ran = Located::new(
                Typ::Fun(Box::new(un.clone()), Box::new(un.clone())),
                loc.clone(),
            );
            // fn m2: (t1 -> mt2) => fn _ => ...
            let m2_abs = Located::new(
                Exp::Abs(
                    "m2".into(),
                    m2_t.clone(),
                    bind_ran.clone(),
                    Box::new(inner_abs),
                ),
                loc.clone(),
            );
            // type of outer abs: mt1 -> (m2_t -> bind_ran)
            let outer_ran = Located::new(Typ::Fun(Box::new(m2_t), Box::new(bind_ran)), loc.clone());
            // fn m1: mt1 => fn m2 => fn _ => ...
            Some(Located::new(
                Exp::Abs("m1".into(), mt1, outer_ran, Box::new(m2_abs)),
                loc.clone(),
            ))
        }

        "query" if targs.len() >= 3 => {
            let exps = match mono_type(env, &mut HashMap::new(), targs[targs.len() - 2]).node {
                Typ::Record(exps) => exps,
                _ => return None,
            };
            let tables = decode_query_tables(env, loc, targs[targs.len() - 3])?;
            let state = {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, targs[targs.len() - 1])
            };
            let s = string_type(loc);
            let un = unit_typ(loc);

            let mut row_fields = exps.clone();
            row_fields.extend(tables.iter().map(|(name, fields)| {
                (
                    name.clone(),
                    Located::new(Typ::Record(fields.clone()), loc.clone()),
                )
            }));
            let row_t = Located::new(Typ::Record(row_fields), loc.clone());
            let thunk_t = Located::new(
                Typ::Fun(Box::new(un.clone()), Box::new(state.clone())),
                loc.clone(),
            );
            let f_t = Located::new(
                Typ::Fun(
                    Box::new(row_t.clone()),
                    Box::new(Located::new(
                        Typ::Fun(Box::new(state.clone()), Box::new(thunk_t.clone())),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            );

            let query_body = Located::new(
                Exp::App(
                    Box::new(Located::new(
                        Exp::App(
                            Box::new(Located::new(
                                Exp::App(
                                    Box::new(Located::new(Exp::Rel(4), loc.clone())),
                                    Box::new(Located::new(Exp::Rel(1), loc.clone())),
                                ),
                                loc.clone(),
                            )),
                            Box::new(Located::new(Exp::Rel(0), loc.clone())),
                        ),
                        loc.clone(),
                    )),
                    Box::new(unit_exp(loc)),
                ),
                loc.clone(),
            );
            let query = Located::new(
                Exp::Query(crate::monomorphized::QueryMeta {
                    exps,
                    tables,
                    state: state.clone(),
                    query: Box::new(Located::new(Exp::Rel(3), loc.clone())),
                    body: Box::new(query_body),
                    initial: Box::new(Located::new(Exp::Rel(1), loc.clone())),
                }),
                loc.clone(),
            );
            let unit_abs = Located::new(
                Exp::Abs("_".into(), un.clone(), state.clone(), Box::new(query)),
                loc.clone(),
            );
            let i_ran = Located::new(
                Typ::Fun(Box::new(un.clone()), Box::new(state.clone())),
                loc.clone(),
            );
            let i_abs = Located::new(
                Exp::Abs("i".into(), state.clone(), i_ran.clone(), Box::new(unit_abs)),
                loc.clone(),
            );
            let f_ran = Located::new(
                Typ::Fun(Box::new(state.clone()), Box::new(i_ran.clone())),
                loc.clone(),
            );
            let f_abs = Located::new(
                Exp::Abs("f".into(), f_t.clone(), f_ran.clone(), Box::new(i_abs)),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs(
                    "q".into(),
                    s.clone(),
                    Located::new(Typ::Fun(Box::new(f_t), Box::new(f_ran)), loc.clone()),
                    Box::new(f_abs),
                ),
                loc.clone(),
            ))
        }

        _ => None,
    }
}

fn mono_basis_full_app(
    env: &Env,
    fm: &mut Fm,
    settings: &Settings,
    exp: &LocatedExpression,
    x: &str,
    targs: &[&LocatedConstructor],
    vargs: &[&LocatedExpression],
    loc: &Span,
) -> Option<LocExp> {
    if vargs.is_empty() {
        return None;
    }

    let s_t = string_type(loc);
    let last = |n: usize| -> Option<&LocatedExpression> {
        vargs.get(vargs.len().checked_sub(n)?).copied()
    };
    let mk_rel = |n: usize| Located::new(Exp::Rel(n), loc.clone());
    let mk_field =
        |e: LocExp, name: &str| Located::new(Exp::Field(Box::new(e), name.into()), loc.clone());
    let apply_arg = |function: LocExp, argument: LocExp| -> LocExp {
        match &function.node {
            Exp::Abs(_, _, _, body) => {
                crate::monomorphized::environment::sub_exp_in_exp(0, &argument, body)
            }
            _ => Located::new(
                Exp::App(Box::new(function), Box::new(argument)),
                loc.clone(),
            ),
        }
    };
    let recover_erased_query_arg =
        |arg: &LocatedExpression, expected_signature: Option<&str>| -> Option<LocExp> {
            match &arg.node {
                CE::Prim(Prim::Int(0)) => {
                    let local_sql_rel = || {
                        nearest_sql_query_rel(env)
                            .map(|rel| Located::new(Exp::Rel(rel), arg.span.clone()))
                    };
                    let local_string_rel = || {
                        nearest_string_like_rel(env)
                            .map(|rel| Located::new(Exp::Rel(rel), arg.span.clone()))
                    };
                    let callsite_string_rel = || {
                        string_like_rel_at_callsite(env, loc)
                            .map(|rel| Located::new(Exp::Rel(rel), arg.span.clone()))
                    };
                    let cached_query = || {
                        sql_query_cache()
                            .lock()
                            .ok()
                            .and_then(|cache| cache.get(&query_cache_key(&arg.span)).cloned())
                            .and_then(|entry| {
                                expected_signature
                                    .is_none_or(|signature| entry.signature == signature)
                                    .then_some(entry.query)
                            })
                    };
                    let queued_query = || {
                        queued_sql_queries()
                            .lock()
                            .ok()
                            .and_then(|queue| {
                                queue
                                    .iter()
                                    .rev()
                                    .find(|entry| {
                                        expected_signature
                                            .is_none_or(|signature| entry.signature == signature)
                                    })
                                    .cloned()
                            })
                            .map(|entry| entry.query)
                    };
                    if loc.file.ends_with("/lib/ur/top.ur")
                        && matches!(
                            loc.first.line,
                            266 | 332 | 344 | 353 | 362 | 366 | 378 | 382
                        )
                    {
                        return local_sql_rel().or_else(queued_query);
                    }
                    let chosen = cached_query()
                        .or_else(local_sql_rel)
                        .or_else(queued_query)
                        .or_else(local_string_rel)
                        .or_else(callsite_string_rel);
                    chosen
                }
                _ => None,
            }
        };

    match x {
        "query" => {
            let mut mixed = Vec::new();
            let _head = peel_mixed_spine(exp, &mut mixed);
            let (tables_con, exps_con, state_con, query_arg, body_arg, initial_arg, trailing_args) =
                match mixed.as_slice() {
                    [MixedSpineArg::Type(tables_con), MixedSpineArg::Type(exps_con), MixedSpineArg::Value(_proof1), MixedSpineArg::Type(state_con)] => {
                        (
                            *tables_con,
                            *exps_con,
                            *state_con,
                            None,
                            None,
                            None,
                            Vec::new(),
                        )
                    }
                    [MixedSpineArg::Type(tables_con), MixedSpineArg::Type(exps_con), MixedSpineArg::Value(_proof1), MixedSpineArg::Type(state_con), MixedSpineArg::Value(query_arg)] => {
                        (
                            *tables_con,
                            *exps_con,
                            *state_con,
                            Some(*query_arg),
                            None,
                            None,
                            Vec::new(),
                        )
                    }
                    [MixedSpineArg::Type(tables_con), MixedSpineArg::Type(exps_con), MixedSpineArg::Value(_proof1), MixedSpineArg::Type(state_con), MixedSpineArg::Value(query_arg), MixedSpineArg::Value(body_arg)] => {
                        (
                            *tables_con,
                            *exps_con,
                            *state_con,
                            Some(*query_arg),
                            Some(*body_arg),
                            None,
                            Vec::new(),
                        )
                    }
                    [MixedSpineArg::Type(tables_con), MixedSpineArg::Type(exps_con), MixedSpineArg::Value(_proof1), MixedSpineArg::Type(state_con), MixedSpineArg::Value(query_arg), MixedSpineArg::Value(body_arg), MixedSpineArg::Value(initial_arg), rest @ ..]
                        if rest
                            .iter()
                            .all(|arg| matches!(arg, MixedSpineArg::Value(_))) =>
                    {
                        let trailing_args = rest
                            .iter()
                            .map(|arg| match arg {
                                MixedSpineArg::Value(v) => *v,
                                MixedSpineArg::Type(_) => unreachable!(),
                            })
                            .collect();
                        (
                            *tables_con,
                            *exps_con,
                            *state_con,
                            Some(*query_arg),
                            Some(*body_arg),
                            Some(*initial_arg),
                            trailing_args,
                        )
                    }
                    _ => return None,
                };
            let exps = match mono_type(env, &mut HashMap::new(), exps_con).node {
                Typ::Record(exps) => exps,
                _ => return None,
            };
            let has_trailing_args = !trailing_args.is_empty();
            let tables = decode_query_tables(env, loc, tables_con)?;
            let state = mono_type(env, &mut HashMap::new(), state_con);
            let unit_t = unit_typ(loc);
            let expected_query_signature = query_row_signature_from_mono(&exps, &tables);

            let mut row_fields = exps.clone();
            row_fields.extend(tables.iter().map(|(name, fields)| {
                (
                    name.clone(),
                    Located::new(Typ::Record(fields.clone()), loc.clone()),
                )
            }));
            let row_t = Located::new(Typ::Record(row_fields), loc.clone());
            let thunk_t = Located::new(
                Typ::Fun(Box::new(unit_t.clone()), Box::new(state.clone())),
                loc.clone(),
            );
            let f_t = Located::new(
                Typ::Fun(
                    Box::new(row_t.clone()),
                    Box::new(Located::new(
                        Typ::Fun(Box::new(state.clone()), Box::new(thunk_t.clone())),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            );

            let body = Located::new(
                Exp::App(
                    Box::new(Located::new(
                        Exp::App(
                            Box::new(Located::new(
                                Exp::App(
                                    Box::new(Located::new(Exp::Rel(4), loc.clone())),
                                    Box::new(mk_rel(1)),
                                ),
                                loc.clone(),
                            )),
                            Box::new(mk_rel(0)),
                        ),
                        loc.clone(),
                    )),
                    Box::new(unit_exp(loc)),
                ),
                loc.clone(),
            );
            let query = Located::new(
                Exp::Query(crate::monomorphized::QueryMeta {
                    exps: exps.clone(),
                    tables: tables.clone(),
                    state: state.clone(),
                    query: Box::new(Located::new(Exp::Rel(3), loc.clone())),
                    body: Box::new(body),
                    initial: Box::new(Located::new(Exp::Rel(1), loc.clone())),
                }),
                loc.clone(),
            );
            let unit_abs = Located::new(
                Exp::Abs("_".into(), unit_t.clone(), state.clone(), Box::new(query)),
                loc.clone(),
            );
            let i_ran = Located::new(
                Typ::Fun(Box::new(unit_t.clone()), Box::new(state.clone())),
                loc.clone(),
            );
            let i_abs = Located::new(
                Exp::Abs("i".into(), state.clone(), i_ran.clone(), Box::new(unit_abs)),
                loc.clone(),
            );
            let f_ran = Located::new(
                Typ::Fun(Box::new(state.clone()), Box::new(i_ran.clone())),
                loc.clone(),
            );
            let mut lowered = Located::new(
                Exp::Abs(
                    "q".into(),
                    s_t.clone(),
                    Located::new(
                        Typ::Fun(Box::new(f_t.clone()), Box::new(f_ran.clone())),
                        loc.clone(),
                    ),
                    Box::new(Located::new(
                        Exp::Abs("f".into(), f_t, f_ran, Box::new(i_abs)),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            );
            let instantiate_body_fun = |fm: &mut Fm, body_arg: &LocatedExpression| {
                let mut body_fun = mono_exp(env, fm, body_arg, settings);
                for arg in trailing_args.iter().rev() {
                    let marg = mono_exp(env, fm, arg, settings);
                    body_fun =
                        crate::monomorphized::environment::sub_exp_in_exp(0, &marg, &body_fun);
                }
                body_fun
            };
            let effective_body_fun =
                |fm: &mut Fm, body_arg: &LocatedExpression| instantiate_body_fun(fm, body_arg);
            let recovered_query = query_arg
                .and_then(|arg| recover_erased_query_arg(arg, Some(&expected_query_signature)));
            let mut lowered_is_partial_query_abs = false;
            match (query_arg, body_arg, initial_arg, recovered_query.clone()) {
                (Some(query_arg), Some(body_arg), Some(initial_arg), None)
                    if matches!(&query_arg.node, CE::Prim(Prim::Int(0))) =>
                {
                    let body_exp = lift_exp_in_exp(0, effective_body_fun(fm, body_arg));
                    let initial_exp = lift_exp_in_exp(0, mono_exp(env, fm, initial_arg, settings));
                    let q_rel = Located::new(Exp::Rel(0), loc.clone());
                    let partially_applied = Located::new(
                        Exp::App(
                            Box::new(Located::new(
                                Exp::App(
                                    Box::new(Located::new(
                                        Exp::App(Box::new(lowered), Box::new(q_rel)),
                                        loc.clone(),
                                    )),
                                    Box::new(body_exp),
                                ),
                                loc.clone(),
                            )),
                            Box::new(initial_exp),
                        ),
                        loc.clone(),
                    );
                    lowered = Located::new(
                        Exp::Abs(
                            "q".into(),
                            s_t.clone(),
                            thunk_t.clone(),
                            Box::new(partially_applied),
                        ),
                        loc.clone(),
                    );
                    lowered_is_partial_query_abs = true;
                }
                _ => {
                    let mut args = Vec::new();
                    if let Some(arg) = query_arg {
                        args.push(
                            recovered_query
                                .clone()
                                .unwrap_or_else(|| mono_exp(env, fm, arg, settings)),
                        );
                    }
                    if let Some(arg) = body_arg {
                        args.push(effective_body_fun(fm, arg));
                    }
                    if let Some(arg) = initial_arg {
                        args.push(mono_exp(env, fm, arg, settings));
                    }
                    for marg in args {
                        lowered = apply_arg(lowered, marg);
                    }
                    if has_trailing_args {
                        for arg in &trailing_args {
                            let marg = if matches!(arg.node, CE::Prim(Prim::Int(0))) {
                                unit_exp(loc)
                            } else {
                                mono_exp(env, fm, arg, settings)
                            };
                            lowered = apply_arg(lowered, marg);
                        }
                    }
                }
            }
            if lowered_is_partial_query_abs && has_trailing_args {
                return None;
            }

            Some(lowered)
        }

        "dml" if !vargs.is_empty() => {
            let e = mono_exp(env, fm, last(1)?, settings);
            let disc = string_type(loc);
            let unit_t = unit_typ(loc);
            Some(Located::new(
                Exp::Case(
                    Box::new(e),
                    vec![
                        (
                            Located::new(
                                Pat::Prim(Prim::String(
                                    crate::primitives::StringMode::Normal,
                                    String::new(),
                                )),
                                loc.clone(),
                            ),
                            unit_exp(loc),
                        ),
                        (
                            Located::new(Pat::Var("cmd".into(), disc.clone()), loc.clone()),
                            Located::new(
                                Exp::Dml(
                                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                                    FailureMode::Error,
                                ),
                                loc.clone(),
                            ),
                        ),
                    ],
                    CaseMeta {
                        disc,
                        result: unit_t,
                    },
                ),
                loc.clone(),
            ))
        }

        "tryDml" if !vargs.is_empty() => {
            let e = mono_exp(env, fm, last(1)?, settings);
            let disc = string_type(loc);
            let unit_t = unit_typ(loc);
            Some(Located::new(
                Exp::Case(
                    Box::new(e),
                    vec![
                        (
                            Located::new(
                                Pat::Prim(Prim::String(
                                    crate::primitives::StringMode::Normal,
                                    String::new(),
                                )),
                                loc.clone(),
                            ),
                            unit_exp(loc),
                        ),
                        (
                            Located::new(Pat::Var("cmd".into(), disc.clone()), loc.clone()),
                            Located::new(
                                Exp::Dml(
                                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                                    FailureMode::None,
                                ),
                                loc.clone(),
                            ),
                        ),
                    ],
                    CaseMeta {
                        disc,
                        result: unit_t,
                    },
                ),
                loc.clone(),
            ))
        }

        "unique" => mono_basis_capp(env, settings, x, targs, loc),

        "one_constraint" => {
            let name = match &targs.last()?.node {
                CC::Name(name) => name.clone(),
                _ => return None,
            };
            let c = mono_exp(env, fm, last(1)?, settings);
            Some(Located::new(Exp::Record(vec![(name, c, s_t)]), loc.clone()))
        }

        "join_constraints" => {
            let cs1 = mono_exp(env, fm, last(2)?, settings);
            let cs2 = mono_exp(env, fm, last(1)?, settings);
            Some(make_strcat(cs1, cs2))
        }

        "mat_cons" => {
            let nm1 = match &targs.get(targs.len().checked_sub(2)?)?.node {
                CC::Name(name) => lowercase_first(name),
                _ => return None,
            };
            let nm2 = match &targs.get(targs.len().checked_sub(1)?)?.node {
                CC::Name(name) => lowercase_first(name),
                _ => return None,
            };
            let m = mono_exp(env, fm, last(1)?, settings);
            let m1 = mk_field(m.clone(), "1");
            let m2 = mk_field(m.clone(), "2");
            let col1 = settings.mangle_sql(&nm1);
            let col2 = settings.mangle_sql(&nm2);
            let rec = |left: LocExp, right: LocExp| {
                Located::new(
                    Exp::Record(vec![
                        ("1".into(), left, s_t.clone()),
                        ("2".into(), right, s_t.clone()),
                    ]),
                    loc.clone(),
                )
            };
            Some(Located::new(
                Exp::Case(
                    Box::new(m1.clone()),
                    vec![
                        (
                            Located::new(
                                Pat::Prim(Prim::String(
                                    crate::primitives::StringMode::Normal,
                                    String::new(),
                                )),
                                loc.clone(),
                            ),
                            rec(str_n(&col1, loc), str_n(&col2, loc)),
                        ),
                        (
                            Located::new(Pat::Var("_".into(), s_t.clone()), loc.clone()),
                            rec(
                                make_strcat(str_n(&(col1 + ", "), loc), m1),
                                make_strcat(str_n(&(col2 + ", "), loc), m2),
                            ),
                        ),
                    ],
                    CaseMeta {
                        disc: s_t.clone(),
                        result: Located::new(
                            Typ::Record(vec![("1".into(), s_t.clone()), ("2".into(), s_t.clone())]),
                            loc.clone(),
                        ),
                    },
                ),
                loc.clone(),
            ))
        }

        "check" => {
            let e = mono_exp(env, fm, last(1)?, settings);
            Some(make_strcat(
                str_n("CHECK ", loc),
                Located::new(
                    Exp::FfiApp("Basis".into(), "checkString".into(), vec![(e, s_t.clone())]),
                    loc.clone(),
                ),
            ))
        }

        "foreign_key" => {
            let matching = mono_exp(env, fm, last(3)?, settings);
            let tab = mono_exp(env, fm, last(2)?, settings);
            let props = mono_exp(env, fm, last(1)?, settings);

            let prop = |field: &str, kw: &str| {
                let fd = mk_field(props.clone(), field);
                Located::new(
                    Exp::Case(
                        Box::new(fd.clone()),
                        vec![
                            (
                                Located::new(
                                    Pat::Prim(Prim::String(
                                        crate::primitives::StringMode::Normal,
                                        "NO ACTION".into(),
                                    )),
                                    loc.clone(),
                                ),
                                str_n("", loc),
                            ),
                            (
                                Located::new(Pat::Var("_".into(), s_t.clone()), loc.clone()),
                                make_strcat_list(vec![str_n(&format!(" ON {kw} "), loc), fd], loc),
                            ),
                        ],
                        CaseMeta {
                            disc: s_t.clone(),
                            result: s_t.clone(),
                        },
                    ),
                    loc.clone(),
                )
            };

            Some(make_strcat_list(
                vec![
                    str_n("FOREIGN KEY (", loc),
                    mk_field(matching.clone(), "1"),
                    str_n(") REFERENCES ", loc),
                    tab,
                    str_n(" (", loc),
                    mk_field(matching, "2"),
                    str_n(")", loc),
                    prop("OnDelete", "DELETE"),
                    prop("OnUpdate", "UPDATE"),
                ],
                loc,
            ))
        }

        "sql_inject" => {
            let inj = mono_exp(env, fm, last(2)?, settings);
            let value = mono_exp(env, fm, last(1)?, settings);
            Some(Located::new(
                Exp::App(Box::new(inj), Box::new(value)),
                loc.clone(),
            ))
        }

        "sql_from_table" => {
            if vargs.len() < 2 {
                return None;
            }
            let tab = mono_exp(env, fm, last(1)?, settings);
            let alias = match targs.last().map(|t| &t.node) {
                Some(CC::Name(name)) => name.clone(),
                _ => match &tab.node {
                    Exp::Prim(Prim::String(_, table_name)) => {
                        let stem = table_name.rsplit('_').next().unwrap_or("t");
                        stem.chars()
                            .next()
                            .map(|c| c.to_ascii_uppercase().to_string())
                            .unwrap_or_else(|| "T".into())
                    }
                    _ => "T".into(),
                },
            };
            Some(make_strcat(tab, str_n(&format!(" AS T_{alias}"), loc)))
        }

        "sql_from_query" => {
            let q = mono_exp(env, fm, last(1)?, settings);
            let alias = match targs.last().map(|t| &t.node) {
                Some(CC::Name(name)) => name.clone(),
                _ => "T".into(),
            };
            Some(make_strcat_list(
                vec![str_n("(", loc), q, str_n(&format!(") AS T_{alias}"), loc)],
                loc,
            ))
        }

        "sql_from_comma" => {
            let left = mono_exp(env, fm, last(2)?, settings);
            let right = mono_exp(env, fm, last(1)?, settings);
            Some(combine_nonempty_sql(left, right, ", ", loc))
        }

        "sql_inner_join" => {
            let left = mono_exp(env, fm, last(3)?, settings);
            let right = mono_exp(env, fm, last(2)?, settings);
            let on = mono_exp(env, fm, last(1)?, settings);
            Some(join_nonempty_sql(left, right, "JOIN", on, loc))
        }

        "sql_left_join" => {
            let left = mono_exp(env, fm, last(3)?, settings);
            let right = mono_exp(env, fm, last(2)?, settings);
            let on = mono_exp(env, fm, last(1)?, settings);
            Some(join_nonempty_sql(left, right, "LEFT JOIN", on, loc))
        }

        "sql_right_join" => {
            let left = mono_exp(env, fm, last(3)?, settings);
            let right = mono_exp(env, fm, last(2)?, settings);
            let on = mono_exp(env, fm, last(1)?, settings);
            Some(join_nonempty_sql(left, right, "RIGHT JOIN", on, loc))
        }

        "sql_full_join" => {
            let left = mono_exp(env, fm, last(3)?, settings);
            let right = mono_exp(env, fm, last(2)?, settings);
            let on = mono_exp(env, fm, last(1)?, settings);
            Some(join_nonempty_sql(left, right, "FULL JOIN", on, loc))
        }

        "sql_window" => {
            if vargs.len() < 2 {
                return None;
            }
            Some(mono_exp(env, fm, last(1)?, settings))
        }

        "sql_unary" => {
            let c = mono_exp(env, fm, last(2)?, settings);
            let e1 = ensure_sql_string_expr(mono_exp(env, fm, last(1)?, settings), loc, settings);
            Some(make_strcat_list(
                vec![str_n("(", loc), c, str_n(" ", loc), e1, str_n(")", loc)],
                loc,
            ))
        }

        "sql_order_by_Cons" => {
            let e1 = mono_exp(env, fm, last(3)?, settings);
            let dir = mono_exp(env, fm, last(2)?, settings);
            let e2 = mono_exp(env, fm, last(1)?, settings);
            Some(Located::new(
                Exp::Case(
                    Box::new(e2.clone()),
                    vec![
                        (
                            Located::new(
                                Pat::Prim(Prim::String(
                                    crate::primitives::StringMode::Normal,
                                    String::new(),
                                )),
                                loc.clone(),
                            ),
                            make_strcat(e1.clone(), dir.clone()),
                        ),
                        (
                            Located::new(Pat::Var("_".into(), s_t.clone()), loc.clone()),
                            make_strcat_list(vec![e1, dir, str_n(", ", loc), e2], loc),
                        ),
                    ],
                    CaseMeta {
                        disc: s_t.clone(),
                        result: s_t.clone(),
                    },
                ),
                loc.clone(),
            ))
        }

        "sql_binary" => {
            let c = mono_exp(env, fm, last(3)?, settings);
            let e1 = ensure_sql_string_expr(mono_exp(env, fm, last(2)?, settings), loc, settings);
            let e2 = ensure_sql_string_expr(mono_exp(env, fm, last(1)?, settings), loc, settings);
            Some(make_strcat_list(
                vec![
                    str_n("(", loc),
                    e1,
                    str_n(" ", loc),
                    c,
                    str_n(" ", loc),
                    e2,
                    str_n(")", loc),
                ],
                loc,
            ))
        }

        "sql_query" => {
            let raw_r = last(1)?;
            let CE::Record(fields) = &raw_r.node else {
                return None;
            };
            let lookup = |name: &str| -> Option<&LocatedExpression> {
                fields
                    .iter()
                    .find(|(field_name, _, _)| mono_name(field_name) == name)
                    .map(|(_, e, _)| e)
            };
            let rows = mono_exp(env, fm, lookup("Rows")?, settings);
            let order_by = mono_exp(env, fm, lookup("OrderBy")?, settings);
            let limit = mono_exp(env, fm, lookup("Limit")?, settings);
            let offset = mono_exp(env, fm, lookup("Offset")?, settings);
            let order_suffix = Located::new(
                Exp::Case(
                    Box::new(order_by),
                    vec![
                        (
                            Located::new(
                                Pat::Prim(Prim::String(
                                    crate::primitives::StringMode::Normal,
                                    String::new(),
                                )),
                                loc.clone(),
                            ),
                            str_n("", loc),
                        ),
                        (
                            Located::new(Pat::Var("orderby".into(), s_t.clone()), loc.clone()),
                            make_strcat_list(vec![str_n(" ORDER BY ", loc), mk_rel(0)], loc),
                        ),
                    ],
                    CaseMeta {
                        disc: s_t.clone(),
                        result: s_t.clone(),
                    },
                ),
                loc.clone(),
            );
            Some(make_strcat_list(
                vec![rows, order_suffix, limit, offset],
                loc,
            ))
        }

        "sql_query1" => {
            let raw_r = last(1)?;
            let CE::Record(fields) = &raw_r.node else {
                return None;
            };
            let lookup = |name: &str| -> Option<&LocatedExpression> {
                fields
                    .iter()
                    .find(|(field_name, _, _)| mono_name(field_name) == name)
                    .map(|(_, e, _)| e)
            };
            let distinct = mono_exp(env, fm, lookup("Distinct")?, settings);
            let from = mono_exp(env, fm, lookup("From")?, settings);
            let where_raw = lookup("Where")?;
            let where_e = mono_exp(env, fm, where_raw, settings);
            let having_raw = lookup("Having")?;
            let having_e = mono_exp(env, fm, having_raw, settings);
            let select_exps = mono_exp(env, fm, lookup("SelectExps")?, settings);
            let Exp::Record(select_exps_fields) = &select_exps.node else {
                return None;
            };
            let tables = decode_query_tables(env, loc, targs.get(targs.len().checked_sub(5)?)?)?;
            let grouped = decode_query_tables(env, loc, targs.get(targs.len().checked_sub(4)?)?)?;
            let selected_fields =
                decode_query_tables(env, loc, targs.get(targs.len().checked_sub(3)?)?)?;

            let distinct_prefix = Located::new(
                Exp::Case(
                    Box::new(distinct),
                    vec![
                        (bool_pattern("True", loc), str_n("DISTINCT ", loc)),
                        (bool_pattern("False", loc), str_n("", loc)),
                    ],
                    CaseMeta {
                        disc: Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone()),
                        result: s_t.clone(),
                    },
                ),
                loc.clone(),
            );

            let mut select_parts: Vec<LocExp> = Vec::new();
            for (name, exp, _) in select_exps_fields {
                select_parts.push(make_strcat_list(
                    vec![
                        ensure_sql_string_expr(exp.clone(), loc, settings),
                        str_n(
                            &format!(" AS {}", settings.mangle_sql(&lowercase_first(name))),
                            loc,
                        ),
                    ],
                    loc,
                ));
            }
            for (table_name, row_fields) in &selected_fields {
                for (field_name, _) in row_fields {
                    select_parts.push(str_n(
                        &format!(
                            "T_{table_name}.{}",
                            settings.mangle_sql(&lowercase_first(field_name))
                        ),
                        loc,
                    ));
                }
            }
            let select_list = if select_parts.is_empty() {
                str_n("0", loc)
            } else {
                let mut iter = select_parts.into_iter();
                let first = iter.next().expect("select_parts is non-empty");
                iter.fold(first, |acc, item| {
                    make_strcat(acc, make_strcat(str_n(", ", loc), item))
                })
            };

            let from_clause = Located::new(
                Exp::Case(
                    Box::new(from),
                    vec![
                        (
                            Located::new(
                                Pat::Prim(Prim::String(
                                    crate::primitives::StringMode::Normal,
                                    String::new(),
                                )),
                                loc.clone(),
                            ),
                            str_n("", loc),
                        ),
                        (
                            Located::new(Pat::Var("x".into(), s_t.clone()), loc.clone()),
                            make_strcat_list(vec![str_n(" FROM ", loc), mk_rel(0)], loc),
                        ),
                    ],
                    CaseMeta {
                        disc: s_t.clone(),
                        result: s_t.clone(),
                    },
                ),
                loc.clone(),
            );

            let where_clause = if core_basis_bool(where_raw, "True") {
                str_n("", loc)
            } else if core_basis_bool(where_raw, "False") {
                make_strcat(
                    str_n(" WHERE ", loc),
                    str_n(sql_false_string(settings), loc),
                )
            } else {
                optional_sql_clause(where_e, " WHERE ", settings, loc)
            };

            let grouped_covers_tables = tables.iter().all(|(table_name, table_fields)| {
                grouped
                    .iter()
                    .find(|(grouped_name, _)| grouped_name == table_name)
                    .map_or(table_fields.is_empty(), |(_, grouped_fields)| {
                        table_fields.iter().all(|(field_name, _)| {
                            grouped_fields
                                .iter()
                                .any(|(grouped_field_name, _)| grouped_field_name == field_name)
                        })
                    })
            });
            let group_by_clause = if grouped_covers_tables {
                str_n("", loc)
            } else {
                let mut group_parts = Vec::new();
                for (table_name, row_fields) in &grouped {
                    for (field_name, _) in row_fields {
                        group_parts.push(str_n(
                            &format!(
                                "T_{table_name}.{}",
                                settings.mangle_sql(&lowercase_first(field_name))
                            ),
                            loc,
                        ));
                    }
                }
                if group_parts.is_empty() {
                    str_n("", loc)
                } else {
                    let mut iter = group_parts.into_iter();
                    let first = iter.next().expect("group_parts is non-empty");
                    let body = iter.fold(first, |acc, item| {
                        make_strcat(acc, make_strcat(str_n(", ", loc), item))
                    });
                    make_strcat(str_n(" GROUP BY ", loc), body)
                }
            };
            let having_clause = if core_basis_bool(having_raw, "True") {
                str_n("", loc)
            } else if core_basis_bool(having_raw, "False") {
                make_strcat(
                    str_n(" HAVING ", loc),
                    str_n(sql_false_string(settings), loc),
                )
            } else {
                optional_sql_clause(having_e, " HAVING ", settings, loc)
            };

            let query1 = make_strcat_list(
                vec![
                    str_n("SELECT ", loc),
                    distinct_prefix,
                    select_list,
                    from_clause,
                    where_clause,
                    group_by_clause,
                    having_clause,
                ],
                loc,
            );
            let query_signature = query_row_signature(
                select_exps_fields
                    .iter()
                    .map(|(name, _, _)| name.clone())
                    .collect(),
                selected_fields
                    .iter()
                    .map(|(table, fields)| {
                        (
                            table.clone(),
                            fields.iter().map(|(name, _)| name.clone()).collect(),
                        )
                    })
                    .collect(),
            );
            let key = query_cache_key(loc);
            if let Ok(mut cache) = sql_query_cache().lock() {
                cache.insert(
                    key.clone(),
                    QueryCacheEntry {
                        query: query1.clone(),
                        signature: query_signature.clone(),
                    },
                );
            }
            if let Ok(mut queue) = queued_sql_queries().lock() {
                queue.push_back(QueryCacheEntry {
                    query: query1.clone(),
                    signature: query_signature,
                });
            }
            Some(query1)
        }

        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Expression translation: mono_exp
// ---------------------------------------------------------------------------

/// Lift all ERel(n >= depth) by 1 in a Mono expression.
fn lift_exp_in_exp(depth: usize, e: LocExp) -> LocExp {
    crate::monomorphized::environment::lift_exp_in_exp(depth, &e)
}

fn str_exp(s: impl Into<String>, loc: &Span) -> LocExp {
    Located::new(
        Exp::Prim(Prim::String(
            crate::primitives::StringMode::Normal,
            s.into(),
        )),
        loc.clone(),
    )
}

fn unit_exp(loc: &Span) -> LocExp {
    Located::new(Exp::Record(Vec::new()), loc.clone())
}

fn unit_typ(loc: &Span) -> LocTyp {
    Located::new(Typ::Record(Vec::new()), loc.clone())
}

fn source_span_excerpt(span: &Span) -> Option<String> {
    static CACHE: OnceLock<Mutex<HashMap<String, Option<String>>>> = OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    let contents = {
        let mut guard = cache.lock().expect("source excerpt cache mutex poisoned");
        match guard.get(&span.file) {
            Some(cached) => cached.clone(),
            None => {
                let loaded = fs::read_to_string(&span.file).ok();
                guard.insert(span.file.clone(), loaded.clone());
                loaded
            }
        }
    }?;

    let start_line = span.first.line.max(1) as usize;
    let end_line = span.last.line.max(span.first.line.max(1)) as usize;
    let lines: Vec<&str> = contents.lines().collect();
    if start_line > lines.len() || end_line > lines.len() {
        return None;
    }

    let mut excerpt = String::new();
    for line_index in start_line..=end_line {
        let line = lines[line_index - 1];
        let start_col = if line_index == start_line {
            span.first.col.saturating_sub(1) as usize
        } else {
            0
        };
        let end_col = if line_index == end_line {
            span.last.col.saturating_sub(1) as usize
        } else {
            line.chars().count()
        };
        if start_col > end_col {
            continue;
        }
        let segment: String = line
            .chars()
            .skip(start_col)
            .take(end_col.saturating_sub(start_col))
            .collect();
        if !excerpt.is_empty() {
            excerpt.push('\n');
        }
        excerpt.push_str(&segment);
    }

    Some(excerpt)
}

fn span_looks_like_erased_constraint_artifact(span: &Span) -> bool {
    let Some(excerpt) = source_span_excerpt(span) else {
        return false;
    };
    let trimmed = excerpt.trim();
    if trimmed.is_empty()
        || trimmed == "0"
        || trimmed.eq_ignore_ascii_case("false")
        || trimmed.eq_ignore_ascii_case("true")
    {
        return false;
    }
    true
}

fn is_synthetic_constraint_prim0(exp: &LocatedExpression) -> bool {
    matches!(exp.node, CE::Prim(Prim::Int(0)))
        && span_looks_like_erased_constraint_artifact(&exp.span)
}

fn mono_exp_uses_rel_at_depth(exp: &LocExp, target: usize, depth: usize) -> bool {
    match &exp.node {
        Exp::Rel(n) => *n == target + depth,
        Exp::Con(_, _, Some(inner))
        | Exp::Some(_, inner)
        | Exp::Write(inner)
        | Exp::SignalReturn(inner)
        | Exp::SignalSource(inner)
        | Exp::Sleep(inner)
        | Exp::Spawn(inner)
        | Exp::JavaScript(_, inner)
        | Exp::Unop(_, inner)
        | Exp::Field(inner, _)
        | Exp::Redirect(inner, _)
        | Exp::Recv(inner, _)
        | Exp::Nextval(inner) => mono_exp_uses_rel_at_depth(inner, target, depth),
        Exp::Error(inner, _) => mono_exp_uses_rel_at_depth(inner, target, depth),
        Exp::ReturnBlob {
            blob, mime_type, ..
        } => {
            blob.as_ref()
                .is_some_and(|inner| mono_exp_uses_rel_at_depth(inner, target, depth))
                || mono_exp_uses_rel_at_depth(mime_type, target, depth)
        }
        Exp::App(left, right)
        | Exp::Binop(_, _, left, right)
        | Exp::Strcat(left, right)
        | Exp::Seq(left, right)
        | Exp::SignalBind(left, right)
        | Exp::Setval(left, right) => {
            mono_exp_uses_rel_at_depth(left, target, depth)
                || mono_exp_uses_rel_at_depth(right, target, depth)
        }
        Exp::Abs(_, _, _, body) => mono_exp_uses_rel_at_depth(body, target, depth + 1),
        Exp::FfiApp(_, _, args) => args
            .iter()
            .any(|(arg, _)| mono_exp_uses_rel_at_depth(arg, target, depth)),
        Exp::Record(fields) => fields
            .iter()
            .any(|(_, value, _)| mono_exp_uses_rel_at_depth(value, target, depth)),
        Exp::Case(disc, arms, _) => {
            mono_exp_uses_rel_at_depth(disc, target, depth)
                || arms.iter().any(|(pat, body)| {
                    mono_exp_uses_rel_at_depth(
                        body,
                        target,
                        depth + crate::monomorphized::environment::pat_binds_n(pat),
                    )
                })
        }
        Exp::Let(_, _, bound, body) => {
            mono_exp_uses_rel_at_depth(bound, target, depth)
                || mono_exp_uses_rel_at_depth(body, target, depth + 1)
        }
        Exp::Closure(_, envs) => envs
            .iter()
            .any(|inner| mono_exp_uses_rel_at_depth(inner, target, depth)),
        Exp::Query(query) => {
            mono_exp_uses_rel_at_depth(&query.query, target, depth)
                || mono_exp_uses_rel_at_depth(&query.body, target, depth)
                || mono_exp_uses_rel_at_depth(&query.initial, target, depth)
        }
        Exp::Dml(inner, _) | Exp::ServerCall(inner, _, _, _) | Exp::Uurlify(inner, _, _) => {
            mono_exp_uses_rel_at_depth(inner, target, depth)
        }
        Exp::Con(_, _, None) | Exp::Prim(_) | Exp::Named(_) | Exp::None(_) | Exp::Ffi(_, _) => {
            false
        }
    }
}

fn erase_synthetic_unit_abs(exp: LocExp) -> LocExp {
    let loc = exp.span.clone();
    let node = match exp.node {
        Exp::Con(kind, pat_con, Some(inner)) => Exp::Con(
            kind,
            pat_con,
            Some(Box::new(erase_synthetic_unit_abs(*inner))),
        ),
        Exp::Con(kind, pat_con, None) => Exp::Con(kind, pat_con, None),
        Exp::Some(typ, inner) => Exp::Some(typ, Box::new(erase_synthetic_unit_abs(*inner))),
        Exp::FfiApp(module, name, args) => Exp::FfiApp(
            module,
            name,
            args.into_iter()
                .map(|(arg, typ)| (erase_synthetic_unit_abs(arg), typ))
                .collect(),
        ),
        Exp::App(left, right) => {
            let left = erase_synthetic_unit_abs(*left);
            let right = erase_synthetic_unit_abs(*right);
            let synthetic_unit_arg = matches!(&right.node, Exp::Record(fields) if fields.is_empty())
                && span_looks_like_erased_constraint_artifact(&right.span);
            if let Exp::Abs(_, _, _, body) = &left.node {
                return crate::monomorphized::environment::sub_exp_in_exp(0, &right, body);
            }
            if synthetic_unit_arg {
                return left;
            }
            Exp::App(Box::new(left), Box::new(right))
        }
        Exp::Abs(name, dom, ran, body) => {
            let body = erase_synthetic_unit_abs(*body);
            let synthetic_unit_binder = name == "_"
                && matches!(&dom.node, Typ::Record(fields) if fields.is_empty())
                && span_looks_like_erased_constraint_artifact(&dom.span)
                && !mono_exp_uses_rel_at_depth(&body, 0, 0);
            if synthetic_unit_binder {
                return crate::monomorphized::environment::sub_exp_in_exp(
                    0,
                    &unit_exp(&dom.span),
                    &body,
                );
            }
            Exp::Abs(name, dom, ran, Box::new(body))
        }
        Exp::Unop(op, inner) => Exp::Unop(op, Box::new(erase_synthetic_unit_abs(*inner))),
        Exp::Binop(intness, op, left, right) => Exp::Binop(
            intness,
            op,
            Box::new(erase_synthetic_unit_abs(*left)),
            Box::new(erase_synthetic_unit_abs(*right)),
        ),
        Exp::Record(fields) => Exp::Record(
            fields
                .into_iter()
                .map(|(name, value, typ)| (name, erase_synthetic_unit_abs(value), typ))
                .collect(),
        ),
        Exp::Field(inner, name) => Exp::Field(Box::new(erase_synthetic_unit_abs(*inner)), name),
        Exp::Case(disc, arms, meta) => Exp::Case(
            Box::new(erase_synthetic_unit_abs(*disc)),
            arms.into_iter()
                .map(|(pat, body)| (pat, erase_synthetic_unit_abs(body)))
                .collect(),
            meta,
        ),
        Exp::Strcat(left, right) => Exp::Strcat(
            Box::new(erase_synthetic_unit_abs(*left)),
            Box::new(erase_synthetic_unit_abs(*right)),
        ),
        Exp::Error(inner, typ) => Exp::Error(Box::new(erase_synthetic_unit_abs(*inner)), typ),
        Exp::ReturnBlob { blob, mime_type, t } => Exp::ReturnBlob {
            blob: blob.map(|inner| Box::new(erase_synthetic_unit_abs(*inner))),
            mime_type: Box::new(erase_synthetic_unit_abs(*mime_type)),
            t,
        },
        Exp::Redirect(inner, typ) => Exp::Redirect(Box::new(erase_synthetic_unit_abs(*inner)), typ),
        Exp::Write(inner) => Exp::Write(Box::new(erase_synthetic_unit_abs(*inner))),
        Exp::Seq(left, right) => Exp::Seq(
            Box::new(erase_synthetic_unit_abs(*left)),
            Box::new(erase_synthetic_unit_abs(*right)),
        ),
        Exp::Let(name, typ, bound, body) => Exp::Let(
            name,
            typ,
            Box::new(erase_synthetic_unit_abs(*bound)),
            Box::new(erase_synthetic_unit_abs(*body)),
        ),
        Exp::Closure(id, envs) => {
            Exp::Closure(id, envs.into_iter().map(erase_synthetic_unit_abs).collect())
        }
        Exp::Query(mut query) => {
            query.query = Box::new(erase_synthetic_unit_abs(*query.query));
            query.body = Box::new(erase_synthetic_unit_abs(*query.body));
            query.initial = Box::new(erase_synthetic_unit_abs(*query.initial));
            Exp::Query(query)
        }
        Exp::Dml(inner, mode) => Exp::Dml(Box::new(erase_synthetic_unit_abs(*inner)), mode),
        Exp::Nextval(inner) => Exp::Nextval(Box::new(erase_synthetic_unit_abs(*inner))),
        Exp::Setval(left, right) => Exp::Setval(
            Box::new(erase_synthetic_unit_abs(*left)),
            Box::new(erase_synthetic_unit_abs(*right)),
        ),
        Exp::Uurlify(inner, typ, flag) => {
            Exp::Uurlify(Box::new(erase_synthetic_unit_abs(*inner)), typ, flag)
        }
        Exp::JavaScript(mode, inner) => {
            Exp::JavaScript(mode, Box::new(erase_synthetic_unit_abs(*inner)))
        }
        Exp::SignalReturn(inner) => Exp::SignalReturn(Box::new(erase_synthetic_unit_abs(*inner))),
        Exp::SignalBind(left, right) => Exp::SignalBind(
            Box::new(erase_synthetic_unit_abs(*left)),
            Box::new(erase_synthetic_unit_abs(*right)),
        ),
        Exp::SignalSource(inner) => Exp::SignalSource(Box::new(erase_synthetic_unit_abs(*inner))),
        Exp::ServerCall(inner, typ, effect, mode) => Exp::ServerCall(
            Box::new(erase_synthetic_unit_abs(*inner)),
            typ,
            effect,
            mode,
        ),
        Exp::Recv(inner, typ) => Exp::Recv(Box::new(erase_synthetic_unit_abs(*inner)), typ),
        Exp::Sleep(inner) => Exp::Sleep(Box::new(erase_synthetic_unit_abs(*inner))),
        Exp::Spawn(inner) => Exp::Spawn(Box::new(erase_synthetic_unit_abs(*inner))),
        other => other,
    };
    Located::new(node, loc)
}

fn zero_exp(loc: &Span, reason: &str) -> LocExp {
    if loc.file.ends_with("/lib/ur/top.ur") || loc.file.ends_with("/demo/batchFun.ur") {
        eprintln!(
            "monoize zero_exp reason={reason} span={}:{}:{}-{}:{}",
            loc.file, loc.first.line, loc.first.col, loc.last.line, loc.last.col
        );
    }
    Located::new(Exp::Prim(Prim::Int(0)), loc.clone())
}

fn should_log_source_zero_once(key: &str) -> bool {
    static SEEN: OnceLock<Mutex<HashSet<String>>> = OnceLock::new();
    let seen = SEEN.get_or_init(|| Mutex::new(HashSet::new()));
    let mut guard = seen.lock().expect("source zero log mutex poisoned");
    guard.insert(key.to_string())
}

fn should_log_once(key: &str) -> bool {
    static SEEN: OnceLock<Mutex<HashSet<String>>> = OnceLock::new();
    let seen = SEEN.get_or_init(|| Mutex::new(HashSet::new()));
    let mut guard = seen.lock().expect("one-shot log mutex poisoned");
    guard.insert(key.to_string())
}

/// Translate a Core expression to a Mono expression.
///
/// Returns `(mono_exp, updated_fm)`. The `Fm` accumulates helper function
/// declarations generated for URL/attribute encoding of polymorphic types.
///
/// Mirrors `monoExp` in `monoize.sml`.
fn mono_exp(env: &Env, fm: &mut Fm, exp: &LocatedExpression, settings: &Settings) -> LocExp {
    let loc = exp.span.clone();
    match &exp.node {
        // --------------- Primitives ---------------
        CE::Prim(p) => {
            if matches!(p, Prim::Int(0)) && span_looks_like_erased_constraint_artifact(&loc) {
                return unit_exp(&loc);
            }
            if matches!(p, Prim::Int(0))
                && (loc.file.ends_with("/lib/ur/top.ur") || loc.file.ends_with("/demo/batchFun.ur"))
            {
                let key = format!(
                    "{}:{}:{}-{}:{}",
                    loc.file, loc.first.line, loc.first.col, loc.last.line, loc.last.col
                );
                if should_log_source_zero_once(&key) {
                    let rels = env
                        .rel_e
                        .iter()
                        .rev()
                        .take(6)
                        .enumerate()
                        .map(|(rel, con)| format!("rel{rel}@{:?}", con.node))
                        .collect::<Vec<_>>()
                        .join(" | ");
                    eprintln!("monoize saw source prim0 span={key} env={rels}");
                }
            }
            Located::new(Exp::Prim(p.clone()), loc)
        }
        CE::Rel(n) => Located::new(Exp::Rel(*n), loc),
        CE::Named(n) => Located::new(Exp::Named(*n), loc),

        // --------------- Constructors ---------------
        CE::Constructor(dk, pc, targs, opt_e) => {
            if targs.is_empty() {
                let me = opt_e
                    .as_ref()
                    .map(|e| Box::new(mono_exp(env, fm, e, settings)));
                Located::new(Exp::Con(*dk, mono_pat_con(pc), me), loc)
            } else if targs.len() == 1 {
                match (pc, opt_e) {
                    (
                        CPC::Ffi {
                            module, datatyp, ..
                        },
                        _,
                    ) if module == "Basis" && datatyp == "list" => {
                        let mut dtmap = HashMap::new();
                        let inner_t = mono_type(env, &mut dtmap, &targs[0]);
                        let lt = listify(inner_t, &loc);
                        match opt_e {
                            None => Located::new(Exp::None(lt), loc),
                            Some(e) => {
                                let e = mono_exp(env, fm, e, settings);
                                Located::new(Exp::Some(lt, Box::new(e)), loc)
                            }
                        }
                    }
                    (_, None) => {
                        let mut dtmap = HashMap::new();
                        let t = mono_type(env, &mut dtmap, &targs[0]);
                        Located::new(Exp::None(t), loc)
                    }
                    (_, Some(e)) => {
                        let mut dtmap = HashMap::new();
                        let t = mono_type(env, &mut dtmap, &targs[0]);
                        let me = mono_exp(env, fm, e, settings);
                        Located::new(Exp::Some(t, Box::new(me)), loc)
                    }
                }
            } else {
                // Polymorphic — error
                zero_exp(&loc, "constructor-polymorphic-arity")
            }
        }

        // --------------- FFI ---------------
        CE::Ffi(m, x) => {
            // For Basis type class concrete instances, generate implementations.
            if m == "Basis" {
                if let Some(e) = mono_basis_ffi(x, &loc) {
                    return e;
                }
            }
            Located::new(Exp::Ffi(m.clone(), x.clone()), loc)
        }
        CE::FfiApp(m, x, args) => {
            if m == "Basis" {
                match x.as_str() {
                    "sql_limit" if args.len() == 1 => {
                        let mut dtmap = HashMap::new();
                        let e = mono_exp(env, fm, &args[0].0, settings);
                        let t = mono_type(env, &mut dtmap, &args[0].1);
                        return make_strcat_list(
                            vec![
                                str_n(" LIMIT ", &loc),
                                Located::new(
                                    Exp::FfiApp("Basis".into(), "sqlifyInt".into(), vec![(e, t)]),
                                    loc.clone(),
                                ),
                            ],
                            &loc,
                        );
                    }
                    "sql_offset" if args.len() == 1 => {
                        let mut dtmap = HashMap::new();
                        let e = mono_exp(env, fm, &args[0].0, settings);
                        let t = mono_type(env, &mut dtmap, &args[0].1);
                        return make_strcat_list(
                            vec![
                                str_n(" OFFSET ", &loc),
                                Located::new(
                                    Exp::FfiApp("Basis".into(), "sqlifyInt".into(), vec![(e, t)]),
                                    loc.clone(),
                                ),
                            ],
                            &loc,
                        );
                    }
                    "dml" if args.len() == 1 => {
                        let e = mono_exp(env, fm, &args[0].0, settings);
                        let disc = string_type(&loc);
                        let unit_t = unit_typ(&loc);
                        return Located::new(
                            Exp::Case(
                                Box::new(e),
                                vec![
                                    (
                                        Located::new(
                                            Pat::Prim(Prim::String(
                                                crate::primitives::StringMode::Normal,
                                                String::new(),
                                            )),
                                            loc.clone(),
                                        ),
                                        unit_exp(&loc),
                                    ),
                                    (
                                        Located::new(
                                            Pat::Var("cmd".into(), disc.clone()),
                                            loc.clone(),
                                        ),
                                        Located::new(
                                            Exp::Dml(
                                                Box::new(Located::new(Exp::Rel(0), loc.clone())),
                                                FailureMode::Error,
                                            ),
                                            loc.clone(),
                                        ),
                                    ),
                                ],
                                CaseMeta {
                                    disc,
                                    result: unit_t,
                                },
                            ),
                            loc,
                        );
                    }
                    "tryDml" if args.len() == 1 => {
                        let e = mono_exp(env, fm, &args[0].0, settings);
                        let disc = string_type(&loc);
                        let result_t = unit_typ(&loc);
                        return Located::new(
                            Exp::Case(
                                Box::new(e),
                                vec![
                                    (
                                        Located::new(
                                            Pat::Prim(Prim::String(
                                                crate::primitives::StringMode::Normal,
                                                String::new(),
                                            )),
                                            loc.clone(),
                                        ),
                                        unit_exp(&loc),
                                    ),
                                    (
                                        Located::new(
                                            Pat::Var("cmd".into(), disc.clone()),
                                            loc.clone(),
                                        ),
                                        Located::new(
                                            Exp::Dml(
                                                Box::new(Located::new(Exp::Rel(0), loc.clone())),
                                                FailureMode::None,
                                            ),
                                            loc.clone(),
                                        ),
                                    ),
                                ],
                                CaseMeta {
                                    disc,
                                    result: result_t,
                                },
                            ),
                            loc,
                        );
                    }
                    "nextval" if args.len() == 1 => {
                        let e = mono_exp(env, fm, &args[0].0, settings);
                        return Located::new(Exp::Nextval(Box::new(e)), loc);
                    }
                    "setval" if args.len() == 2 => {
                        let e1 = mono_exp(env, fm, &args[0].0, settings);
                        let e2 = mono_exp(env, fm, &args[1].0, settings);
                        return Located::new(Exp::Setval(Box::new(e1), Box::new(e2)), loc);
                    }
                    _ => {}
                }
            }
            let margs: Vec<_> = args
                .iter()
                .map(|(e, t)| {
                    let mut dtmap = HashMap::new();
                    (
                        mono_exp(env, fm, e, settings),
                        mono_type(env, &mut dtmap, t),
                    )
                })
                .collect();
            Located::new(Exp::FfiApp(m.clone(), x.clone(), margs), loc)
        }

        // --------------- Application / Abstraction ---------------
        CE::App(_, _) => {
            let reduced = crate::core::local_reduction::reduce_exp(exp.clone());
            if !matches!(reduced.node, CE::App(_, _)) {
                return mono_exp(env, fm, &reduced, settings);
            }
            let exp = &reduced;
            let loc = exp.span.clone();
            if loc.file.ends_with("/lib/ur/top.ur")
                && loc.first.line == 156
                && loc.first.col == 11
                && should_log_once("mono-top-156-app")
            {
                eprintln!("mono top156 reduced app = {:?}", exp.node);
            }
            let mut vargs: Vec<&LocatedExpression> = vec![];
            let mut targs: Vec<&LocatedConstructor> = vec![];
            let head_e = peel_spine(exp, &mut vargs, &mut targs);
            let basis_head = match &head_e.node {
                CE::Ffi(module, name) if module == "Basis" => Some(name.clone()),
                CE::Named(n) => env
                    .lookup_e_named(*n)
                    .and_then(|(name, _, src)| named_builtin_head(name, src)),
                _ => None,
            };
            if let Some(x) = basis_head {
                match x.as_str() {
                    "join" if vargs.len() >= 4 => {
                        // join has 2 constraint proof args + 2 xml args = 4 minimum
                        let n = vargs.len();
                        let xml1 = mono_exp(env, fm, vargs[n - 2], settings);
                        let xml2 = mono_exp(env, fm, vargs[n - 1], settings);
                        return Located::new(Exp::Strcat(Box::new(xml1), Box::new(xml2)), loc);
                    }
                    "cdata" if !vargs.is_empty() => {
                        // cdata has 0 proof args + 1 string arg
                        let str_e = mono_exp(env, fm, vargs[vargs.len() - 1], settings);
                        let str_t =
                            Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
                        return Located::new(
                            Exp::FfiApp(
                                "Basis".into(),
                                "htmlifyString".into(),
                                vec![(str_e, str_t)],
                            ),
                            loc,
                        );
                    }
                    "form" if vargs.len() >= 3 => {
                        let n = vargs.len();
                        return desugar_form(
                            env,
                            fm,
                            settings,
                            &loc,
                            vargs[n - 3], // id
                            vargs[n - 2], // class
                            vargs[n - 1], // xml
                        );
                    }
                    "tag" if vargs.len() >= 10 => {
                        // vargs: [proof0, proof1, proof2, class, dynClass, style,
                        //         dynStyle, attrs, tagFn, xml]
                        // Use last 7 value args (skip 3 proof args at front).
                        let n = vargs.len();
                        return desugar_tag(
                            env,
                            fm,
                            settings,
                            &loc,
                            &targs,
                            vargs[n - 7], // class  (css_class)
                            vargs[n - 6], // dynClass
                            vargs[n - 5], // style  (css_style)
                            vargs[n - 4], // dynStyle
                            vargs[n - 3], // attrs
                            vargs[n - 2], // tag function (e.g. head{})
                            vargs[n - 1], // xml content
                        );
                    }
                    _ => {}
                }
                if let Some(result) =
                    mono_basis_full_app(env, fm, settings, exp, &x, &targs, &vargs, &loc)
                {
                    return result;
                }
            }
            // Normal App: recursively process both sides.
            // Re-extract e1/e2 since we already have them in the outer match.
            match &exp.node {
                CE::App(e1, e2) => {
                    let me1 = mono_exp(env, fm, e1, settings);
                    let synthetic_constraint_arg = is_synthetic_constraint_prim0(e2);
                    let me2 = if synthetic_constraint_arg {
                        unit_exp(&e2.span)
                    } else {
                        mono_exp(env, fm, e2, settings)
                    };
                    let out = match (&me1.node, synthetic_constraint_arg) {
                        (Exp::Abs(_, _, _, body), _) => {
                            crate::monomorphized::environment::sub_exp_in_exp(0, &me2, body)
                        }
                        (_, true) => me1,
                        _ => Located::new(Exp::App(Box::new(me1), Box::new(me2)), loc.clone()),
                    };
                    if loc.file.ends_with("/lib/ur/top.ur")
                        && loc.first.line == 156
                        && loc.first.col == 11
                        && should_log_once("mono-top-156-out")
                    {
                        eprintln!("mono top156 out = {:?}", out.node);
                    }
                    erase_synthetic_unit_abs(out)
                }
                _ => zero_exp(&loc, "app-nonapp-fallback"),
            }
        }
        CE::Abs(x, dom, ran, body) => {
            let mut dtmap = HashMap::new();
            let mdom = mono_type(env, &mut dtmap, dom);
            let mran = mono_type(env, &mut dtmap, ran);
            let env2 = env.clone().push_e_rel(dom.clone());
            let mbody = mono_exp(&env2, fm, body, settings);
            erase_synthetic_unit_abs(Located::new(
                Exp::Abs(x.clone(), mdom, mran, Box::new(mbody)),
                loc,
            ))
        }

        // Type application: ECApp (e, _) — strip the type arg, or desugar type class instances.
        CE::CApp(_, _) => {
            let reduced = crate::core::local_reduction::reduce_exp(exp.clone());
            if !matches!(reduced.node, CE::CApp(_, _)) {
                return mono_exp(env, fm, &reduced, settings);
            }

            let (head, targs) = peel_capp(&reduced);
            let basis_head = match &head.node {
                CE::Ffi(module, name) if module == "Basis" => Some(name.clone()),
                CE::Named(n) => env
                    .lookup_e_named(*n)
                    .and_then(|(name, _, src)| named_builtin_head(name, src)),
                _ => None,
            };
            if let Some(x) = basis_head {
                if let Some(result) = mono_basis_capp(env, settings, &x, &targs, &loc) {
                    return result;
                }
            }
            // Fall through: translate head and strip all type args.
            mono_exp(env, fm, head, settings)
        }

        // Type/kind abstraction: erase at runtime once any remaining local beta-reduction
        // has had a chance to fire in surrounding CApp/KApp nodes.
        CE::CAbs(_, _, body) => mono_exp(env, fm, body, settings),
        CE::KAbs(_, body) => mono_exp(env, fm, body, settings),
        CE::KApp(inner, _) => mono_exp(env, fm, inner, settings),

        // --------------- Records ---------------
        CE::Record(xets) => {
            let mut mxets: Vec<(String, LocExp, LocTyp)> = xets
                .iter()
                .map(|(name_con, e, t)| {
                    let mut dtmap = HashMap::new();
                    (
                        mono_name(name_con),
                        mono_exp(env, fm, e, settings),
                        mono_type(env, &mut dtmap, t),
                    )
                })
                .collect();
            mxets.sort_by(|(a, _, _), (b, _, _)| a.cmp(b));
            Located::new(Exp::Record(mxets), loc)
        }
        CE::Field(e, x, _) => {
            let me = mono_exp(env, fm, e, settings);
            Located::new(Exp::Field(Box::new(me), mono_name(x)), loc)
        }
        CE::Concat(left, left_row, right, right_row) => {
            let mleft = mono_exp(env, fm, left, settings);
            let mright = mono_exp(env, fm, right, settings);
            match (&mleft.node, &mright.node) {
                (Exp::Record(left_fields), Exp::Record(right_fields)) => {
                    let mut fields = left_fields.clone();
                    fields.extend(right_fields.clone());
                    fields.sort_by(|(a, _, _), (b, _, _)| a.cmp(b));
                    Located::new(Exp::Record(fields), loc)
                }
                _ => {
                    let mut dtmap = HashMap::new();
                    let left_fields = mono_row_fields(env, &mut dtmap, left_row)
                        .or_else(|| mono_record_fields_from_exp_type(env, &mut dtmap, left));
                    let right_fields = mono_row_fields(env, &mut dtmap, right_row)
                        .or_else(|| mono_record_fields_from_exp_type(env, &mut dtmap, right));

                    match (left_fields, right_fields) {
                        (Some(left_fields), Some(right_fields)) => {
                            let mut fields = mono_project_row_parts(&mleft, &left_fields, &loc);
                            fields.extend(mono_project_row_parts(&mright, &right_fields, &loc));
                            fields.sort_by(|(a, _, _), (b, _, _)| a.cmp(b));
                            Located::new(Exp::Record(fields), loc)
                        }
                        (Some(known_fields), None) => {
                            let mut fields = mono_project_row_parts(&mleft, &known_fields, &loc);
                            fields.sort_by(|(a, _, _), (b, _, _)| a.cmp(b));
                            let known_record = Located::new(Exp::Record(fields), loc.clone());
                            Located::new(Exp::App(Box::new(known_record), Box::new(mright)), loc)
                        }
                        (None, Some(known_fields)) => {
                            let mut fields = mono_project_row_parts(&mright, &known_fields, &loc);
                            fields.sort_by(|(a, _, _), (b, _, _)| a.cmp(b));
                            let known_record = Located::new(Exp::Record(fields), loc.clone());
                            Located::new(Exp::App(Box::new(known_record), Box::new(mleft)), loc)
                        }
                        (None, None) => zero_exp(&loc, "concat-both-rows-unknown"),
                    }
                }
            }
        }
        CE::Cut(exp, name, meta) => {
            let me = mono_exp(env, fm, exp, settings);
            let field_name = mono_name(name);
            if let Exp::Record(fields) = &me.node {
                let filtered = fields
                    .iter()
                    .filter(|(name, _, _)| name != &field_name)
                    .cloned()
                    .collect();
                return Located::new(Exp::Record(filtered), loc);
            }

            let mut dtmap = HashMap::new();
            let rest_fields = mono_row_fields(env, &mut dtmap, &meta.rest).or_else(|| {
                mono_record_fields_from_exp_type(env, &mut dtmap, exp).map(|fields| {
                    fields
                        .into_iter()
                        .filter(|(name, _)| name != &field_name)
                        .collect::<Vec<_>>()
                })
            });
            let Some(rest_fields) = rest_fields else {
                return zero_exp(&loc, "cut-rest-row-unknown");
            };
            let mut fields = mono_project_row_parts(&me, &rest_fields, &loc);
            fields.sort_by(|(a, _, _), (b, _, _)| a.cmp(b));
            Located::new(Exp::Record(fields), loc)
        }
        CE::CutMulti(exp, names, meta) => {
            let me = mono_exp(env, fm, exp, settings);
            let mut dtmap = HashMap::new();
            let cut_names = mono_row_fields(env, &mut dtmap, names)
                .map(|fields| fields.into_iter().map(|(name, _)| name).collect::<Vec<_>>());

            if let (Exp::Record(fields), Some(cut_names)) = (&me.node, cut_names.as_ref()) {
                let filtered = fields
                    .iter()
                    .filter(|(name, _, _)| !cut_names.contains(name))
                    .cloned()
                    .collect();
                return Located::new(Exp::Record(filtered), loc);
            }

            let rest_fields = mono_row_fields(env, &mut dtmap, &meta.rest).or_else(|| {
                mono_record_fields_from_exp_type(env, &mut dtmap, exp).map(|fields| {
                    fields
                        .into_iter()
                        .filter(|(name, _)| {
                            !cut_names
                                .as_ref()
                                .is_some_and(|cut_names| cut_names.contains(name))
                        })
                        .collect::<Vec<_>>()
                })
            });
            let Some(rest_fields) = rest_fields else {
                return zero_exp(&loc, "cutmulti-rest-row-unknown");
            };
            let mut fields = mono_project_row_parts(&me, &rest_fields, &loc);
            fields.sort_by(|(a, _, _), (b, _, _)| a.cmp(b));
            Located::new(Exp::Record(fields), loc)
        }

        // --------------- Case ---------------
        CE::Case(e, arms, meta) => {
            let mut dtmap = HashMap::new();
            let me = mono_exp(env, fm, e, settings);
            let marms: Vec<(LocPat, LocExp)> = arms
                .iter()
                .map(|(p, arm_e)| {
                    (
                        mono_pat(env, &mut dtmap, p),
                        mono_exp(env, fm, arm_e, settings),
                    )
                })
                .collect();
            let disc = mono_type(env, &mut dtmap, &meta.disc);
            let result = mono_type(env, &mut dtmap, &meta.result);
            Located::new(
                Exp::Case(Box::new(me), marms, CaseMeta { disc, result }),
                loc,
            )
        }

        // --------------- Write ---------------
        CE::Write(e) => {
            // EWrite e → EAbs("_", unit, unit, EWrite(lift e))
            let me = mono_exp(env, fm, e, settings);
            let un = unit_typ(&loc);
            let lifted = lift_exp_in_exp(0, me);
            Located::new(
                Exp::Abs(
                    "_".into(),
                    un.clone(),
                    un.clone(),
                    Box::new(Located::new(Exp::Write(Box::new(lifted)), loc.clone())),
                ),
                loc,
            )
        }

        // --------------- Closure ---------------
        CE::Closure(n, envs) => {
            let menvs: Vec<LocExp> = envs
                .iter()
                .map(|e| mono_exp(env, fm, e, settings))
                .collect();
            Located::new(Exp::Closure(*n, menvs), loc)
        }

        // --------------- Let ---------------
        CE::Let(x, t, e1, e2) => {
            let mut dtmap = HashMap::new();
            let mt = mono_type(env, &mut dtmap, t);
            let me1 = mono_exp(env, fm, e1, settings);
            let env2 = env.clone().push_e_rel(t.clone());
            let me2 = mono_exp(&env2, fm, e2, settings);
            Located::new(Exp::Let(x.clone(), mt, Box::new(me1), Box::new(me2)), loc)
        }

        // --------------- ServerCall ---------------
        CE::ServerCall(n, args, result_t, fmode) => {
            let mut dtmap = HashMap::new();
            let mt = mono_type(env, &mut dtmap, result_t);
            let margs: Vec<LocExp> = args
                .iter()
                .map(|e| mono_exp(env, fm, e, settings))
                .collect();

            // Get the function name/path from the env
            let name = env
                .lookup_e_named(*n)
                .map(|(_, _, s)| s.clone())
                .unwrap_or_default();

            // Build URL-encoded call string: name/arg1/arg2/...
            // (simplified: just pass args as Mono EServerCall)
            let call = if margs.is_empty() {
                str_exp(&name, &loc)
            } else {
                margs.iter().fold(str_exp(&name, &loc), |acc, arg| {
                    let slash = str_exp("/", &loc);
                    let cat1 =
                        Located::new(Exp::Strcat(Box::new(acc), Box::new(slash)), loc.clone());
                    Located::new(
                        Exp::Strcat(Box::new(cat1), Box::new(arg.clone())),
                        loc.clone(),
                    )
                })
            };

            use crate::export::Effect;
            let un = unit_typ(&loc);
            let e = Located::new(
                Exp::ServerCall(Box::new(call), mt, Effect::ReadOnly, *fmode),
                loc.clone(),
            );
            let e = lift_exp_in_exp(0, e);
            Located::new(Exp::Abs("_".into(), un.clone(), un, Box::new(e)), loc)
        }
    }
}

// ---------------------------------------------------------------------------
// Declaration translation: mono_decl
// ---------------------------------------------------------------------------

/// Translate a Core declaration to zero or more Mono declarations.
///
/// Returns `None` if the declaration should be dropped (e.g. DCon).
/// Returns `Some((new_env, mono_decls))` on success.
///
/// Mirrors `monoDecl` in `monoize.sml`.
fn mono_decl(
    env: Env,
    fm: &mut Fm,
    decl: &LocatedDeclaration,
    settings: &Settings,
) -> Option<(Env, Vec<LocDecl>)> {
    let loc = decl.span.clone();
    match &decl.node {
        // Type synonym — disappears in Mono
        CD::Constructor(_, _, _, _) => None,

        // Datatype — translate constructors
        CD::Datatype(dts) => {
            // Extend env before translating constructor types (for mutual recursion)
            let env2 = env.clone().decl_binds(decl);
            let mut dtmap = HashMap::new();

            let mono_dts: Vec<MonoDatatypeDecl> = dts
                .iter()
                .filter_map(|dt| {
                    if !dt.params.is_empty() {
                        return None; // Polymorphic — skip
                    }
                    if dt.name == "list" {
                        return None; // Built-in in Mono
                    }
                    let constrs: Vec<_> = dt
                        .constrs
                        .iter()
                        .map(|(x, n, to)| {
                            (
                                x.clone(),
                                *n,
                                to.as_ref().map(|t| mono_type(&env2, &mut dtmap, t)),
                            )
                        })
                        .collect();
                    Some(MonoDatatypeDecl {
                        name: dt.name.clone(),
                        id: dt.id,
                        constrs,
                    })
                })
                .collect();

            if mono_dts.is_empty() {
                None
            } else {
                let d = Located::new(Decl::Datatype(mono_dts), loc);
                Some((env2, vec![d]))
            }
        }

        // Value binding
        CD::Val(x, n, t, e, s) => {
            let mut dtmap = HashMap::new();
            let me = mono_exp(&env, fm, e, settings);
            let mt = mono_type(&env, &mut dtmap, t);
            let env2 = env.push_e_named(x.clone(), *n, t.clone(), s.clone());
            let mut out = fm.drain_decls(&loc);
            out.push(Located::new(
                Decl::Val(x.clone(), *n, mt, me, s.clone()),
                loc,
            ));
            Some((env2, out))
        }

        // Mutually recursive bindings
        CD::ValRec(vis) => {
            let vis: Vec<_> = vis
                .iter()
                .map(|(x, n, t, e, s)| {
                    (
                        x.clone(),
                        *n,
                        t.clone(),
                        maybe_transaction_core_exp(t, e, &loc).unwrap_or_else(|| e.clone()),
                        s.clone(),
                    )
                })
                .collect();

            let env2 = vis.iter().fold(env, |env, (x, n, t, _, s)| {
                env.push_e_named(x.clone(), *n, t.clone(), s.clone())
            });
            let mut dtmap = HashMap::new();

            let mvis: Vec<_> = vis
                .iter()
                .map(|(x, n, t, e, s)| {
                    let mt = mono_type(&env2, &mut dtmap, t);
                    let me = mono_exp(&env2, fm, e, settings);
                    (x.clone(), *n, mt, me, s.clone())
                })
                .collect();

            let mut out = fm.drain_decls(&loc);
            out.push(Located::new(Decl::ValRec(mvis), loc));
            Some((env2, out))
        }

        // Export
        CD::Export(ek, n, has_state) => {
            let (_name, typ, src) = env
                .lookup_e_named(*n)
                .map(|(nm, t, s)| (nm.clone(), t.clone(), s.clone()))
                .unwrap_or((
                    "?".into(),
                    Located::new(CC::Ffi("Basis".into(), "unit".into()), loc.clone()),
                    "?".into(),
                ));

            let mut dtmap = HashMap::new();
            let (arg_types, ran) = unwind_type(&env, &mut dtmap, &typ, &loc);
            let d = Located::new(
                Decl::Export(*ek, src.clone(), *n, arg_types, ran, *has_state),
                loc,
            );
            Some((env, vec![d]))
        }

        // Table
        CD::Table {
            sql_name,
            id,
            con,
            sql_con,
            exp: pe,
            pk_con: _,
            pk_exp: ce,
            unique_con: _,
        } => {
            let mut dtmap = HashMap::new();
            let s = settings.mangle_sql_table(sql_con);
            let e_name = str_exp(&s, &loc);
            let t = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());

            let xts: Vec<(String, LocTyp)> = match &con.node {
                CC::Record(_, fields) => fields
                    .iter()
                    .map(|(name_con, col_t)| {
                        (mono_name(name_con), mono_type(&env, &mut dtmap, col_t))
                    })
                    .collect(),
                _ => Vec::new(),
            };

            let mpe = mono_exp(&env, fm, pe, settings);
            let ce = mono_exp(&env, fm, ce, settings);

            let env2 = env.push_e_named(
                sql_name.clone(),
                *id,
                Located::new(CC::Ffi("Basis".into(), "string".into()), loc.clone()),
                s.clone(),
            );
            let mut out = fm.drain_decls(&loc);
            out.push(Located::new(
                Decl::Table(s.clone(), xts, mpe, ce),
                loc.clone(),
            ));
            out.push(Located::new(
                Decl::Val(sql_name.clone(), *id, t, e_name, s),
                loc,
            ));
            Some((env2, out))
        }

        // Sequence
        CD::Sequence(x, n, sql_name) => {
            let s = settings.mangle_sql(sql_name);
            let t = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
            let e = str_exp(&s, &loc);
            let env2 = env.push_e_named(
                x.clone(),
                *n,
                Located::new(CC::Ffi("Basis".into(), "string".into()), loc.clone()),
                s.clone(),
            );
            let out = vec![
                Located::new(Decl::Sequence(s.clone()), loc.clone()),
                Located::new(Decl::Val(x.clone(), *n, t, e, s), loc),
            ];
            Some((env2, out))
        }

        // View
        CD::View(x, n, sql_name, e, con) => {
            let mut dtmap = HashMap::new();
            let s = settings.mangle_sql_table(sql_name);
            let e_name = str_exp(&s, &loc);
            let t = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());

            let xts: Vec<(String, LocTyp)> = match &con.node {
                CC::Record(_, fields) => fields
                    .iter()
                    .map(|(nm, ct)| (mono_name(nm), mono_type(&env, &mut dtmap, ct)))
                    .collect(),
                _ => Vec::new(),
            };

            let me = mono_exp(&env, fm, e, settings);
            let view_e = Located::new(
                Exp::FfiApp("Basis".into(), "viewify".into(), vec![(me, t.clone())]),
                loc.clone(),
            );

            let env2 = env.push_e_named(
                x.clone(),
                *n,
                Located::new(CC::Ffi("Basis".into(), "string".into()), loc.clone()),
                s.clone(),
            );
            let mut out = fm.drain_decls(&loc);
            out.push(Located::new(
                Decl::View(s.clone(), xts, view_e),
                loc.clone(),
            ));
            out.push(Located::new(Decl::Val(x.clone(), *n, t, e_name, s), loc));
            Some((env2, out))
        }

        // Index
        CD::Index(tab_e, cols_e) => {
            let tab_path = match &tab_e.node {
                CE::Named(n) => env
                    .lookup_e_named(*n)
                    .map(|(_, _, s)| s.clone())
                    .unwrap_or_default(),
                _ => return None,
            };
            let cols: Vec<(String, mono::IndexMode)> = match &cols_e.node {
                CE::Record(xms) => xms
                    .iter()
                    .filter_map(|(name_con, mode_e, _)| {
                        let name = mono_name(name_con);
                        let mode = extract_index_mode(mode_e)?;
                        Some((name, mode))
                    })
                    .collect(),
                _ => return None,
            };
            let d = Located::new(Decl::Index(tab_path, cols), loc);
            Some((env, vec![d]))
        }

        // Database — handled specially at top level
        CD::Database(_) => None,

        // Cookie
        CD::Cookie(x, n, _, s) => {
            let t = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
            let e = str_exp(s, &loc);
            let env2 = env.push_e_named(
                x.clone(),
                *n,
                Located::new(CC::Ffi("Basis".into(), "string".into()), loc.clone()),
                s.clone(),
            );
            let out = vec![
                Located::new(Decl::Cookie(s.clone()), loc.clone()),
                Located::new(Decl::Val(x.clone(), *n, t, e, s.clone()), loc),
            ];
            Some((env2, out))
        }

        // Style
        CD::Style(x, n, s) => {
            let t = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
            let e = Located::new(
                Exp::Prim(Prim::String(crate::primitives::StringMode::Html, s.clone())),
                loc.clone(),
            );
            let env2 = env.push_e_named(
                x.clone(),
                *n,
                Located::new(CC::Ffi("Basis".into(), "string".into()), loc.clone()),
                s.clone(),
            );
            let out = vec![
                Located::new(Decl::Style(s.clone()), loc.clone()),
                Located::new(Decl::Val(x.clone(), *n, t, e, s.clone()), loc),
            ];
            Some((env2, out))
        }

        // Task
        CD::Task(e1, e2) => {
            let me1 = mono_exp(&env, fm, e1, settings);
            let me2 = mono_exp(&env, fm, e2, settings);

            let un = unit_typ(&loc);
            let e2_wrapped = Located::new(
                Exp::Abs(
                    "$x".into(),
                    un.clone(),
                    Located::new(
                        Typ::Fun(Box::new(un.clone()), Box::new(un.clone())),
                        loc.clone(),
                    ),
                    Box::new(Located::new(
                        Exp::Abs(
                            "$y".into(),
                            un.clone(),
                            un.clone(),
                            Box::new(Located::new(
                                Exp::App(
                                    Box::new(Located::new(
                                        Exp::App(
                                            Box::new(me2.clone()),
                                            Box::new(Located::new(Exp::Rel(1), loc.clone())),
                                        ),
                                        loc.clone(),
                                    )),
                                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                                ),
                                loc.clone(),
                            )),
                        ),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            );

            let mut out = fm.drain_decls(&loc);
            out.push(Located::new(Decl::Task(me1, e2_wrapped), loc));
            Some((env, out))
        }

        // Policy
        CD::Policy(e) => {
            let policies = extract_policies(&env, fm, e, &loc, settings);
            let mut out = fm.drain_decls(&loc);
            out.extend(policies);
            Some((env, out))
        }

        // OnError
        CD::OnError(n) => {
            let d = Located::new(Decl::OnError(*n), loc);
            Some((env, vec![d]))
        }
    }
}

// ---------------------------------------------------------------------------
// Helpers for mono_decl
// ---------------------------------------------------------------------------

/// Unwind a function type into `(arg_types, return_type)`.
fn unwind_type(
    env: &Env,
    dtmap: &mut HashMap<usize, DatatypeRef>,
    t: &LocatedConstructor,
    loc: &Span,
) -> (Vec<LocTyp>, LocTyp) {
    fn go(
        env: &Env,
        dtmap: &mut HashMap<usize, DatatypeRef>,
        t: &LocatedConstructor,
        loc: &Span,
        args: &mut Vec<LocTyp>,
    ) -> LocTyp {
        match &t.node {
            CC::TFun(dom, ran) => {
                args.push(mono_type(env, dtmap, dom));
                go(env, dtmap, ran, loc, args)
            }
            CC::App(f, arg) => match &f.node {
                CC::Ffi(m, x) if m == "Basis" && x == "transaction" => {
                    // transaction t → treat as returning t (with unit arg stripped)
                    args.push(Located::new(Typ::Record(Vec::new()), loc.clone()));
                    mono_type(env, dtmap, arg)
                }
                _ => mono_type(env, dtmap, t),
            },
            _ => mono_type(env, dtmap, t),
        }
    }
    let mut args = Vec::new();
    let ran = go(env, dtmap, t, loc, &mut args);
    (args, ran)
}

fn extract_index_mode(e: &LocatedExpression) -> Option<mono::IndexMode> {
    // Look at the head of CApp/EFfi chains
    fn head(e: &LocatedExpression) -> Option<(&str, &str)> {
        match &e.node {
            CE::Ffi(m, x) => Some((m.as_str(), x.as_str())),
            CE::CApp(inner, _) => head(inner),
            CE::App(inner, _) => head(inner),
            _ => None,
        }
    }
    match head(e) {
        Some(("Basis", "equality")) => Some(mono::IndexMode::Equality),
        Some(("Basis", "trigram")) => Some(mono::IndexMode::Trigram),
        Some(("Basis", "skipped")) => Some(mono::IndexMode::Skipped),
        _ => None,
    }
}

fn extract_policies(
    env: &Env,
    fm: &mut Fm,
    e: &LocatedExpression,
    loc: &Span,
    settings: &Settings,
) -> Vec<LocDecl> {
    match &e.node {
        CE::FfiApp(m, x, args) if m == "Basis" && x == "also" => {
            if let [(e1, _), (e2, _)] = args.as_slice() {
                let mut p1 = extract_policies(env, fm, e1, loc, settings);
                let p2 = extract_policies(env, fm, e2, loc, settings);
                p1.extend(p2);
                return p1;
            }
            Vec::new()
        }
        _ => {
            let (inner_e, make): (_, fn(LocExp) -> Policy) = match &e.node {
                CE::App(f, arg) => match &f.node {
                    CE::CApp(ff, _) => match &ff.node {
                        CE::CApp(fff, _) => match &fff.node {
                            CE::Ffi(m, x) if m == "Basis" => match x.as_str() {
                                "sendClient" => (arg.as_ref(), |e| Policy::Client(e)),
                                "mayInsert" => (arg.as_ref(), |e| Policy::Insert(e)),
                                "mayDelete" => (arg.as_ref(), |e| Policy::Delete(e)),
                                "mayUpdate" => (arg.as_ref(), |e| Policy::Update(e)),
                                _ => return Vec::new(),
                            },
                            _ => return Vec::new(),
                        },
                        _ => return Vec::new(),
                    },
                    _ => return Vec::new(),
                },
                CE::FfiApp(m, x, args) if m == "Basis" && x == "sendOwnIds" => {
                    if let [(arg, _)] = args.as_slice() {
                        let me = mono_exp(env, fm, arg, settings);
                        return vec![Located::new(
                            Decl::Policy(Policy::Sequence(me)),
                            loc.clone(),
                        )];
                    }
                    return Vec::new();
                }
                _ => return Vec::new(),
            };
            let me = mono_exp(env, fm, inner_e, settings);
            vec![Located::new(Decl::Policy(make(me)), loc.clone())]
        }
    }
}

// ---------------------------------------------------------------------------
// Max name computation
// ---------------------------------------------------------------------------

/// Compute the maximum named id used in a Core file.
fn max_name_in_file(file: &core::File) -> usize {
    let mut max = 0usize;
    for decl in file {
        max_name_in_decl(&decl.node, &mut max);
    }
    max
}

fn max_name_in_decl(d: &core::Declaration, max: &mut usize) {
    match d {
        CD::Constructor(_, n, _, _)
        | CD::Sequence(_, n, _)
        | CD::Cookie(_, n, _, _)
        | CD::Style(_, n, _)
        | CD::OnError(n) => update(max, *n),
        CD::Datatype(dts) => {
            for dt in dts {
                update(max, dt.id);
                for (_, cn, _) in &dt.constrs {
                    update(max, *cn);
                }
            }
        }
        CD::Val(_, n, _, _, _) => update(max, *n),
        CD::ValRec(vis) => {
            for (_, n, _, _, _) in vis {
                update(max, *n);
            }
        }
        CD::Export(_, n, _) => update(max, *n),
        CD::Table { id, .. } | CD::View(_, id, _, _, _) => update(max, *id),
        _ => {}
    }
}

fn update(max: &mut usize, n: usize) {
    if n > *max {
        *max = n;
    }
}

// ---------------------------------------------------------------------------
// Public entry point: monoize
// ---------------------------------------------------------------------------

/// Convert a Core file to a Mono file.
///
/// Mirrors `monoize` in `monoize.sml`.
pub fn monoize(
    file: core::File,
    settings: &Settings,
    _errors: &mut crate::error_types::ErrorReporter,
) -> Option<mono::File> {
    reset_monoize_caches();
    let mname = max_name_in_file(&file) + 1;
    let mut env = Env::empty();
    let mut fm = Fm::empty(mname);
    let mut decls: Vec<LocDecl> = Vec::new();

    for core_decl in &file {
        // Handle DDatabase specially (generates expunger + initializer)
        if let CD::Database(name) = &core_decl.node {
            let nexp = fm.fresh_name();
            let nini = fm.fresh_name();
            let loc = core_decl.span.clone();

            let un = unit_typ(&loc);
            let client_t = Located::new(Typ::Ffi("Basis".into(), "client".into()), loc.clone());

            let expunger_fn = Located::new(
                Exp::Abs(
                    "cli".into(),
                    client_t.clone(),
                    un.clone(),
                    Box::new(unit_exp(&loc)),
                ),
                loc.clone(),
            );
            let init_fn = Located::new(
                Exp::Abs("_".into(), un.clone(), un.clone(), Box::new(unit_exp(&loc))),
                loc.clone(),
            );

            decls.push(Located::new(
                Decl::Database {
                    name: name.clone(),
                    expunge: nexp,
                    initialize: nini,
                    uses_similar: false,
                },
                loc.clone(),
            ));
            decls.push(Located::new(
                Decl::Val(
                    "expunger".into(),
                    nexp,
                    Located::new(
                        Typ::Fun(Box::new(client_t), Box::new(un.clone())),
                        loc.clone(),
                    ),
                    expunger_fn,
                    "expunger".into(),
                ),
                loc.clone(),
            ));
            decls.push(Located::new(
                Decl::Val(
                    "initializer".into(),
                    nini,
                    Located::new(
                        Typ::Fun(Box::new(un.clone()), Box::new(un.clone())),
                        loc.clone(),
                    ),
                    init_fn,
                    "initializer".into(),
                ),
                loc.clone(),
            ));
            continue;
        }

        match mono_decl(env.clone(), &mut fm, core_decl, settings) {
            None => {
                env = env.decl_binds(core_decl);
            }
            Some((new_env, ds)) => {
                decls.extend(ds);
                env = new_env;
            }
        }
    }

    Some((decls, Vec::new()))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::Constructor as CC;
    use crate::core::Expression as CE;
    use anyhow::Context as _; // .with_context() on Result in tests

    fn loc() -> Span {
        Span::dummy()
    }

    #[test]
    fn empty_file_monoizes_to_empty() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let settings = Settings::default();
        let mut errors = crate::error_types::ErrorReporter::new();
        let result = monoize(Vec::new(), &settings, &mut errors);
        assert!(result.is_some());
        let (decls, ps) = result.context("expected monoize to succeed for an empty file")?;
        assert!(decls.is_empty());
        assert!(ps.is_empty());
        Ok(()) // return success to the test harness
    }

    #[test]
    fn mono_name_extracts_name() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let c = Located::new(CC::Name("foo".into()), loc());
        assert_eq!(mono_name(&c), "foo");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn mono_name_fallback_for_non_name() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let c = Located::new(CC::Ffi("Basis".into(), "int".into()), loc());
        assert_eq!(mono_name(&c), "?");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn mono_type_ffi_basis_unit() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let t = mono_type_ffi("Basis", "unit", &loc());
        assert!(matches!(&t.node, Typ::Record(fs) if fs.is_empty()));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn mono_type_ffi_basis_int() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let t = mono_type_ffi("Basis", "int", &loc());
        assert!(matches!(&t.node, Typ::Ffi(m, x) if m == "Basis" && x == "int"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn mono_type_ffi_non_basis_passthrough() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let t = mono_type_ffi("Other", "foo", &loc());
        assert!(matches!(&t.node, Typ::Ffi(m, x) if m == "Other" && x == "foo"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn mono_type_reduces_mapped_unit_row_to_empty_record() -> anyhow::Result<()> {
        let env = Env::empty();
        let row_k = Located::new(
            crate::core::Kind::Record(Box::new(Located::new(crate::core::Kind::Type, loc()))),
            loc(),
        );
        let ran_k = Located::new(crate::core::Kind::Type, loc());
        let mapped_empty_row = Located::new(
            CC::TRecord(Box::new(Located::new(
                CC::App(
                    Box::new(Located::new(
                        CC::App(
                            Box::new(Located::new(
                                CC::Map(Box::new(row_k.clone()), Box::new(ran_k)),
                                loc(),
                            )),
                            Box::new(Located::new(
                                CC::Abs(
                                    "fields".into(),
                                    Box::new(row_k),
                                    Box::new(Located::new(
                                        CC::TRecord(Box::new(Located::new(CC::Rel(0), loc()))),
                                        loc(),
                                    )),
                                ),
                                loc(),
                            )),
                        ),
                        loc(),
                    )),
                    Box::new(Located::new(CC::Unit, loc())),
                ),
                loc(),
            ))),
            loc(),
        );

        let mono = mono_type(&env, &mut HashMap::new(), &mapped_empty_row);
        assert!(matches!(&mono.node, Typ::Record(fields) if fields.is_empty()));
        Ok(())
    }

    #[test]
    fn mono_type_preserves_bare_kind_type_record_fields() -> anyhow::Result<()> {
        let env = Env::empty();
        let bare_record = Located::new(
            CC::Record(
                Box::new(Located::new(crate::core::Kind::Type, loc())),
                vec![(
                    Located::new(CC::Name("Room".into()), loc()),
                    Located::new(CC::Ffi("Basis".into(), "int".into()), loc()),
                )],
            ),
            loc(),
        );

        let mono = mono_type(&env, &mut HashMap::new(), &bare_record);
        assert!(matches!(
            &mono.node,
            Typ::Record(fields)
                if fields.len() == 1
                    && fields[0].0 == "Room"
                    && matches!(fields[0].1.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "int")
        ));
        Ok(())
    }

    #[test]
    fn mono_type_normalizes_nested_row_map_in_record_field() -> anyhow::Result<()> {
        let env = Env::empty();
        let row_kind = Located::new(
            crate::core::Kind::Record(Box::new(Located::new(crate::core::Kind::Type, loc()))),
            loc(),
        );
        let type_kind = Located::new(crate::core::Kind::Type, loc());
        let pack_row = Located::new(
            CC::Abs(
                "fields".into(),
                Box::new(row_kind.clone()),
                Box::new(Located::new(
                    CC::TRecord(Box::new(Located::new(CC::Rel(0), loc()))),
                    loc(),
                )),
            ),
            loc(),
        );
        let inner_row = Located::new(
            CC::Record(
                Box::new(Located::new(crate::core::Kind::Type, loc())),
                vec![(
                    Located::new(CC::Name("Room".into()), loc()),
                    Located::new(CC::Ffi("Basis".into(), "int".into()), loc()),
                )],
            ),
            loc(),
        );
        let mapped_inner_row = Located::new(
            CC::App(
                Box::new(Located::new(
                    CC::App(
                        Box::new(Located::new(
                            CC::Map(Box::new(row_kind), Box::new(type_kind)),
                            loc(),
                        )),
                        Box::new(pack_row),
                    ),
                    loc(),
                )),
                Box::new(inner_row),
            ),
            loc(),
        );
        let outer_record = Located::new(
            CC::TRecord(Box::new(Located::new(
                CC::Record(
                    Box::new(Located::new(crate::core::Kind::Type, loc())),
                    vec![(
                        Located::new(CC::Name("T".into()), loc()),
                        mapped_inner_row.clone(),
                    )],
                ),
                loc(),
            ))),
            loc(),
        );

        let _normalized_inner = normalize_constructor_for_mono(&env, &mapped_inner_row);
        let mono = mono_type(&env, &mut HashMap::new(), &outer_record);
        assert!(matches!(
            &mono.node,
            Typ::Record(fields)
                if fields.len() == 1
                    && fields[0].0 == "T"
                    && matches!(
                        fields[0].1.node,
                        Typ::Record(ref inner_fields)
                            if inner_fields.len() == 1
                                && inner_fields[0].0 == "Room"
                                && matches!(inner_fields[0].1.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "int")
                    )
        ));
        Ok(())
    }

    #[test]
    fn mono_type_sql_injectable_is_serializer_function() -> anyhow::Result<()> {
        let env = Env::empty();
        let sql_injectable_int = Located::new(
            CC::App(
                Box::new(Located::new(
                    CC::Ffi("Basis".into(), "sql_injectable".into()),
                    loc(),
                )),
                Box::new(Located::new(CC::Ffi("Basis".into(), "int".into()), loc())),
            ),
            loc(),
        );

        let mono = mono_type(&env, &mut HashMap::new(), &sql_injectable_int);
        assert!(matches!(
            &mono.node,
            Typ::Fun(dom, ran)
                if matches!(dom.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "int")
                    && matches!(ran.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "string")
        ));
        Ok(())
    }

    #[test]
    fn mono_type_sql_injectable_prim_is_serializer_function() -> anyhow::Result<()> {
        let env = Env::empty();
        let sql_injectable_prim_int = Located::new(
            CC::App(
                Box::new(Located::new(
                    CC::Ffi("Basis".into(), "sql_injectable_prim".into()),
                    loc(),
                )),
                Box::new(Located::new(CC::Ffi("Basis".into(), "int".into()), loc())),
            ),
            loc(),
        );

        let mono = mono_type(&env, &mut HashMap::new(), &sql_injectable_prim_int);
        assert!(matches!(
            &mono.node,
            Typ::Fun(dom, ran)
                if matches!(dom.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "int")
                    && matches!(ran.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "string")
        ));
        Ok(())
    }

    #[test]
    fn mono_type_trigrammable_returns_unit_record() -> anyhow::Result<()> {
        let env = Env::empty();
        let trigrammable_string = Located::new(
            CC::App(
                Box::new(Located::new(
                    CC::Ffi("Basis".into(), "trigrammable".into()),
                    loc(),
                )),
                Box::new(Located::new(
                    CC::Ffi("Basis".into(), "string".into()),
                    loc(),
                )),
            ),
            loc(),
        );

        let mono = mono_type(&env, &mut HashMap::new(), &trigrammable_string);
        assert!(matches!(
            &mono.node,
            Typ::Fun(dom, ran)
                if matches!(dom.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "string")
                    && matches!(ran.node, Typ::Record(ref fields) if fields.is_empty())
        ));
        Ok(())
    }

    #[test]
    fn fm_fresh_name_increments() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut fm = Fm::empty(10);
        assert_eq!(fm.fresh_name(), 10);
        assert_eq!(fm.fresh_name(), 11);
        Ok(()) // return success to the test harness
    }

    #[test]
    fn mono_type_row_flattens_concat_rows() -> anyhow::Result<()> {
        let env = Env::empty();
        let row = Located::new(
            CC::Concat(
                Box::new(Located::new(
                    CC::Record(
                        Box::new(Located::new(crate::core::Kind::Type, loc())),
                        vec![(
                            Located::new(CC::Name("A".into()), loc()),
                            Located::new(CC::Ffi("Basis".into(), "int".into()), loc()),
                        )],
                    ),
                    loc(),
                )),
                Box::new(Located::new(
                    CC::Record(
                        Box::new(Located::new(crate::core::Kind::Type, loc())),
                        vec![(
                            Located::new(CC::Name("B".into()), loc()),
                            Located::new(CC::Ffi("Basis".into(), "string".into()), loc()),
                        )],
                    ),
                    loc(),
                )),
            ),
            loc(),
        );

        let mono = mono_type_row(&env, &mut HashMap::new(), &row, &loc());
        assert!(matches!(
            &mono.node,
            Typ::Record(fields)
                if fields.len() == 2
                    && fields[0].0 == "A"
                    && fields[1].0 == "B"
        ));
        Ok(())
    }

    #[test]
    fn mono_exp_concat_of_record_literals_merges_fields() -> anyhow::Result<()> {
        let env = Env::empty();
        let settings = Settings::default();
        let mut fm = Fm::empty(0);
        let int_c = Located::new(CC::Ffi("Basis".into(), "int".into()), loc());
        let string_c = Located::new(CC::Ffi("Basis".into(), "string".into()), loc());
        let left = Located::new(
            CE::Record(vec![(
                Located::new(CC::Name("A".into()), loc()),
                Located::new(CE::Prim(Prim::Int(1)), loc()),
                int_c.clone(),
            )]),
            loc(),
        );
        let right = Located::new(
            CE::Record(vec![(
                Located::new(CC::Name("B".into()), loc()),
                Located::new(
                    CE::Prim(Prim::String(
                        crate::primitives::StringMode::Normal,
                        "x".into(),
                    )),
                    loc(),
                ),
                string_c.clone(),
            )]),
            loc(),
        );
        let left_row = Located::new(
            CC::Record(
                Box::new(Located::new(crate::core::Kind::Type, loc())),
                vec![(Located::new(CC::Name("A".into()), loc()), int_c)],
            ),
            loc(),
        );
        let right_row = Located::new(
            CC::Record(
                Box::new(Located::new(crate::core::Kind::Type, loc())),
                vec![(Located::new(CC::Name("B".into()), loc()), string_c)],
            ),
            loc(),
        );
        let concat = Located::new(
            CE::Concat(Box::new(left), left_row, Box::new(right), right_row),
            loc(),
        );

        let mono = mono_exp(&env, &mut fm, &concat, &settings);
        assert!(matches!(
            &mono.node,
            Exp::Record(fields)
                if fields.len() == 2
                    && fields[0].0 == "A"
                    && fields[1].0 == "B"
                    && matches!(fields[0].1.node, Exp::Prim(Prim::Int(1)))
        ));
        Ok(())
    }

    #[test]
    fn mono_exp_cut_uses_rest_row_when_input_is_not_literal() -> anyhow::Result<()> {
        let env = Env::empty();
        let settings = Settings::default();
        let mut fm = Fm::empty(0);
        let int_c = Located::new(CC::Ffi("Basis".into(), "int".into()), loc());
        let string_c = Located::new(CC::Ffi("Basis".into(), "string".into()), loc());
        let cut = Located::new(
            CE::Cut(
                Box::new(Located::new(CE::Rel(0), loc())),
                Located::new(CC::Name("A".into()), loc()),
                crate::core::FieldMeta {
                    field: int_c.clone(),
                    rest: Located::new(
                        CC::Record(
                            Box::new(Located::new(crate::core::Kind::Type, loc())),
                            vec![(Located::new(CC::Name("B".into()), loc()), string_c.clone())],
                        ),
                        loc(),
                    ),
                },
            ),
            loc(),
        );

        let mono = mono_exp(&env, &mut fm, &cut, &settings);
        assert!(matches!(
            &mono.node,
            Exp::Record(fields)
                if fields.len() == 1
                    && fields[0].0 == "B"
                    && matches!(fields[0].1.node, Exp::Field(_, ref name) if name == "B")
        ));
        Ok(())
    }

    #[test]
    fn mono_exp_cut_multi_uses_rest_row_when_input_is_not_literal() -> anyhow::Result<()> {
        let env = Env::empty();
        let settings = Settings::default();
        let mut fm = Fm::empty(0);
        let int_c = Located::new(CC::Ffi("Basis".into(), "int".into()), loc());
        let string_c = Located::new(CC::Ffi("Basis".into(), "string".into()), loc());
        let cut_multi = Located::new(
            CE::CutMulti(
                Box::new(Located::new(CE::Rel(0), loc())),
                Located::new(
                    CC::Record(
                        Box::new(Located::new(crate::core::Kind::Type, loc())),
                        vec![(Located::new(CC::Name("A".into()), loc()), int_c.clone())],
                    ),
                    loc(),
                ),
                crate::core::RestMeta {
                    rest: Located::new(
                        CC::Record(
                            Box::new(Located::new(crate::core::Kind::Type, loc())),
                            vec![(Located::new(CC::Name("B".into()), loc()), string_c.clone())],
                        ),
                        loc(),
                    ),
                },
            ),
            loc(),
        );

        let mono = mono_exp(&env, &mut fm, &cut_multi, &settings);
        assert!(matches!(
            &mono.node,
            Exp::Record(fields)
                if fields.len() == 1
                    && fields[0].0 == "B"
                    && matches!(fields[0].1.node, Exp::Field(_, ref name) if name == "B")
        ));
        Ok(())
    }

    #[test]
    fn mono_exp_reduces_local_constructor_application_before_erasure() -> anyhow::Result<()> {
        let env = Env::empty();
        let settings = Settings::default();
        let mut fm = Fm::empty(0);
        let exp = Located::new(
            CE::CApp(
                Box::new(Located::new(
                    CE::CAbs(
                        "t".into(),
                        Box::new(Located::new(crate::core::Kind::Type, loc())),
                        Box::new(Located::new(CE::Prim(Prim::Int(7)), loc())),
                    ),
                    loc(),
                )),
                Located::new(CC::Ffi("Basis".into(), "int".into()), loc()),
            ),
            loc(),
        );

        let mono = mono_exp(&env, &mut fm, &exp, &settings);
        assert!(matches!(mono.node, Exp::Prim(Prim::Int(7))));
        Ok(())
    }

    #[test]
    fn mono_exp_erases_kind_application_without_dummy_prim() -> anyhow::Result<()> {
        let env = Env::empty();
        let settings = Settings::default();
        let mut fm = Fm::empty(0);
        let exp = Located::new(
            CE::KApp(
                Box::new(Located::new(
                    CE::KAbs(
                        "k".into(),
                        Box::new(Located::new(CE::Prim(Prim::Int(9)), loc())),
                    ),
                    loc(),
                )),
                Box::new(Located::new(crate::core::Kind::Type, loc())),
            ),
            loc(),
        );

        let mono = mono_exp(&env, &mut fm, &exp, &settings);
        assert!(matches!(mono.node, Exp::Prim(Prim::Int(9))));
        Ok(())
    }
}
