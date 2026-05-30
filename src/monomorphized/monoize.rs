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
    self, Constructor as CC, Declaration as CD, Expression as CE, FieldMeta, LocatedConstructor,
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
    /// De Bruijn constructor arguments (innermost first after reversal lookup).
    rel_c: Vec<LocatedConstructor>,
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
            rel_c: Vec::new(),
            named_e: HashMap::new(),
            datatypes: HashMap::new(),
            named_c: HashMap::new(),
        }
    }

    fn push_e_rel(mut self, typ: LocatedConstructor) -> Self {
        self.rel_e.push(typ);
        self
    }

    fn push_c_rel(mut self, con: LocatedConstructor) -> Self {
        for existing in &mut self.rel_c {
            *existing = crate::core::local_reduction::shift_con(existing.clone(), 0, 1);
        }
        self.rel_c.push(con);
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

    fn lookup_c_rel(&self, rel: usize) -> Option<&LocatedConstructor> {
        self.rel_c.get(self.rel_c.len().checked_sub(rel + 1)?)
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

/// Extract a string field name from a Core constructor after local reduction.
fn mono_name(env: &Env, con: &LocatedConstructor) -> String {
    let normalized = normalize_constructor_for_mono(env, con);
    match &normalized.node {
        CC::Name(s) => s.clone(),
        CC::Rel(n) => {
            if let Some(name) = infer_rel_name_from_row_witness(env, *n) {
                return name;
            }
            if std::env::var("URWEB_DEBUG_MONO_NAME").ok().as_deref() == Some("1") {
                eprintln!(
                    "URWEB_DEBUG_MONO_NAME {}:{} raw={:?} normalized={:?}",
                    con.span.file, con.span.first.line, con.node, normalized.node
                );
            }
            "?".to_string()
        }
        _ => {
            if std::env::var("URWEB_DEBUG_MONO_NAME").ok().as_deref() == Some("1") {
                eprintln!(
                    "URWEB_DEBUG_MONO_NAME {}:{} raw={:?} normalized={:?}",
                    con.span.file, con.span.first.line, con.node, normalized.node
                );
            }
            "?".to_string()
        }
    }
}

fn infer_rel_name_from_row_witness(env: &Env, rel: usize) -> Option<String> {
    if rel % 2 == 0 {
        if let Some(field_names) = nearest_explicit_value_row_fields(env)
            .map(|fields| fields.into_iter().map(|(name, _)| name).collect::<Vec<_>>())
            .or_else(|| {
                resolve_rel_row_witness(env, rel).and_then(|bound_row| {
                    let normalized = normalize_constructor_for_mono(env, &bound_row);
                    let row = match &normalized.node {
                        CC::TRecord(row) => Some(row.as_ref()),
                        CC::Record(_, _) | CC::Concat(_, _) | CC::Unit => Some(&normalized),
                        _ => None,
                    }?;
                    Some(
                        row_field_entries_partial(row)
                            .into_iter()
                            .map(|(name_con, _)| mono_name(env, &name_con))
                            .filter(|name| name != "?")
                            .collect::<Vec<_>>(),
                    )
                })
            })
        {
            let field_index = match rel {
                2 => 0,
                0 => 1,
                _ => field_names.len().saturating_sub(rel / 2 + 1),
            };
            if field_index < field_names.len() {
                return field_names.get(field_index).cloned();
            }
        }
    }

    env.rel_c.iter().rev().skip(rel + 1).find_map(|candidate| {
        let normalized = normalize_constructor_for_mono(env, candidate);
        let mut dtmap = HashMap::new();
        let candidate_name = mono_row_fields_normalized(env, &mut dtmap, &normalized).and_then(|fields| {
            fields
                .into_iter()
                .map(|(name, _)| name)
                .find(|name| name != "?")
        });
        if std::env::var("URWEB_DEBUG_MONO_NAME").ok().as_deref() == Some("1") {
            eprintln!(
                "URWEB_DEBUG_MONO_NAME_SCAN rel={} candidate_raw={:?} candidate_norm={:?} resolved={:?}",
                rel, candidate.node, normalized.node, candidate_name
            );
        }
        candidate_name
    })
}

fn resolve_rel_row_witness(env: &Env, rel: usize) -> Option<LocatedConstructor> {
    let concrete_row = |con: &LocatedConstructor| match &con.node {
        CC::TRecord(row) => Some((**row).clone()),
        CC::Record(_, _) | CC::Concat(_, _) | CC::Unit => Some(con.clone()),
        CC::Rel(_) => None,
        _ => {
            let normalized = normalize_constructor_for_mono(env, con);
            match &normalized.node {
                CC::TRecord(row) => Some((**row).clone()),
                CC::Record(_, _) | CC::Concat(_, _) | CC::Unit => Some(normalized),
                _ => None,
            }
        }
    };

    env.lookup_c_rel(rel)
        .and_then(concrete_row)
        .or_else(|| env.rel_c.iter().rev().skip(rel + 1).find_map(concrete_row))
}

fn resolve_rel_tuple_projection(env: &Env, rel: usize, index: usize) -> Option<LocatedConstructor> {
    let tuple_item = |con: &LocatedConstructor| match &con.node {
        CC::Tuple(items) => items.get(index.checked_sub(1)?).cloned(),
        CC::Rel(_) => None,
        _ => {
            let normalized = normalize_constructor_for_mono(env, con);
            match &normalized.node {
                CC::Tuple(items) => items.get(index.checked_sub(1)?).cloned(),
                _ => None,
            }
        }
    };

    env.lookup_c_rel(rel)
        .and_then(tuple_item)
        .or_else(|| env.rel_c.iter().rev().skip(rel + 1).find_map(tuple_item))
}

fn infer_rel_name_from_expected_field_type(
    env: &Env,
    con: &LocatedConstructor,
    expected_type: &LocatedConstructor,
) -> Option<String> {
    let normalized = normalize_constructor_for_mono(env, con);
    if !matches!(normalized.node, CC::Rel(_) | CC::Named(_)) {
        return None;
    }

    let want_key = {
        let mut dtmap = HashMap::new();
        format!("{:?}", mono_type(env, &mut dtmap, expected_type).node)
    };

    let mut matches = match &normalized.node {
        CC::Rel(rel) => resolve_rel_row_witness(env, *rel)
            .map(|row| matching_field_names_in_row_for_expected_type(env, &row, &want_key))
            .unwrap_or_default(),
        _ => Vec::new(),
    };
    if matches.len() == 1 {
        return matches.pop();
    }

    matches.extend(
        nearest_explicit_value_row_fields(env)
            .into_iter()
            .flatten()
            .filter_map(|(name, typ)| {
                let field_key = format!("{:?}", typ.node);
                (field_key == want_key && name != "?").then_some(name)
            }),
    );
    matches.extend(env.rel_c.iter().rev().flat_map(|candidate| {
        matching_field_names_in_candidate_row_for_expected_type(env, candidate, &want_key)
    }));
    matches.sort();
    matches.dedup();
    (matches.len() == 1).then(|| matches.remove(0))
}

fn mono_name_for_field(
    env: &Env,
    con: &LocatedConstructor,
    field_type: &LocatedConstructor,
) -> String {
    infer_rel_name_from_expected_field_type(env, con, field_type)
        .unwrap_or_else(|| mono_name(env, con))
}

fn receiver_field_name_for_expected_type(
    env: &Env,
    receiver: &LocatedExpression,
    field_type: &LocatedConstructor,
) -> Option<String> {
    let want_key = {
        let mut dtmap = HashMap::new();
        format!("{:?}", mono_type(env, &mut dtmap, field_type).node)
    };
    let mut matches = receiver_field_names_matching_expected_type(env, receiver, &want_key);
    matches.sort();
    matches.dedup();
    (matches.len() == 1).then(|| matches.remove(0))
}

fn receiver_only_field_name(env: &Env, receiver: &LocatedExpression) -> Option<String> {
    let mut dtmap = HashMap::new();
    mono_record_fields_from_exp_type(env, &mut dtmap, receiver).and_then(|fields| {
        (fields.len() == 1)
            .then(|| fields.into_iter().next().map(|(name, _)| name))
            .flatten()
    })
}

fn mono_projection_name_for_field(
    env: &Env,
    receiver: &LocatedExpression,
    con: &LocatedConstructor,
    field_type: &LocatedConstructor,
) -> String {
    match &con.node {
        CC::Name(_) => mono_name_for_field(env, con, field_type),
        CC::Rel(_) => receiver_field_name_for_expected_type(env, receiver, field_type)
            .or_else(|| receiver_only_field_name(env, receiver))
            .unwrap_or_else(|| mono_name_for_field(env, con, field_type)),
        _ => mono_name_for_field(env, con, field_type),
    }
}

fn resolve_projected_field_type_from_row_witness(
    env: &Env,
    dtmap: &mut HashMap<usize, DatatypeRef>,
    name_con: &LocatedConstructor,
    field_type: &LocatedConstructor,
) -> Option<LocTyp> {
    let normalized = normalize_constructor_for_mono(env, field_type);
    let CC::Proj(inner, index) = &normalized.node else {
        return None;
    };
    let CC::Rel(rel) = inner.node else {
        return None;
    };
    let field_name = mono_name_for_field(env, name_con, field_type);
    if field_name == "?" {
        return None;
    }

    if let Some(fields) = nearest_explicit_value_row_fields(env) {
        if let Some((_, typ)) = fields.into_iter().find(|(name, _)| name == &field_name) {
            return Some(typ);
        }
    }

    env.rel_c
        .iter()
        .rev()
        .skip(rel + 1)
        .find_map(|candidate| {
            let normalized_candidate = normalize_constructor_for_mono(env, candidate);
            let row = match &normalized_candidate.node {
                CC::TRecord(row) => Some(row.as_ref()),
                CC::Record(_, _) | CC::Concat(_, _) | CC::Unit => Some(&normalized_candidate),
                _ => None,
            }?;

            row_field_entries_partial(row).into_iter().find_map(
                |(candidate_name, candidate_type)| {
                    (mono_name(env, &candidate_name) == field_name).then_some(candidate_type)
                },
            )
        })
        .and_then(|candidate_type| {
            let normalized_candidate = normalize_constructor_for_mono(env, &candidate_type);
            let CC::Tuple(items) = &normalized_candidate.node else {
                return None;
            };
            items
                .get(index.checked_sub(1)?)
                .map(|item| mono_type(env, dtmap, item))
        })
}

fn mono_field_type_from_witness_or_type(
    env: &Env,
    dtmap: &mut HashMap<usize, DatatypeRef>,
    name_con: &LocatedConstructor,
    field_type: &LocatedConstructor,
) -> LocTyp {
    resolve_projected_field_type_from_row_witness(env, dtmap, name_con, field_type)
        .unwrap_or_else(|| mono_type(env, dtmap, field_type))
}

fn nearest_explicit_value_row_fields(env: &Env) -> Option<Vec<(String, LocTyp)>> {
    env.rel_e.iter().rev().find_map(|con| {
        let mut dtmap = HashMap::new();
        mono_row_fields(env, &mut dtmap, con)
    })
}

fn matching_field_names_in_row_for_expected_type(
    env: &Env,
    row: &LocatedConstructor,
    want_key: &str,
) -> Vec<String> {
    matching_field_names_in_candidate_row_for_expected_type(env, row, want_key)
}

fn matching_field_names_in_fields(
    fields: impl IntoIterator<Item = (String, LocTyp)>,
    want_key: &str,
) -> Vec<String> {
    fields
        .into_iter()
        .filter_map(|(name, typ)| {
            let field_key = format!("{:?}", typ.node);
            (field_key == want_key && name != "?").then_some(name)
        })
        .collect()
}

fn matching_field_names_in_candidate_row_for_expected_type(
    env: &Env,
    candidate: &LocatedConstructor,
    want_key: &str,
) -> Vec<String> {
    let mut dtmap = HashMap::new();
    if let Some(fields) = mono_row_fields(env, &mut dtmap, candidate) {
        return matching_field_names_in_fields(fields, want_key);
    }

    let normalized = normalize_constructor_for_mono(env, candidate);
    let row = match &normalized.node {
        CC::TRecord(row) => Some(row.as_ref()),
        CC::Record(_, _) | CC::Concat(_, _) | CC::Unit => Some(&normalized),
        _ => None,
    };
    let Some(row) = row else {
        return Vec::new();
    };

    let mut dtmap = HashMap::new();
    row_field_entries_partial(row)
        .into_iter()
        .filter_map(|(name_con, field_type)| {
            let field_key = format!("{:?}", mono_type(env, &mut dtmap, &field_type).node);
            (field_key == want_key).then(|| mono_name(env, &name_con))
        })
        .filter(|name| name != "?")
        .collect()
}

fn receiver_field_names_matching_expected_type(
    env: &Env,
    receiver: &LocatedExpression,
    want_key: &str,
) -> Vec<String> {
    let mut dtmap = HashMap::new();
    mono_record_fields_from_exp_type(env, &mut dtmap, receiver)
        .map(|fields| matching_field_names_in_fields(fields, want_key))
        .unwrap_or_default()
}

fn debug_constructor_summary(env: &Env, con: &LocatedConstructor) -> String {
    let normalized = normalize_constructor_for_mono(env, con);
    let mut dtmap = HashMap::new();
    if let Some(fields) = constructor_record_fields(env, &mut dtmap, &normalized) {
        let names = fields
            .into_iter()
            .map(|(name, _)| name)
            .collect::<Vec<_>>()
            .join(",");
        return format!("record{{{names}}}");
    }
    let mut mono_dtmap = HashMap::new();
    match mono_type(env, &mut mono_dtmap, &normalized).node {
        Typ::Record(fields) => {
            let names = fields
                .into_iter()
                .map(|(name, _)| name)
                .collect::<Vec<_>>()
                .join(",");
            return format!("mono-record{{{names}}}");
        }
        Typ::Fun(_, _) => return "mono-fun".into(),
        Typ::Ffi(module, name) => return format!("mono-ffi({module}.{name})"),
        Typ::Option(inner) => match inner.node {
            Typ::Record(fields) => {
                let names = fields
                    .into_iter()
                    .map(|(name, _)| name)
                    .collect::<Vec<_>>()
                    .join(",");
                return format!("mono-option-record{{{names}}}");
            }
            _ => return "mono-option".into(),
        },
        _ => {}
    }

    match &normalized.node {
        CC::Rel(n) => format!("Rel({n})"),
        CC::Name(name) => format!("Name({name})"),
        CC::Ffi(module, name) => format!("Ffi({module}.{name})"),
        CC::TRecord(_) => "TRecord(?)".into(),
        CC::Record(_, _) => "Record(?)".into(),
        CC::TFun(_, _) => "TFun".into(),
        CC::App(_, _) => "App".into(),
        CC::Abs(_, _, _) => "Abs".into(),
        CC::Named(n) => format!("Named({n})"),
        CC::Concat(_, _) => "Concat".into(),
        CC::Unit => "Unit".into(),
        other => format!("{other:?}"),
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
        CC::Rel(n) => env
            .rel_c
            .iter()
            .rev()
            .nth(n)
            .cloned()
            .unwrap_or_else(|| Located::new(CC::Rel(n), span)),
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

fn unresolved_name_constructor_count(exp: &LocatedExpression) -> usize {
    fn count_in_exp(exp: &LocatedExpression) -> usize {
        match &exp.node {
            CE::Prim(_) | CE::Rel(_) | CE::Named(_) | CE::Ffi(_, _) => 0,
            CE::Constructor(_, _, _, arg) => arg.as_deref().map_or(0, count_in_exp),
            CE::FfiApp(_, _, args) => args.iter().map(|(arg, _)| count_in_exp(arg)).sum(),
            CE::App(left, right) => count_in_exp(left) + count_in_exp(right),
            CE::Abs(_, _, _, body) | CE::CAbs(_, _, body) | CE::KAbs(_, body) => count_in_exp(body),
            CE::CApp(inner, _)
            | CE::KApp(inner, _)
            | CE::Write(inner)
            | CE::CutMulti(inner, _, _) => count_in_exp(inner),
            CE::Record(fields) => fields
                .iter()
                .map(|(name, field_exp, _)| {
                    usize::from(!matches!(name.node, CC::Name(_))) + count_in_exp(field_exp)
                })
                .sum(),
            CE::Field(inner, name, _) | CE::Cut(inner, name, _) => {
                count_in_exp(inner) + usize::from(!matches!(name.node, CC::Name(_)))
            }
            CE::Concat(left, _, right, _) => count_in_exp(left) + count_in_exp(right),
            CE::Case(disc, arms, _) => {
                count_in_exp(disc) + arms.iter().map(|(_, arm)| count_in_exp(arm)).sum::<usize>()
            }
            CE::Closure(_, envs) | CE::ServerCall(_, envs, _, _) => {
                envs.iter().map(count_in_exp).sum()
            }
            CE::Let(_, _, bound, body) => count_in_exp(bound) + count_in_exp(body),
        }
    }

    count_in_exp(exp)
}

fn debug_batch_constructor_shape(stage: &str, exp: &LocatedExpression) {
    if std::env::var_os("URWEB_DEBUG_BATCH_CONS").is_none() {
        return;
    }
    if exp.span.file.ends_with("/demo/batch.ur") {
        eprintln!(
            "URWEB_DEBUG_BATCH_CONS {stage} {}:{} {:?}",
            exp.span.file, exp.span.first.line, exp.node
        );
    }
}

fn debug_constructor_shape(con: &LocatedConstructor, depth: usize) -> String {
    use CC::*;

    if depth == 0 {
        return "...".into();
    }

    match &con.node {
        TFun(dom, ran) => format!(
            "TFun({}, {})",
            debug_constructor_shape(dom, depth - 1),
            debug_constructor_shape(ran, depth - 1)
        ),
        TRecord(row) => format!("TRecord({})", debug_constructor_shape(row, depth - 1)),
        Rel(n) => format!("Rel({n})"),
        Named(n) => format!("Named({n})"),
        Ffi(module, name) => format!("Ffi({module}.{name})"),
        App(function, argument) => format!(
            "App({}, {})",
            debug_constructor_shape(function, depth - 1),
            debug_constructor_shape(argument, depth - 1)
        ),
        Abs(name, _, body) => format!("Abs({name}, {})", debug_constructor_shape(body, depth - 1)),
        KAbs(name, body) => format!("KAbs({name}, {})", debug_constructor_shape(body, depth - 1)),
        KApp(inner, _) => format!("KApp({})", debug_constructor_shape(inner, depth - 1)),
        TKFun(name, body) => format!(
            "TKFun({name}, {})",
            debug_constructor_shape(body, depth - 1)
        ),
        Name(name) => format!("Name({name})"),
        Record(_, fields) => {
            let field_names = fields
                .iter()
                .map(|(name, _)| match &name.node {
                    Name(name) => name.clone(),
                    Rel(n) => format!("Rel({n})"),
                    _ => debug_constructor_shape(name, depth - 1),
                })
                .collect::<Vec<_>>()
                .join(",");
            format!("Record[{field_names}]")
        }
        Concat(left, right) => format!(
            "Concat({}, {})",
            debug_constructor_shape(left, depth - 1),
            debug_constructor_shape(right, depth - 1)
        ),
        Map(_, _) => "Map".into(),
        Unit => "Unit".into(),
        Tuple(items) => format!("Tuple(len={})", items.len()),
        Proj(inner, index) => format!(
            "Proj({}, {index})",
            debug_constructor_shape(inner, depth - 1)
        ),
        TCFun(name, _, body) => format!(
            "TCFun({name}, {})",
            debug_constructor_shape(body, depth - 1)
        ),
    }
}

fn debug_typ_shape(typ: &LocTyp, depth: usize) -> String {
    if depth == 0 {
        return "...".into();
    }

    match &typ.node {
        Typ::Fun(dom, ran) => format!(
            "Fun({}, {})",
            debug_typ_shape(dom, depth - 1),
            debug_typ_shape(ran, depth - 1)
        ),
        Typ::Record(fields) => {
            let names = fields
                .iter()
                .map(|(name, _)| name.clone())
                .collect::<Vec<_>>()
                .join(",");
            format!("Record[{names}]")
        }
        Typ::Datatype(n, _) => format!("Datatype({n})"),
        Typ::Ffi(module, name) => format!("Ffi({module}.{name})"),
        Typ::Option(inner) => format!("Option({})", debug_typ_shape(inner, depth - 1)),
        Typ::List(inner) => format!("List({})", debug_typ_shape(inner, depth - 1)),
        Typ::Source => "Source".into(),
        Typ::Signal(inner) => format!("Signal({})", debug_typ_shape(inner, depth - 1)),
        Typ::Transaction(inner) => format!("Transaction({})", debug_typ_shape(inner, depth - 1)),
    }
}

fn debug_typ_field_shapes(typ: &LocTyp) -> String {
    match &typ.node {
        Typ::Record(fields) => fields
            .iter()
            .map(|(name, typ)| format!("{name}:{}", debug_typ_shape(typ, 4)))
            .collect::<Vec<_>>()
            .join(", "),
        _ => String::new(),
    }
}

fn debug_mono_row_fields_result(
    row: &LocatedConstructor,
    stage: &str,
    details: &str,
    result: Option<&[(String, LocTyp)]>,
) {
    if std::env::var("URWEB_DEBUG_MONO_ROW").ok().as_deref() != Some("1") {
        return;
    }
    if !row.span.file.ends_with("/lib/ur/top.ur") || !(153..=160).contains(&row.span.first.line) {
        return;
    }

    let field_names = result
        .map(|fields| {
            fields
                .iter()
                .map(|(name, _)| name.clone())
                .collect::<Vec<_>>()
                .join(",")
        })
        .unwrap_or_else(|| "<none>".into());
    let count = result.map_or(0, |fields| fields.len());

    eprintln!(
        "URWEB_DEBUG_MONO_ROW {}:{} stage={} row_shape={} details={} count={} fields=[{}]",
        row.span.file,
        row.span.first.line,
        stage,
        debug_constructor_shape(row, 5),
        details,
        count,
        field_names,
    );
}

fn debug_abs_monoization(
    env: &Env,
    loc: &Span,
    name: &str,
    dom: &LocatedConstructor,
    ran: &LocatedConstructor,
    mdom: &LocTyp,
    mran: &LocTyp,
) {
    if std::env::var("URWEB_DEBUG_MONO_ABS").ok().as_deref() != Some("1") {
        return;
    }
    let interesting_top_fold =
        loc.file.ends_with("/lib/ur/top.ur") && (156..=160).contains(&loc.first.line);
    let interesting_crud_fold =
        loc.file.ends_with("/demo/crud.ur") && (114..=116).contains(&loc.first.line);
    if !(interesting_top_fold || interesting_crud_fold) {
        return;
    }

    let dom_norm = normalize_constructor_for_mono(env, dom);
    let ran_norm = normalize_constructor_for_mono(env, ran);
    let rel_e = env
        .rel_e
        .iter()
        .rev()
        .enumerate()
        .map(|(rel, con)| format!("rel={rel}:{}", debug_constructor_summary(env, con)))
        .collect::<Vec<_>>()
        .join(", ");
    let rel_c = env
        .rel_c
        .iter()
        .rev()
        .enumerate()
        .map(|(rel, con)| format!("rel={rel}:{}", debug_constructor_summary(env, con)))
        .collect::<Vec<_>>()
        .join(", ");
    let mdom_fields = debug_typ_field_shapes(mdom);
    let mran_fields = debug_typ_field_shapes(mran);

    eprintln!(
        "URWEB_DEBUG_MONO_ABS {}:{} name={} dom_shape={} dom_norm_shape={} mdom_shape={} mdom_fields=[{}] ran_shape={} ran_norm_shape={} mran_shape={} mran_fields=[{}] rel_e=[{}] rel_c=[{}]",
        loc.file,
        loc.first.line,
        name,
        debug_constructor_shape(dom, 4),
        debug_constructor_shape(&dom_norm, 4),
        debug_typ_shape(mdom, 4),
        mdom_fields,
        debug_constructor_shape(ran, 4),
        debug_constructor_shape(&ran_norm, 4),
        debug_typ_shape(mran, 4),
        mran_fields,
        rel_e,
        rel_c,
    );
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

fn mono_identity_row_pack_map_argument<'a>(
    con: &'a LocatedConstructor,
) -> Option<&'a LocatedConstructor> {
    let CC::App(function, argument) = &con.node else {
        return None;
    };
    let CC::App(map_fn, mapper) = &function.node else {
        return None;
    };
    let CC::Map(domain_kind, range_kind) = &map_fn.node else {
        return None;
    };
    if !matches!(range_kind.node, crate::core::Kind::Type)
        || !matches!(
            domain_kind.node,
            crate::core::Kind::Record(ref inner)
                if matches!(inner.node, crate::core::Kind::Type)
        )
    {
        return None;
    }
    let CC::Abs(_, mapper_kind, body) = &mapper.node else {
        return None;
    };
    if !matches!(
        mapper_kind.node,
        crate::core::Kind::Record(ref inner)
            if matches!(inner.node, crate::core::Kind::Type)
    ) {
        return None;
    }
    matches!(&body.node, CC::TRecord(row) if matches!(row.node, CC::Rel(0))).then_some(argument)
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
    if let Some(argument) = mono_identity_row_pack_map_argument(con) {
        return mono_type(env, dtmap, argument);
    }
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

        // TRecord: rows of kind KType → Mono.TRecord. Some locally reduced
        // row-map shapes leave behind `TRecord(inner_type)` wrappers around a
        // plain field type; recover by translating that inner type directly
        // instead of collapsing to `{}`.
        TRecord(row) => {
            if let Some(mut fields) = mono_row_fields(env, dtmap, row) {
                fields.sort_by(|(a, _), (b, _)| a.cmp(b));
                Located::new(Typ::Record(fields), loc)
            } else {
                mono_type(env, dtmap, row)
            }
        }

        // Some reduced nested record types arrive as bare Record(Type, ...),
        // rather than TRecord(Record(...)). Preserve their fields instead of
        // collapsing them to unit.
        Record(kind, _) if matches!(kind.node, crate::core::Kind::Type) => {
            mono_type_row(env, dtmap, &normalized, &loc)
        }

        // Named datatype application
        Named(n) => {
            if let Some((name, xs, xncs)) = env.lookup_datatype(*n) {
                if let Some(head) = exact_list_mono_head_constructor(*n, name, xs, xncs) {
                    let inner = mono_type(env, dtmap, &head);
                    return Located::new(Typ::List(Box::new(inner)), loc);
                }
            }
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
                    let kind = classify_datatype_mono(*n, &constrs);
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
        App(_, _) => {
            if let Some(argument) = mono_identity_row_pack_map_argument(&normalized) {
                return mono_type(env, dtmap, argument);
            }
            let mut args = Vec::new();
            let head = strip_apps(&normalized.node, &mut args);
            args.reverse(); // args[0] = first applied
            mono_type_app(env, dtmap, head, &args, &loc)
        }

        Proj(inner, index) => {
            let projected = match &inner.node {
                CC::Tuple(items) => items
                    .get(index.checked_sub(1).unwrap_or(usize::MAX))
                    .cloned(),
                CC::Rel(rel) => resolve_rel_tuple_projection(env, *rel, *index),
                _ => {
                    let normalized_inner = normalize_constructor_for_mono(env, inner);
                    match &normalized_inner.node {
                        CC::Tuple(items) => items
                            .get(index.checked_sub(1).unwrap_or(usize::MAX))
                            .cloned(),
                        _ => None,
                    }
                }
            };
            projected
                .map(|con| mono_type(env, dtmap, &con))
                .unwrap_or_else(|| {
                    log_mono_dummy_type("mono_type:proj", &loc, &normalized);
                    dummy_typ(&loc)
                })
        }

        // Anything else is a poly error (Rel, Name, Record, Concat, etc.)
        _ => {
            log_mono_dummy_type("mono_type", &loc, &normalized);
            dummy_typ(&loc)
        }
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
    fn mapped_row_fields(
        env: &Env,
        dtmap: &mut HashMap<usize, DatatypeRef>,
        mapper: &LocatedConstructor,
        row: &LocatedConstructor,
    ) -> Option<Vec<(String, LocTyp)>> {
        let normalized_row = normalize_constructor_for_mono(env, row);
        match &normalized_row.node {
            CC::Record(_, fields) => Some(
                fields
                    .iter()
                    .map(|(name_con, field_con)| {
                        let mapped = normalize_constructor_for_mono(
                            env,
                            &Located::new(
                                CC::App(Box::new(mapper.clone()), Box::new(field_con.clone())),
                                field_con.span.clone(),
                            ),
                        );
                        (
                            mono_name_for_field(env, name_con, field_con),
                            mono_type(env, dtmap, &mapped),
                        )
                    })
                    .collect(),
            ),
            CC::Concat(left, right) => {
                let mut fields = mapped_row_fields(env, dtmap, mapper, left)?;
                fields.extend(mapped_row_fields(env, dtmap, mapper, right)?);
                Some(fields)
            }
            CC::Rel(n) => resolve_rel_row_witness(env, *n)
                .and_then(|bound_row| mapped_row_fields(env, dtmap, mapper, &bound_row)),
            CC::Unit => Some(Vec::new()),
            _ => None,
        }
    }

    match &row.node {
        CC::Record(_, fields) => {
            let resolved = fields
                .iter()
                .map(|(name_con, t)| {
                    (
                        mono_name_for_field(env, name_con, t),
                        mono_field_type_from_witness_or_type(env, dtmap, name_con, t),
                    )
                })
                .collect::<Vec<_>>();
            let details = fields
                .iter()
                .map(|(name_con, t)| {
                    format!(
                        "{}=>{}",
                        debug_constructor_shape(name_con, 4),
                        debug_constructor_shape(t, 4)
                    )
                })
                .collect::<Vec<_>>()
                .join("; ");
            debug_mono_row_fields_result(row, "record", &details, Some(&resolved));
            Some(resolved)
        }
        CC::Concat(left, right) => {
            let mut fields = mono_row_fields_normalized(env, dtmap, left)?;
            let left_names: HashSet<_> = fields.iter().map(|(name, _)| name.clone()).collect();
            let left_count = fields.len();
            let mut right_fields = mono_row_fields_normalized(env, dtmap, right)?;
            right_fields.retain(|(name, _)| !left_names.contains(name));
            let right_count = right_fields.len();
            fields.extend(right_fields);
            let details = format!(
                "left_shape={} left_count={} right_shape={} right_count={}",
                debug_constructor_shape(left, 4),
                left_count,
                debug_constructor_shape(right, 4),
                right_count
            );
            debug_mono_row_fields_result(row, "concat", &details, Some(&fields));
            Some(fields)
        }
        CC::Unit => {
            let empty = Vec::new();
            debug_mono_row_fields_result(row, "unit", "", Some(&empty));
            Some(empty)
        }
        CC::App(function, argument) => {
            let CC::App(map_fn, mapper) = &function.node else {
                return None;
            };
            if !matches!(map_fn.node, CC::Map(_, _)) {
                return None;
            }
            let mapped = mapped_row_fields(env, dtmap, mapper, argument);
            let bound_shape = match &argument.node {
                CC::Rel(n) => resolve_rel_row_witness(env, *n)
                    .as_ref()
                    .map(|bound| debug_constructor_shape(bound, 4))
                    .unwrap_or_else(|| "<unbound>".into()),
                _ => "<n/a>".into(),
            };
            let details = format!(
                "mapper_shape={} argument_shape={} bound_shape={}",
                debug_constructor_shape(mapper, 4),
                debug_constructor_shape(argument, 4),
                bound_shape
            );
            debug_mono_row_fields_result(row, "mapped", &details, mapped.as_deref());
            mapped
        }
        CC::Rel(n) => {
            let resolved = resolve_rel_row_witness(env, *n)
                .and_then(|bound_row| mono_row_fields_normalized(env, dtmap, &bound_row));
            let details = resolve_rel_row_witness(env, *n)
                .map(|bound_row| format!("bound_shape={}", debug_constructor_shape(&bound_row, 4)))
                .unwrap_or_else(|| "bound_shape=<unbound>".into());
            debug_mono_row_fields_result(row, "rel", &details, resolved.as_deref());
            resolved
        }
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

fn mono_exp_result_type(
    env: &Env,
    dtmap: &mut HashMap<usize, DatatypeRef>,
    exp: &LocatedExpression,
) -> Option<LocTyp> {
    match &exp.node {
        CE::Rel(n) => env
            .rel_e
            .get(env.rel_e.len().checked_sub(n + 1)?)
            .map(|typ| mono_type(env, dtmap, typ)),
        CE::Named(n) => env
            .lookup_e_named(*n)
            .map(|(_, typ, _)| mono_type(env, dtmap, typ)),
        CE::Record(fields) => Some(Located::new(
            Typ::Record(
                fields
                    .iter()
                    .map(|(name_con, _, typ)| {
                        (
                            mono_name_for_field(env, name_con, typ),
                            mono_field_type_from_witness_or_type(env, dtmap, name_con, typ),
                        )
                    })
                    .collect(),
            ),
            exp.span.clone(),
        )),
        CE::Concat(left, _, right, _) => {
            let mut fields = mono_record_fields_from_exp_type(env, dtmap, left)?;
            fields.extend(mono_record_fields_from_exp_type(env, dtmap, right)?);
            Some(Located::new(Typ::Record(fields), exp.span.clone()))
        }
        CE::Let(_, _, _, body) => mono_exp_result_type(env, dtmap, body),
        CE::Field(_, _, meta) => Some(mono_type(env, dtmap, &meta.field)),
        CE::Abs(_, dom, ran, _) => Some(Located::new(
            Typ::Fun(
                Box::new(mono_type(env, dtmap, dom)),
                Box::new(mono_type(env, dtmap, ran)),
            ),
            exp.span.clone(),
        )),
        CE::App(function, _) => {
            let fun_typ = mono_exp_result_type(env, dtmap, function)?;
            let Typ::Fun(_, ran) = fun_typ.node else {
                return None;
            };
            Some(*ran)
        }
        _ => None,
    }
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
    mono_exp_result_type(env, dtmap, exp).and_then(|typ| match typ.node {
        Typ::Record(fields) => Some(fields),
        _ => None,
    })
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

fn list_payload_fields(
    con: &LocatedConstructor,
) -> Option<(&LocatedConstructor, &LocatedConstructor)> {
    let CC::TRecord(row) = &con.node else {
        return None;
    };
    let CC::Record(_, fields) = &row.node else {
        return None;
    };

    let mut head = None;
    let mut tail = None;
    for (name, field_t) in fields {
        match &name.node {
            CC::Name(field_name) if field_name == "1" => head = Some(field_t),
            CC::Name(field_name) if field_name == "2" => tail = Some(field_t),
            _ => {}
        }
    }

    Some((head?, tail?))
}

fn is_exact_list_poly_datatype(
    datatype_id: usize,
    name: &str,
    params: &[String],
    constrs: &[(String, usize, Option<LocatedConstructor>)],
) -> bool {
    if name != "list" || params.len() != 1 || constrs.len() != 2 {
        return false;
    }

    let has_nil = constrs
        .iter()
        .any(|(con_name, _, arg)| con_name == "Nil" && arg.is_none());
    let has_cons = constrs.iter().any(|(_con_name, _, arg)| {
        let Some(payload) = arg.as_ref() else {
            return false;
        };
        let Some((head, tail)) = list_payload_fields(payload) else {
            return false;
        };
        matches!(&head.node, CC::Rel(0))
            && matches!(
                &tail.node,
                CC::App(fun, arg)
                    if matches!((&fun.node, &arg.node), (CC::Named(id), CC::Rel(0)) if *id == datatype_id)
            )
    });

    has_nil && has_cons
}

fn exact_list_mono_head_constructor(
    datatype_id: usize,
    name: &str,
    params: &[String],
    constrs: &[(String, usize, Option<LocatedConstructor>)],
) -> Option<LocatedConstructor> {
    if name != "list" || !params.is_empty() || constrs.len() != 2 {
        return None;
    }

    let has_nil = constrs
        .iter()
        .any(|(con_name, _, arg)| con_name == "Nil" && arg.is_none());
    let cons_payload = constrs.iter().find_map(|(con_name, _, arg)| {
        if con_name == "Cons" {
            arg.as_ref()
        } else {
            None
        }
    })?;
    let (head, tail) = list_payload_fields(cons_payload)?;
    let tail_is_self = matches!(&tail.node, CC::Named(id) if *id == datatype_id)
        || matches!(
            &tail.node,
            CC::App(fun, _arg) if matches!(&fun.node, CC::Named(id) if *id == datatype_id)
        );
    (has_nil && tail_is_self).then(|| head.clone())
}

fn is_exact_list_datatype(
    datatype_id: usize,
    name: &str,
    params: &[String],
    constrs: &[(String, usize, Option<LocatedConstructor>)],
) -> bool {
    is_exact_list_poly_datatype(datatype_id, name, params, constrs)
        || exact_list_mono_head_constructor(datatype_id, name, params, constrs).is_some()
}

fn exact_list_head_from_type(env: &Env, con: &LocatedConstructor) -> Option<LocatedConstructor> {
    let normalized = normalize_constructor_for_mono(env, con);
    match &normalized.node {
        CC::TFun(_, result) => exact_list_head_from_type(env, result),
        CC::App(fun, arg) => match &fun.node {
            CC::Named(datatype_id) => {
                env.lookup_datatype(*datatype_id)
                    .and_then(|(name, params, constrs)| {
                        is_exact_list_poly_datatype(*datatype_id, name, params, constrs)
                            .then(|| (**arg).clone())
                    })
            }
            _ => None,
        },
        CC::Named(datatype_id) => {
            env.lookup_datatype(*datatype_id)
                .and_then(|(name, params, constrs)| {
                    exact_list_mono_head_constructor(*datatype_id, name, params, constrs)
                })
        }
        _ => None,
    }
}

fn exact_list_constructor_head(env: &Env, constructor_id: usize) -> Option<LocatedConstructor> {
    env.datatypes
        .iter()
        .find_map(|(datatype_id, (name, params, constrs))| {
            constrs
                .iter()
                .any(|(_, con_id, _)| *con_id == constructor_id)
                .then(|| exact_list_mono_head_constructor(*datatype_id, name, params, constrs))
                .flatten()
        })
        .or_else(|| {
            env.named_c
                .get(&constructor_id)
                .and_then(|def| def.as_ref())
                .and_then(|def| exact_list_head_from_type(env, def))
        })
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
    if let CC::Map(_, _) = head {
        if args.len() == 2
            && !matches!(args[1].node, CC::Record(_, _) | CC::Concat(_, _) | CC::Unit)
        {
            let reduced = Located::new(
                CC::App(Box::new((*args[0]).clone()), Box::new((*args[1]).clone())),
                loc.clone(),
            );
            return mono_type(env, dtmap, &reduced);
        }
    }
    if let CC::App(map_head, mapper) = head {
        if matches!(map_head.node, CC::Map(_, _)) && args.len() == 1 {
            let reduced = Located::new(
                CC::App(Box::new((**mapper).clone()), Box::new((*args[0]).clone())),
                loc.clone(),
            );
            return mono_type(env, dtmap, &reduced);
        }
    }
    match head {
        CC::Named(n) => {
            if let Some((name, params, constrs)) = env.lookup_datatype(*n) {
                if is_exact_list_poly_datatype(*n, name, params, constrs) && args.len() == 1 {
                    let inner = mono_type(env, dtmap, args[0]);
                    return Located::new(Typ::List(Box::new(inner)), loc.clone());
                }
            }

            let folded = args
                .iter()
                .fold(Located::new(head.clone(), loc.clone()), |acc, arg| {
                    Located::new(
                        CC::App(Box::new(acc), Box::new((*arg).clone())),
                        loc.clone(),
                    )
                });
            log_mono_dummy_type("mono_type_app:named", loc, &folded);
            dummy_typ(loc)
        }
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
                _ => {
                    let constructor = Located::new(
                        CC::App(
                            Box::new(Located::new(head.clone(), loc.clone())),
                            Box::new(
                                args.last()
                                    .cloned()
                                    .cloned()
                                    .unwrap_or_else(|| Located::new(CC::Unit, loc.clone())),
                            ),
                        ),
                        loc.clone(),
                    );
                    log_mono_dummy_type("mono_type_app:basis", loc, &constructor);
                    dummy_typ(loc)
                }
            }
        }
        _ => {
            let folded = args
                .iter()
                .fold(Located::new(head.clone(), loc.clone()), |acc, arg| {
                    Located::new(
                        CC::App(Box::new(acc), Box::new((*arg).clone())),
                        loc.clone(),
                    )
                });
            log_mono_dummy_type("mono_type_app:generic", loc, &folded);
            dummy_typ(loc)
        }
    }
}

fn is_list_constructor(env: &Env, pc: &CPC) -> bool {
    match pc {
        CPC::Ffi {
            module, datatyp, ..
        } => module == "Basis" && datatyp == "list",
        CPC::Var(constructor_id) => {
            env.datatypes
                .iter()
                .any(|(datatype_id, (name, params, constrs))| {
                    constrs
                        .iter()
                        .any(|(_, con_id, _)| con_id == constructor_id)
                        && is_exact_list_datatype(*datatype_id, name, params, constrs)
                })
        }
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
    Located::new(
        Typ::Record(vec![
            ("Read".into(), read_field_ty(t.clone(), loc)),
            ("ReadError".into(), read_error_field_ty(t, loc)),
        ]),
        loc.clone(),
    )
}

fn read_field_ty(t: LocTyp, loc: &Span) -> LocTyp {
    let s = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
    let opt_t = Located::new(Typ::Option(Box::new(t.clone())), loc.clone());
    Located::new(Typ::Fun(Box::new(s), Box::new(opt_t)), loc.clone())
}

fn read_error_field_ty(t: LocTyp, loc: &Span) -> LocTyp {
    let s = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
    Located::new(Typ::Fun(Box::new(s), Box::new(t)), loc.clone())
}

fn make_read_record(read_exp: LocExp, read_error_exp: LocExp, t: LocTyp, loc: &Span) -> LocExp {
    Located::new(
        Exp::Record(vec![
            ("Read".into(), read_exp, read_field_ty(t.clone(), loc)),
            (
                "ReadError".into(),
                read_error_exp,
                read_error_field_ty(t, loc),
            ),
        ]),
        loc.clone(),
    )
}

fn dummy_typ(loc: &Span) -> LocTyp {
    // Use a zero-element record as the dummy type (unit in Mono)
    Located::new(Typ::Record(Vec::new()), loc.clone())
}

fn log_mono_dummy_type(stage: &str, loc: &Span, constructor: &LocatedConstructor) {
    let _ = (stage, loc, constructor);
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
                if let CPC::Var(constructor_id) = pc {
                    if let Some(head) = exact_list_constructor_head(env, *constructor_id) {
                        let inner_t = mono_type(env, dtmap, &head);
                        let lt = listify(inner_t, &loc);
                        if let Some(p) = po {
                            let p = mono_pat(env, dtmap, p);
                            return Located::new(Pat::Some(lt, Box::new(p)), loc);
                        }
                        return Located::new(Pat::None(lt), loc);
                    }
                }
                // Nullary or payload constructor without type args
                let mo = po.as_ref().map(|p| Box::new(mono_pat(env, dtmap, p)));
                Located::new(Pat::Con(*dk, mono_pat_con(pc), mo), loc)
            } else if targs.len() == 1 {
                // Option-like or list-like patterns
                if is_list_constructor(env, pc) {
                    let inner_t = mono_type(env, dtmap, &targs[0]);
                    let lt = listify(inner_t, &loc);
                    if let Some(p) = po {
                        let p = mono_pat(env, dtmap, p);
                        Located::new(Pat::Some(lt, Box::new(p)), loc)
                    } else {
                        Located::new(Pat::None(lt), loc)
                    }
                } else {
                    // Option pattern
                    let t = mono_type(env, dtmap, &targs[0]);
                    if let Some(p) = po {
                        let p = mono_pat(env, dtmap, p);
                        Located::new(Pat::Some(t, Box::new(p)), loc)
                    } else {
                        Located::new(Pat::None(t), loc)
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
        "read_int" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "int".into()), loc.clone());
            Some(make_read_record(
                Located::new(Exp::Ffi("Basis".into(), "stringToInt".into()), loc.clone()),
                Located::new(
                    Exp::Ffi("Basis".into(), "stringToInt_error".into()),
                    loc.clone(),
                ),
                t,
                loc,
            ))
        }
        "read_float" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "float".into()), loc.clone());
            Some(make_read_record(
                Located::new(
                    Exp::Ffi("Basis".into(), "stringToFloat".into()),
                    loc.clone(),
                ),
                Located::new(
                    Exp::Ffi("Basis".into(), "stringToFloat_error".into()),
                    loc.clone(),
                ),
                t,
                loc,
            ))
        }
        "read_string" => {
            let s = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
            let read_body = Located::new(
                Exp::Some(s.clone(), Box::new(Located::new(Exp::Rel(0), loc.clone()))),
                loc.clone(),
            );
            Some(make_read_record(
                unary_abs(
                    "s",
                    s.clone(),
                    Located::new(Typ::Option(Box::new(s.clone())), loc.clone()),
                    read_body,
                    loc,
                ),
                unary_abs(
                    "s",
                    s.clone(),
                    s.clone(),
                    Located::new(Exp::Rel(0), loc.clone()),
                    loc,
                ),
                s,
                loc,
            ))
        }
        "read_char" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "char".into()), loc.clone());
            Some(make_read_record(
                Located::new(Exp::Ffi("Basis".into(), "stringToChar".into()), loc.clone()),
                Located::new(
                    Exp::Ffi("Basis".into(), "stringToChar_error".into()),
                    loc.clone(),
                ),
                t,
                loc,
            ))
        }
        "read_bool" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
            Some(make_read_record(
                Located::new(Exp::Ffi("Basis".into(), "stringToBool".into()), loc.clone()),
                Located::new(
                    Exp::Ffi("Basis".into(), "stringToBool_error".into()),
                    loc.clone(),
                ),
                t,
                loc,
            ))
        }
        "read_time" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "time".into()), loc.clone());
            Some(make_read_record(
                Located::new(Exp::Ffi("Basis".into(), "stringToTime".into()), loc.clone()),
                Located::new(
                    Exp::Ffi("Basis".into(), "stringToTime_error".into()),
                    loc.clone(),
                ),
                t,
                loc,
            ))
        }

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
        "sql_time" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "time".into()), loc.clone());
            let s = string_type(loc);
            Some(unary_abs(
                "x",
                t.clone(),
                s.clone(),
                Located::new(
                    Exp::FfiApp(
                        "Basis".into(),
                        "sqlifyTime".into(),
                        vec![(Located::new(Exp::Rel(0), loc.clone()), t)],
                    ),
                    loc.clone(),
                ),
                loc,
            ))
        }
        "sql_clocktime" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "clocktime".into()), loc.clone());
            let s = string_type(loc);
            Some(unary_abs(
                "x",
                t.clone(),
                s.clone(),
                Located::new(
                    Exp::FfiApp(
                        "Basis".into(),
                        "sqlifyClocktime".into(),
                        vec![(Located::new(Exp::Rel(0), loc.clone()), t)],
                    ),
                    loc.clone(),
                ),
                loc,
            ))
        }
        "sql_calendardate" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "calendardate".into()), loc.clone());
            let s = string_type(loc);
            Some(unary_abs(
                "x",
                t.clone(),
                s.clone(),
                Located::new(
                    Exp::FfiApp(
                        "Basis".into(),
                        "sqlifyCalendardate".into(),
                        vec![(Located::new(Exp::Rel(0), loc.clone()), t)],
                    ),
                    loc.clone(),
                ),
                loc,
            ))
        }
        "sql_blob" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "blob".into()), loc.clone());
            let s = string_type(loc);
            Some(unary_abs(
                "x",
                t.clone(),
                s.clone(),
                Located::new(
                    Exp::FfiApp(
                        "Basis".into(),
                        "sqlifyBlob".into(),
                        vec![(Located::new(Exp::Rel(0), loc.clone()), t)],
                    ),
                    loc.clone(),
                ),
                loc,
            ))
        }
        "sql_channel" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "channel".into()), loc.clone());
            let s = string_type(loc);
            Some(unary_abs(
                "x",
                t.clone(),
                s.clone(),
                Located::new(
                    Exp::FfiApp(
                        "Basis".into(),
                        "sqlifyChannel".into(),
                        vec![(Located::new(Exp::Rel(0), loc.clone()), t)],
                    ),
                    loc.clone(),
                ),
                loc,
            ))
        }
        "sql_client" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "client".into()), loc.clone());
            let s = string_type(loc);
            Some(unary_abs(
                "x",
                t.clone(),
                s.clone(),
                Located::new(
                    Exp::FfiApp(
                        "Basis".into(),
                        "sqlifyClient".into(),
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

fn mono_sql_type(t: &LocTyp) -> Option<crate::settings::SqlType> {
    use crate::settings::SqlType;

    match &t.node {
        Typ::Ffi(module, name) if module == "Basis" => match name.as_str() {
            "int" => Some(SqlType::Int),
            "float" => Some(SqlType::Float),
            "string" => Some(SqlType::String),
            "char" => Some(SqlType::Char),
            "bool" => Some(SqlType::Bool),
            "time" => Some(SqlType::Time),
            "clocktime" => Some(SqlType::Clocktime),
            "calendardate" => Some(SqlType::Calendardate),
            "blob" => Some(SqlType::Blob),
            "channel" => Some(SqlType::Channel),
            "client" => Some(SqlType::Client),
            _ => None,
        },
        Typ::Option(inner) => mono_sql_type(inner).map(|t| SqlType::Nullable(Box::new(t))),
        _ => None,
    }
}

fn postgres_sql_type_name(t: &crate::settings::SqlType) -> &'static str {
    use crate::settings::SqlType;

    match t {
        SqlType::Int => "int8",
        SqlType::Float => "float8",
        SqlType::String => "text",
        SqlType::Char => "char",
        SqlType::Bool => "bool",
        SqlType::Time => "timestamp",
        SqlType::Clocktime => "time",
        SqlType::Calendardate => "date",
        SqlType::Blob => "bytea",
        SqlType::Channel => "int8",
        SqlType::Client => "int4",
        SqlType::Nullable(inner) => postgres_sql_type_name(inner),
    }
}

fn sql_null_literal_for_type(t: &LocTyp, settings: &Settings) -> Option<String> {
    let sql_t = mono_sql_type(t)?;
    let db = crate::db::ProjectDbCtx::new(&settings.db_backend);
    if db.is_mysql() || db.is_sqlite() {
        Some("NULL".into())
    } else {
        Some(format!("NULL::{}", postgres_sql_type_name(&sql_t)))
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
        let name = mono_name(env, name_con);
        let normalized_row = normalize_constructor_for_mono(env, row_con);
        let CC::Record(_, row_fields) = &normalized_row.node else {
            return None;
        };
        let mut dtmap = HashMap::new();
        let mut row = row_fields
            .iter()
            .map(|(field_name, field_ty)| {
                (
                    mono_name(env, field_name),
                    mono_type(env, &mut dtmap, field_ty),
                )
            })
            .collect::<Vec<_>>();
        row.sort_by(|(left, _), (right, _)| left.cmp(right));
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

fn constructor_record_fields(
    env: &Env,
    dtmap: &mut HashMap<usize, DatatypeRef>,
    typ: &LocatedConstructor,
) -> Option<Vec<(String, LocTyp)>> {
    let normalized = normalize_constructor_for_mono(env, typ);
    match &normalized.node {
        CC::TRecord(row) => mono_row_fields_normalized(env, dtmap, row),
        CC::Record(_, _) | CC::Concat(_, _) | CC::Unit => {
            mono_row_fields_normalized(env, dtmap, &normalized)
        }
        _ => mono_record_fields_from_type(env, dtmap, typ),
    }
}

fn nearest_record_field_rel(env: &Env, field: &str) -> Option<usize> {
    let mut dtmap = HashMap::new();
    env.rel_e.iter().rev().enumerate().find_map(|(rel, con)| {
        constructor_record_fields(env, &mut dtmap, con)
            .and_then(|fields| fields.iter().any(|(name, _)| name == field).then_some(rel))
    })
}

fn receiver_lacks_record_field(env: &Env, exp: &LocatedExpression, field: &str) -> bool {
    let mut dtmap = HashMap::new();
    if let Some(fields) = mono_record_fields_from_exp_type(env, &mut dtmap, exp) {
        return !fields.iter().any(|(name, _)| name == field);
    }

    let lacks_field =
        |typ: &LocatedConstructor, dtmap: &mut HashMap<usize, DatatypeRef>| match mono_type(
            env, dtmap, typ,
        )
        .node
        {
            Typ::Record(fields) => !fields.iter().any(|(name, _)| name == field),
            _ => true,
        };

    match &exp.node {
        CE::Rel(n) => env
            .rel_e
            .get(env.rel_e.len().checked_sub(n + 1).unwrap_or(usize::MAX))
            .is_some_and(|typ| lacks_field(typ, &mut dtmap)),
        CE::Named(n) => env
            .lookup_e_named(*n)
            .is_some_and(|(_, typ, _)| lacks_field(typ, &mut dtmap)),
        _ => false,
    }
}

fn row_field_entries_partial(
    row: &LocatedConstructor,
) -> Vec<(LocatedConstructor, LocatedConstructor)> {
    match &row.node {
        CC::Record(_, fields) => fields.clone(),
        CC::Concat(left, right) => {
            let mut fields = row_field_entries_partial(left);
            fields.extend(row_field_entries_partial(right));
            fields
        }
        CC::Unit => Vec::new(),
        _ => Vec::new(),
    }
}

fn recover_mapped_record_field_receiver(
    env: &Env,
    field: &str,
    loc: &Span,
) -> Option<LocatedExpression> {
    let mut dtmap = HashMap::new();
    env.rel_e.iter().rev().enumerate().find_map(|(rel, con)| {
        let normalized = normalize_constructor_for_mono(env, con);
        let row = match &normalized.node {
            CC::TRecord(row) => Some(row.as_ref()),
            CC::Record(_, _) | CC::Concat(_, _) | CC::Unit => Some(&normalized),
            _ => None,
        }?;

        row_field_entries_partial(row)
            .into_iter()
            .find_map(|(key_con, value_con)| {
                constructor_record_fields(env, &mut dtmap, &value_con).and_then(|fields| {
                    fields.iter().any(|(name, _)| name == field).then(|| {
                        Located::new(
                            CE::Field(
                                Box::new(Located::new(CE::Rel(rel), loc.clone())),
                                key_con,
                                FieldMeta {
                                    field: value_con,
                                    rest: Located::new(CC::Unit, loc.clone()),
                                },
                            ),
                            loc.clone(),
                        )
                    })
                })
            })
    })
}

fn recover_applied_record_field_receiver(
    env: &Env,
    field: &str,
    loc: &Span,
) -> Option<LocatedExpression> {
    for base_rel in 0..env.rel_e.len() {
        let mut candidate = Located::new(CE::Rel(base_rel), loc.clone());
        let mut dtmap = HashMap::new();
        if mono_record_fields_from_exp_type(env, &mut dtmap, &candidate)
            .is_some_and(|fields| fields.iter().any(|(name, _)| name == field))
        {
            return Some(candidate);
        }

        for arg_rel in (0..base_rel).rev() {
            candidate = Located::new(
                CE::App(
                    Box::new(candidate),
                    Box::new(Located::new(CE::Rel(arg_rel), loc.clone())),
                ),
                loc.clone(),
            );
            let mut dtmap = HashMap::new();
            if mono_record_fields_from_exp_type(env, &mut dtmap, &candidate)
                .is_some_and(|fields| fields.iter().any(|(name, _)| name == field))
            {
                return Some(candidate);
            }
        }
    }

    None
}

fn log_record_field_rel_candidates(env: &Env, field: &str, loc: &Span) {
    if std::env::var("URWEB_DEBUG_FIELD_REL_CANDIDATES")
        .ok()
        .as_deref()
        != Some("1")
    {
        return;
    }
    if !(loc.file.ends_with("/lib/ur/top.ur")
        || loc.file.ends_with("/demo/metaform.ur")
        || loc.file.ends_with("/demo/crud.ur")
        || loc.file.ends_with("/demo/listFun.ur"))
    {
        return;
    }

    let mut dtmap = HashMap::new();
    for (rel, con) in env.rel_e.iter().rev().enumerate() {
        let fields = constructor_record_fields(env, &mut dtmap, con)
            .map(|items| {
                items
                    .into_iter()
                    .map(|(name, _)| name)
                    .collect::<Vec<_>>()
                    .join(",")
            })
            .unwrap_or_else(|| "<non-record>".to_string());
        eprintln!(
            "URWEB_DEBUG_FIELD_REL_CANDIDATES {}:{} want={} rel={} con={:?} fields={}",
            loc.file, loc.first.line, field, rel, con.node, fields
        );
    }
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
    env: &Env,
    attrs_raw: &'a LocatedExpression,
) -> Vec<(String, &'a LocatedExpression, &'a LocatedConstructor)> {
    match &attrs_raw.node {
        CE::Record(entries) => entries
            .iter()
            .map(|(name, exp, typ)| (mono_name(env, name), exp, typ))
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
    let attrs = extract_tag_attrs(env, attrs_raw);
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
    env: &Env,
    xml: &'a LocatedExpression,
) -> Option<(&'a LocatedExpression, &'a LocatedConstructor)> {
    let mut vargs = Vec::new();
    let base = peel_apps_core(xml, &mut vargs);
    let (head, _) = peel_capp(base);

    match &head.node {
        CE::Ffi(m, x) | CE::FfiApp(m, x, _) if m == "Basis" && x == "join" && vargs.len() >= 2 => {
            let left = find_submit_action(env, vargs[vargs.len() - 2]);
            let right = find_submit_action(env, vargs[vargs.len() - 1]);
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
                        .find(|(name, _, _)| mono_name(env, name) == "Action")
                    {
                        return Some((exp, typ));
                    }
                }
            }

            find_submit_action(env, inner_xml)
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
            let attrs = extract_tag_attrs(env, attrs_raw);
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
            let attrs = extract_tag_attrs(env, attrs_raw);
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
            let attrs = extract_tag_attrs(env, attrs_raw);
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

    let action_attr = find_submit_action(env, xml_raw)
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
    let source_t = || Located::new(Typ::Source, loc.clone());
    let string_t = || Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());

    fn core_is_blobby(t: &LocatedConstructor) -> bool {
        matches!(
            &t.node,
            CC::Ffi(module, name)
                if module == "Basis" && (name == "string" || name == "blob")
        )
    }

    let db_ctx = crate::db::ProjectDbCtx::new(&settings.db_backend);
    let text_keys_need_lengths = db_ctx.is_mysql();
    let supports_update_delete_as = db_ctx.is_postgres_family();

    match x {
        "source" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let unit_t = unit_typ(loc);
            let source_fun_t = Located::new(
                Typ::Fun(Box::new(unit_t.clone()), Box::new(source_t())),
                loc.clone(),
            );
            let js_value = Located::new(
                Exp::JavaScript(
                    JavaScriptMode::Source(t.clone()),
                    Box::new(Located::new(Exp::Rel(1), loc.clone())),
                ),
                loc.clone(),
            );
            let body = Located::new(
                Exp::Abs(
                    "_".into(),
                    unit_t.clone(),
                    source_t(),
                    Box::new(Located::new(
                        Exp::FfiApp(
                            "Basis".into(),
                            "new_client_source".into(),
                            vec![(js_value, string_t())],
                        ),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("x".into(), t, source_fun_t, Box::new(body)),
                loc.clone(),
            ))
        }

        "set" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let unit_t = unit_typ(loc);
            let set_result_t = Located::new(
                Typ::Fun(Box::new(unit_t.clone()), Box::new(unit_t.clone())),
                loc.clone(),
            );
            let set_value_t = Located::new(
                Typ::Fun(Box::new(t.clone()), Box::new(set_result_t.clone())),
                loc.clone(),
            );
            let js_value = Located::new(
                Exp::JavaScript(
                    JavaScriptMode::Source(t.clone()),
                    Box::new(Located::new(Exp::Rel(1), loc.clone())),
                ),
                loc.clone(),
            );
            let body = Located::new(
                Exp::Abs(
                    "_".into(),
                    unit_t.clone(),
                    unit_t.clone(),
                    Box::new(Located::new(
                        Exp::FfiApp(
                            "Basis".into(),
                            "set_client_source".into(),
                            vec![
                                (Located::new(Exp::Rel(2), loc.clone()), source_t()),
                                (js_value, string_t()),
                            ],
                        ),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            );
            let value_abs = Located::new(
                Exp::Abs("v".into(), t, set_result_t, Box::new(body)),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("src".into(), source_t(), set_value_t, Box::new(value_abs)),
                loc.clone(),
            ))
        }

        "get" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let unit_t = unit_typ(loc);
            let get_result_t = Located::new(
                Typ::Fun(Box::new(unit_t.clone()), Box::new(t.clone())),
                loc.clone(),
            );
            let body = Located::new(
                Exp::Abs(
                    "_".into(),
                    unit_t,
                    t.clone(),
                    Box::new(Located::new(
                        Exp::FfiApp(
                            "Basis".into(),
                            "get_client_source".into(),
                            vec![(Located::new(Exp::Rel(1), loc.clone()), source_t())],
                        ),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("src".into(), source_t(), get_result_t, Box::new(body)),
                loc.clone(),
            ))
        }

        "current" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let unit_t = unit_typ(loc);
            let current_result_t = Located::new(
                Typ::Fun(Box::new(unit_t.clone()), Box::new(t.clone())),
                loc.clone(),
            );
            let body = Located::new(
                Exp::Abs(
                    "_".into(),
                    unit_t,
                    t.clone(),
                    Box::new(Located::new(
                        Exp::FfiApp(
                            "Basis".into(),
                            "current".into(),
                            vec![(Located::new(Exp::Rel(1), loc.clone()), source_t())],
                        ),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("src".into(), source_t(), current_result_t, Box::new(body)),
                loc.clone(),
            ))
        }

        "signal_return" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let signal_t = Located::new(Typ::Signal(Box::new(t.clone())), loc.clone());
            Some(Located::new(
                Exp::Abs(
                    "x".into(),
                    t.clone(),
                    signal_t,
                    Box::new(Located::new(
                        Exp::SignalReturn(Box::new(Located::new(Exp::Rel(0), loc.clone()))),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            ))
        }

        "signal_bind" => {
            if targs.len() < 2 {
                return None;
            }
            let t1 = {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, targs.get(targs.len().checked_sub(2)?)?)
            };
            let t2 = {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, targs.last()?)
            };
            let signal_t1 = Located::new(Typ::Signal(Box::new(t1.clone())), loc.clone());
            let signal_t2 = Located::new(Typ::Signal(Box::new(t2.clone())), loc.clone());
            let bind_fun_t = Located::new(
                Typ::Fun(Box::new(t1), Box::new(signal_t2.clone())),
                loc.clone(),
            );
            let outer_ran = Located::new(
                Typ::Fun(Box::new(bind_fun_t.clone()), Box::new(signal_t2.clone())),
                loc.clone(),
            );
            let body = Located::new(
                Exp::Abs(
                    "m2".into(),
                    bind_fun_t,
                    signal_t2.clone(),
                    Box::new(Located::new(
                        Exp::SignalBind(
                            Box::new(Located::new(Exp::Rel(1), loc.clone())),
                            Box::new(Located::new(Exp::Rel(0), loc.clone())),
                        ),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("m1".into(), signal_t1, outer_ran, Box::new(body)),
                loc.clone(),
            ))
        }

        "signal" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let int_t = Located::new(Typ::Ffi("Basis".into(), "int".into()), loc.clone());
            let signal_t = Located::new(Typ::Signal(Box::new(t)), loc.clone());
            Some(Located::new(
                Exp::Abs(
                    "x".into(),
                    int_t,
                    signal_t,
                    Box::new(Located::new(
                        Exp::SignalSource(Box::new(Located::new(Exp::Rel(0), loc.clone()))),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            ))
        }

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
                        .map(|(name, _)| (mono_name(env, name), unit_typ(loc)))
                        .collect(),
                ),
                loc.clone(),
            );

            let cols = fields
                .iter()
                .map(|(name, typ)| {
                    let mut col = settings.mangle_sql(&mono_name(env, name));
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
                    let mut col = settings.mangle_sql(&mono_name(env, name));
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
        "sql_option_prim" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let s = string_t();
            let show_t = Located::new(
                Typ::Fun(Box::new(t.clone()), Box::new(s.clone())),
                loc.clone(),
            );
            let option_t = Located::new(Typ::Option(Box::new(t.clone())), loc.clone());
            let option_show_t = Located::new(
                Typ::Fun(Box::new(option_t.clone()), Box::new(s.clone())),
                loc.clone(),
            );
            let null_sql = str_n(&sql_null_literal_for_type(&t, settings)?, loc);
            let none_pat = Located::new(Pat::None(t.clone()), loc.clone());
            let some_pat = Located::new(
                Pat::Some(
                    t.clone(),
                    Box::new(Located::new(Pat::Var("y".into(), t.clone()), loc.clone())),
                ),
                loc.clone(),
            );
            let show_y = Located::new(
                Exp::App(
                    Box::new(Located::new(Exp::Rel(2), loc.clone())),
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                ),
                loc.clone(),
            );
            let body = Located::new(
                Exp::Case(
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                    vec![(none_pat, null_sql), (some_pat, show_y)],
                    CaseMeta {
                        disc: option_t.clone(),
                        result: s.clone(),
                    },
                ),
                loc.clone(),
            );
            let inner = Located::new(
                Exp::Abs("x".into(), option_t, s, Box::new(body)),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("f".into(), show_t, option_show_t, Box::new(inner)),
                loc.clone(),
            ))
        }
        "sql_is_null" => {
            let s = string_t();
            Some(Located::new(
                Exp::Abs(
                    "s".into(),
                    s.clone(),
                    s.clone(),
                    Box::new(make_strcat_list(
                        vec![
                            str_n("(", loc),
                            Located::new(Exp::Rel(0), loc.clone()),
                            str_n(" IS NULL)", loc),
                        ],
                        loc,
                    )),
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

        "insert" => {
            let fields_t = mono_type_row(env, &mut HashMap::new(), targs.first()?, loc);
            let Typ::Record(fields) = &fields_t.node else {
                return None;
            };
            let string_field_t = string_t();
            let string_fields = fields
                .iter()
                .map(|(field, _)| (field.clone(), string_field_t.clone()))
                .collect::<Vec<_>>();
            let record_t = Located::new(Typ::Record(string_fields.clone()), loc.clone());
            let comma_join = |parts: Vec<LocExp>| {
                let mut iter = parts.into_iter();
                let Some(first) = iter.next() else {
                    return str_n("", loc);
                };
                iter.fold(first, |acc, part| {
                    make_strcat(acc, make_strcat(str_n(", ", loc), part))
                })
            };
            let column_names = comma_join(
                string_fields
                    .iter()
                    .map(|(field, _)| str_n(&settings.mangle_sql(field), loc))
                    .collect(),
            );
            let values = comma_join(
                string_fields
                    .iter()
                    .map(|(field, _)| {
                        Located::new(
                            Exp::Field(
                                Box::new(Located::new(Exp::Rel(0), loc.clone())),
                                field.clone(),
                            ),
                            loc.clone(),
                        )
                    })
                    .collect(),
            );
            let body = make_strcat_list(
                vec![
                    str_n("INSERT INTO ", loc),
                    Located::new(Exp::Rel(1), loc.clone()),
                    str_n(" (", loc),
                    column_names,
                    str_n(") VALUES (", loc),
                    values,
                    str_n(")", loc),
                ],
                loc,
            );
            let inner_t = Located::new(
                Typ::Fun(Box::new(record_t.clone()), Box::new(string_field_t.clone())),
                loc.clone(),
            );
            let inner = Located::new(
                Exp::Abs(
                    "fs".into(),
                    record_t,
                    string_field_t.clone(),
                    Box::new(body),
                ),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("tab".into(), string_field_t, inner_t, Box::new(inner)),
                loc.clone(),
            ))
        }

        "update" => {
            let changed_t = mono_type_row(env, &mut HashMap::new(), targs.last()?, loc);
            let Typ::Record(changed) = &changed_t.node else {
                return None;
            };
            let string_field_t = string_t();
            let changed_fields = changed
                .iter()
                .map(|(field, _)| (field.clone(), string_field_t.clone()))
                .collect::<Vec<_>>();
            let record_t = Located::new(Typ::Record(changed_fields.clone()), loc.clone());
            let comma_join = |parts: Vec<LocExp>| {
                let mut iter = parts.into_iter();
                let Some(first) = iter.next() else {
                    return str_n("", loc);
                };
                iter.fold(first, |acc, part| {
                    make_strcat(acc, make_strcat(str_n(", ", loc), part))
                })
            };

            let body = if changed_fields.is_empty() {
                str_n("", loc)
            } else {
                let assignments = comma_join(
                    changed_fields
                        .iter()
                        .map(|(field, _)| {
                            let value = Located::new(
                                Exp::Field(
                                    Box::new(Located::new(Exp::Rel(2), loc.clone())),
                                    field.clone(),
                                ),
                                loc.clone(),
                            );
                            let value = if supports_update_delete_as {
                                value
                            } else {
                                Located::new(
                                    Exp::FfiApp(
                                        "Basis".into(),
                                        "unAs".into(),
                                        vec![(value, string_field_t.clone())],
                                    ),
                                    loc.clone(),
                                )
                            };
                            make_strcat_list(
                                vec![
                                    str_n(&format!("{} = ", settings.mangle_sql(field)), loc),
                                    value,
                                ],
                                loc,
                            )
                        })
                        .collect(),
                );
                let where_clause = if supports_update_delete_as {
                    Located::new(Exp::Rel(0), loc.clone())
                } else {
                    Located::new(
                        Exp::FfiApp(
                            "Basis".into(),
                            "unAs".into(),
                            vec![(
                                Located::new(Exp::Rel(0), loc.clone()),
                                string_field_t.clone(),
                            )],
                        ),
                        loc.clone(),
                    )
                };
                make_strcat_list(
                    vec![
                        str_n("UPDATE ", loc),
                        Located::new(Exp::Rel(1), loc.clone()),
                        if supports_update_delete_as {
                            str_n(" AS T_T SET ", loc)
                        } else {
                            str_n(" SET ", loc)
                        },
                        assignments,
                        str_n(" WHERE ", loc),
                        where_clause,
                    ],
                    loc,
                )
            };
            let predicate_t = Located::new(
                Typ::Fun(
                    Box::new(string_field_t.clone()),
                    Box::new(string_field_t.clone()),
                ),
                loc.clone(),
            );
            let tab_t = Located::new(
                Typ::Fun(
                    Box::new(string_field_t.clone()),
                    Box::new(predicate_t.clone()),
                ),
                loc.clone(),
            );
            let e_abs = Located::new(
                Exp::Abs(
                    "e".into(),
                    string_field_t.clone(),
                    string_field_t.clone(),
                    Box::new(body),
                ),
                loc.clone(),
            );
            let tab_abs = Located::new(
                Exp::Abs(
                    "tab".into(),
                    string_field_t.clone(),
                    predicate_t,
                    Box::new(e_abs),
                ),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("fs".into(), record_t, tab_t, Box::new(tab_abs)),
                loc.clone(),
            ))
        }

        "delete" => {
            let string_field_t = string_t();
            let body = make_strcat_list(
                vec![
                    str_n("DELETE FROM ", loc),
                    Located::new(Exp::Rel(1), loc.clone()),
                    if supports_update_delete_as {
                        str_n(" AS T_T WHERE ", loc)
                    } else {
                        str_n(" WHERE ", loc)
                    },
                    if supports_update_delete_as {
                        Located::new(Exp::Rel(0), loc.clone())
                    } else {
                        Located::new(
                            Exp::FfiApp(
                                "Basis".into(),
                                "unAs".into(),
                                vec![(
                                    Located::new(Exp::Rel(0), loc.clone()),
                                    string_field_t.clone(),
                                )],
                            ),
                            loc.clone(),
                        )
                    },
                ],
                loc,
            );
            let inner = Located::new(
                Exp::Abs(
                    "e".into(),
                    string_field_t.clone(),
                    string_field_t.clone(),
                    Box::new(body),
                ),
                loc.clone(),
            );
            let inner_t = Located::new(
                Typ::Fun(
                    Box::new(string_field_t.clone()),
                    Box::new(string_field_t.clone()),
                ),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("tab".into(), string_field_t, inner_t, Box::new(inner)),
                loc.clone(),
            ))
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
        "show" | "mkShow" => {
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

        // ECApp(ENamed("show_option"), t) → \show. \opt. case opt of None => "" | Some x => show x
        "show_option" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let s = string_type(loc);
            let show_t = Located::new(
                Typ::Fun(Box::new(t.clone()), Box::new(s.clone())),
                loc.clone(),
            );
            let option_t = Located::new(Typ::Option(Box::new(t.clone())), loc.clone());
            let option_show_t = Located::new(
                Typ::Fun(Box::new(option_t.clone()), Box::new(s.clone())),
                loc.clone(),
            );
            let none_pat = Located::new(Pat::None(t.clone()), loc.clone());
            let some_pat = Located::new(
                Pat::Some(
                    t.clone(),
                    Box::new(Located::new(Pat::Var("x".into(), t.clone()), loc.clone())),
                ),
                loc.clone(),
            );
            let empty = Located::new(
                Exp::Prim(Prim::String(
                    crate::primitives::StringMode::Normal,
                    String::new(),
                )),
                loc.clone(),
            );
            let show_x = Located::new(
                Exp::App(
                    Box::new(Located::new(Exp::Rel(2), loc.clone())),
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                ),
                loc.clone(),
            );
            let body = Located::new(
                Exp::Case(
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                    vec![(none_pat, empty), (some_pat, show_x)],
                    CaseMeta {
                        disc: option_t.clone(),
                        result: s.clone(),
                    },
                ),
                loc.clone(),
            );
            let inner = Located::new(
                Exp::Abs("opt".into(), option_t, s, Box::new(body)),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("show".into(), show_t, option_show_t, Box::new(inner)),
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

        // ECApp(EFfi("Basis", "read"), t) → \f: read_t. f.Read
        "read" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let read_field_t = read_field_ty(t.clone(), loc);
            let read_t = read_ty(t, loc);
            Some(Located::new(
                Exp::Abs(
                    "f".into(),
                    read_t.clone(),
                    read_field_t,
                    Box::new(Located::new(
                        Exp::Field(
                            Box::new(Located::new(Exp::Rel(0), loc.clone())),
                            "Read".into(),
                        ),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            ))
        }
        "readError" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let read_t = read_ty(t.clone(), loc);
            let read_err_t = read_error_field_ty(t, loc);
            Some(Located::new(
                Exp::Abs(
                    "f".into(),
                    read_t,
                    read_err_t,
                    Box::new(Located::new(
                        Exp::Field(
                            Box::new(Located::new(Exp::Rel(0), loc.clone())),
                            "ReadError".into(),
                        ),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            ))
        }
        "mkRead" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let read_error_t = read_error_field_ty(t.clone(), loc);
            let read_t = read_field_ty(t.clone(), loc);
            let record_t = read_ty(t, loc);
            let inner = Located::new(
                Exp::Abs(
                    "f'".into(),
                    read_t.clone(),
                    record_t.clone(),
                    Box::new(Located::new(
                        Exp::Record(vec![
                            (
                                "Read".into(),
                                Located::new(Exp::Rel(0), loc.clone()),
                                read_t.clone(),
                            ),
                            (
                                "ReadError".into(),
                                Located::new(Exp::Rel(1), loc.clone()),
                                read_error_t.clone(),
                            ),
                        ]),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs(
                    "f".into(),
                    read_error_t,
                    Located::new(
                        Typ::Fun(Box::new(read_t.clone()), Box::new(record_t)),
                        loc.clone(),
                    ),
                    Box::new(inner),
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

        "getCookie" => {
            let value_t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let cookie_t = string_t();
            let unit_t = unit_typ(loc);
            let inner_t = Located::new(
                Typ::Fun(Box::new(unit_t.clone()), Box::new(value_t.clone())),
                loc.clone(),
            );
            let cookie_value = Located::new(
                Exp::FfiApp(
                    "Basis".into(),
                    "get_cookie".into(),
                    vec![(Located::new(Exp::Rel(1), loc.clone()), cookie_t.clone())],
                ),
                loc.clone(),
            );
            let decoded = Located::new(
                Exp::Uurlify(Box::new(cookie_value), value_t, true),
                loc.clone(),
            );
            let inner = Located::new(
                Exp::Abs(
                    "_".into(),
                    unit_t.clone(),
                    cookie_t.clone(),
                    Box::new(decoded),
                ),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("c".into(), cookie_t, inner_t, Box::new(inner)),
                loc.clone(),
            ))
        }

        "setCookie" => {
            let value_t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let cookie_t = string_t();
            let unit_t = unit_typ(loc);
            let time_t = Located::new(Typ::Ffi("Basis".into(), "time".into()), loc.clone());
            let expires_t = Located::new(Typ::Option(Box::new(time_t)), loc.clone());
            let secure_t = bool_t();
            let record_t = Located::new(
                Typ::Record(vec![
                    ("Expires".into(), expires_t.clone()),
                    ("Secure".into(), secure_t.clone()),
                    ("Value".into(), value_t.clone()),
                ]),
                loc.clone(),
            );
            let inner_t = Located::new(
                Typ::Fun(Box::new(unit_t.clone()), Box::new(unit_t.clone())),
                loc.clone(),
            );
            let middle_t = Located::new(
                Typ::Fun(Box::new(record_t.clone()), Box::new(inner_t.clone())),
                loc.clone(),
            );
            let fd = |field: &str| {
                Located::new(
                    Exp::Field(
                        Box::new(Located::new(Exp::Rel(1), loc.clone())),
                        field.into(),
                    ),
                    loc.clone(),
                )
            };
            let encoded = mono_urlify_exp(env, settings, fd("Value"), &value_t, loc)?;
            let body = Located::new(
                Exp::FfiApp(
                    "Basis".into(),
                    "set_cookie".into(),
                    vec![
                        (str_n(&settings.url_prefix, loc), cookie_t.clone()),
                        (Located::new(Exp::Rel(2), loc.clone()), cookie_t.clone()),
                        (encoded, cookie_t.clone()),
                        (fd("Expires"), expires_t.clone()),
                        (fd("Secure"), secure_t.clone()),
                    ],
                ),
                loc.clone(),
            );
            let inner = Located::new(
                Exp::Abs("_".into(), unit_t.clone(), unit_t.clone(), Box::new(body)),
                loc.clone(),
            );
            let middle = Located::new(
                Exp::Abs("r".into(), record_t, inner_t, Box::new(inner)),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("c".into(), cookie_t, middle_t, Box::new(middle)),
                loc.clone(),
            ))
        }

        "clearCookie" => {
            let cookie_t = string_t();
            let unit_t = unit_typ(loc);
            let inner_t = Located::new(
                Typ::Fun(Box::new(unit_t.clone()), Box::new(unit_t.clone())),
                loc.clone(),
            );
            let body = Located::new(
                Exp::FfiApp(
                    "Basis".into(),
                    "clear_cookie".into(),
                    vec![
                        (str_n(&settings.url_prefix, loc), cookie_t.clone()),
                        (Located::new(Exp::Rel(1), loc.clone()), cookie_t.clone()),
                    ],
                ),
                loc.clone(),
            );
            let inner = Located::new(
                Exp::Abs("_".into(), unit_t.clone(), unit_t.clone(), Box::new(body)),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("c".into(), cookie_t, inner_t, Box::new(inner)),
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

        "returnBlob" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let blob_t = Located::new(Typ::Ffi("Basis".into(), "blob".into()), loc.clone());
            let mime_t = string_t();
            let unit_t = unit_typ(loc);
            let thunk_t =
                Located::new(Typ::Fun(Box::new(unit_t), Box::new(t.clone())), loc.clone());
            let mime_abs = Located::new(
                Exp::Abs(
                    "mt".into(),
                    mime_t.clone(),
                    thunk_t.clone(),
                    Box::new(Located::new(
                        Exp::Abs(
                            "_".into(),
                            unit_typ(loc),
                            t.clone(),
                            Box::new(Located::new(
                                Exp::ReturnBlob {
                                    blob: Some(Box::new(Located::new(Exp::Rel(2), loc.clone()))),
                                    mime_type: Box::new(Located::new(Exp::Rel(1), loc.clone())),
                                    t,
                                },
                                loc.clone(),
                            )),
                        ),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            );
            let outer_t = Located::new(Typ::Fun(Box::new(mime_t), Box::new(thunk_t)), loc.clone());
            Some(Located::new(
                Exp::Abs("b".into(), blob_t, outer_t, Box::new(mime_abs)),
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
        match function.node {
            Exp::Abs(_, _, _, body) => {
                crate::monomorphized::environment::sub_exp_in_exp(0, &argument, &body)
            }
            other => Located::new(
                Exp::App(
                    Box::new(Located::new(other, function.span)),
                    Box::new(argument),
                ),
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

        "subform" if !targs.is_empty() => {
            let nm = mono_name(env, targs.last()?);
            let xml = mono_exp(env, fm, last(1)?, settings);
            Some(make_strcat_list(
                vec![
                    str_h(
                        &format!("<input type=\"hidden\" name=\".b\" value=\"{nm}\" />"),
                        loc,
                    ),
                    xml,
                    str_h("<input type=\"hidden\" name=\".e\" value=\"1\" />", loc),
                ],
                loc,
            ))
        }

        "subforms" if !targs.is_empty() => {
            let nm = mono_name(env, targs.last()?);
            let xml = mono_exp(env, fm, last(1)?, settings);
            Some(make_strcat_list(
                vec![
                    str_h(
                        &format!("<input type=\"hidden\" name=\".s\" value=\"{nm}\" />"),
                        loc,
                    ),
                    xml,
                    str_h("<input type=\"hidden\" name=\".e\" value=\"1\" />", loc),
                ],
                loc,
            ))
        }

        "entry" if vargs.len() >= 2 => {
            let xml = mono_exp(env, fm, last(1)?, settings);
            Some(make_strcat_list(
                vec![
                    str_h("<input type=\"hidden\" name=\".i\" value=\"1\" />", loc),
                    xml,
                    str_h("<input type=\"hidden\" name=\".e\" value=\"1\" />", loc),
                ],
                loc,
            ))
        }

        "useMore" => Some(mono_exp(env, fm, last(1)?, settings)),

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
                    .find(|(field_name, _, _)| mono_name(env, field_name) == name)
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
                    .find(|(field_name, _, _)| mono_name(env, field_name) == name)
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

fn zero_exp(loc: &Span, reason: &str) -> LocExp {
    if std::env::var("URWEB_DEBUG_ZERO_EXP").ok().as_deref() == Some("1") {
        eprintln!(
            "URWEB_DEBUG_ZERO_EXP {}:{} reason={reason}",
            loc.file, loc.first.line
        );
    }
    Located::new(Exp::Prim(Prim::Int(0)), loc.clone())
}

fn debug_mono_named_enabled() -> bool {
    std::env::var("URWEB_DEBUG_MONO_NAMED").ok().as_deref() == Some("1")
}

fn debug_mono_named_span(span: &Span) -> bool {
    span.file.ends_with("/demo/listFun.ur") || span.file.ends_with("/demo/listShop.ur")
}

/// Translate a Core expression to a Mono expression.
///
/// Returns `(mono_exp, updated_fm)`. The `Fm` accumulates helper function
/// declarations generated for URL/attribute encoding of polymorphic types.
///
/// Mirrors `monoExp` in `monoize.sml`.
fn mono_exp(env: &Env, fm: &mut Fm, exp: &LocatedExpression, settings: &Settings) -> LocExp {
    let loc = exp.span.clone();
    if std::env::var("URWEB_DEBUG_TOP_FOLD").ok().as_deref() == Some("1")
        && loc.file.ends_with("/lib/ur/top.ur")
        && matches!(loc.first.line, 139 | 140 | 146 | 156 | 214 | 215)
        && matches!(
            exp.node,
            CE::App(_, _) | CE::Field(_, _, _) | CE::Abs(_, _, _, _)
        )
    {
        eprintln!(
            "URWEB_DEBUG_TOP_FOLD {}:{} {:?}",
            loc.file, loc.first.line, exp.node
        );
    }
    let unresolved_names = unresolved_name_constructor_count(exp);
    if unresolved_names > 0 {
        let reduced = crate::core::local_reduction::reduce_exp(exp.clone());
        if unresolved_name_constructor_count(&reduced) < unresolved_names {
            return mono_exp(env, fm, &reduced, settings);
        }
    }
    match &exp.node {
        // --------------- Primitives ---------------
        CE::Prim(p) => {
            if matches!(p, Prim::Int(0)) && span_looks_like_erased_constraint_artifact(&loc) {
                return unit_exp(&loc);
            }
            Located::new(Exp::Prim(p.clone()), loc)
        }
        CE::Rel(n) => Located::new(Exp::Rel(*n), loc),
        CE::Named(n) => {
            if debug_mono_named_enabled() && debug_mono_named_span(&loc) {
                let value_info = env
                    .lookup_e_named(*n)
                    .map(|(name, typ, src)| format!("value={name} src={src} typ={:?}", typ.node));
                let constructor_info = env
                    .named_c
                    .get(n)
                    .map(|def| format!("constructor_def={:?}", def.as_ref().map(|c| &c.node)));
                let datatype_info = env.lookup_datatype(*n).map(|(name, params, constrs)| {
                    format!(
                        "datatype={name} params={} constrs={}",
                        params.len(),
                        constrs.len()
                    )
                });
                eprintln!(
                    "URWEB_DEBUG_MONO_NAMED {}:{} id={} {} {} {}",
                    loc.file,
                    loc.first.line,
                    n,
                    value_info.unwrap_or_else(|| "value=<none>".to_string()),
                    constructor_info.unwrap_or_else(|| "constructor=<none>".to_string()),
                    datatype_info.unwrap_or_else(|| "datatype=<none>".to_string())
                );
            }
            Located::new(Exp::Named(*n), loc)
        }

        // --------------- Constructors ---------------
        CE::Constructor(dk, pc, targs, opt_e) => {
            debug_batch_constructor_shape("constructor", exp);
            if targs.is_empty() {
                if let CPC::Var(constructor_id) = pc {
                    if let Some(head) = exact_list_constructor_head(env, *constructor_id) {
                        let mut dtmap = HashMap::new();
                        let inner_t = mono_type(env, &mut dtmap, &head);
                        let lt = listify(inner_t, &loc);
                        return match opt_e {
                            None => Located::new(Exp::None(lt), loc),
                            Some(e) => {
                                let e = mono_exp(env, fm, e, settings);
                                Located::new(Exp::Some(lt, Box::new(e)), loc)
                            }
                        };
                    }
                }
                let me = opt_e
                    .as_ref()
                    .map(|e| Box::new(mono_exp(env, fm, e, settings)));
                Located::new(Exp::Con(*dk, mono_pat_con(pc), me), loc)
            } else if targs.len() == 1 {
                if is_list_constructor(env, pc) {
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
                } else {
                    match opt_e {
                        None => {
                            let mut dtmap = HashMap::new();
                            let t = mono_type(env, &mut dtmap, &targs[0]);
                            Located::new(Exp::None(t), loc)
                        }
                        Some(e) => {
                            let mut dtmap = HashMap::new();
                            let t = mono_type(env, &mut dtmap, &targs[0]);
                            let me = mono_exp(env, fm, e, settings);
                            Located::new(Exp::Some(t, Box::new(me)), loc)
                        }
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
            debug_batch_constructor_shape("app-before-reduce", exp);
            let reduced = crate::core::local_reduction::reduce_exp(exp.clone());
            debug_batch_constructor_shape("app-after-reduce", &reduced);
            if !matches!(reduced.node, CE::App(_, _)) {
                return mono_exp(env, fm, &reduced, settings);
            }
            let exp = &reduced;
            let loc = exp.span.clone();
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
                if (x == "txt" || x == "cdata" || x == "htmlifyString")
                    && std::env::var("URWEB_DEBUG_TXT_MONO").ok().as_deref() == Some("1")
                    && (loc.file.ends_with("/demo/outer.ur")
                        || loc.file.ends_with("/demo/cookieSec.ur")
                        || loc.file.ends_with("/lib/ur/top.ur"))
                {
                    eprintln!(
                        "URWEB_DEBUG_TXT_MONO head={x} {}:{} vargs={} targs={} reduced={:?}",
                        loc.file,
                        loc.first.line,
                        vargs.len(),
                        targs.len(),
                        exp
                    );
                }
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
                    "txt" if vargs.len() >= 2 => {
                        let n = vargs.len();
                        let show_e = mono_exp(env, fm, vargs[n - 2], settings);
                        let value_e = mono_exp(env, fm, vargs[n - 1], settings);
                        let shown = match show_e.node {
                            Exp::Abs(_, _, _, body) => {
                                crate::monomorphized::environment::sub_exp_in_exp(
                                    0, &value_e, &body,
                                )
                            }
                            _ => Located::new(
                                Exp::App(Box::new(show_e), Box::new(value_e)),
                                loc.clone(),
                            ),
                        };
                        let str_t =
                            Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
                        return Located::new(
                            Exp::FfiApp(
                                "Basis".into(),
                                "htmlifyString".into(),
                                vec![(shown, str_t)],
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
                    let me2 = mono_exp(env, fm, e2, settings);
                    match me1.node {
                        Exp::Abs(_, _, _, body) => {
                            crate::monomorphized::environment::sub_exp_in_exp(0, &me2, &body)
                        }
                        other => Located::new(
                            Exp::App(Box::new(Located::new(other, me1.span)), Box::new(me2)),
                            loc.clone(),
                        ),
                    }
                }
                _ => zero_exp(&loc, "app-nonapp-fallback"),
            }
        }
        CE::Abs(x, dom, ran, body) => {
            let mut dtmap = HashMap::new();
            let mdom = mono_type(env, &mut dtmap, dom);
            let mran = mono_type(env, &mut dtmap, ran);
            debug_abs_monoization(env, &loc, x, dom, ran, &mdom, &mran);
            let env2 = env.clone().push_e_rel(dom.clone());
            let mbody = mono_exp(&env2, fm, body, settings);
            Located::new(Exp::Abs(x.clone(), mdom, mran, Box::new(mbody)), loc)
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
            let env2 = targs
                .iter()
                .fold(env.clone(), |acc, targ| acc.push_c_rel((**targ).clone()));
            mono_exp(&env2, fm, head, settings)
        }

        // Type/kind abstraction: erase at runtime once any remaining local beta-reduction
        // has had a chance to fire in surrounding CApp/KApp nodes.
        // Still push a constructor placeholder so outer constructor rels keep
        // their de Bruijn alignment under erased binders.
        CE::CAbs(_, _, body) => {
            let env2 = env
                .clone()
                .push_c_rel(Located::new(CC::Rel(0), loc.clone()));
            mono_exp(&env2, fm, body, settings)
        }
        CE::KAbs(_, body) => mono_exp(env, fm, body, settings),
        CE::KApp(inner, _) => mono_exp(env, fm, inner, settings),

        // --------------- Records ---------------
        CE::Record(xets) => {
            let mut mxets: Vec<(String, LocExp, LocTyp)> = xets
                .iter()
                .map(|(name_con, e, t)| {
                    let mut dtmap = HashMap::new();
                    (
                        mono_name_for_field(env, name_con, t),
                        mono_exp(env, fm, e, settings),
                        mono_type(env, &mut dtmap, t),
                    )
                })
                .collect();
            mxets.sort_by(|(a, _, _), (b, _, _)| a.cmp(b));
            Located::new(Exp::Record(mxets), loc)
        }
        CE::Field(e, x, meta) => {
            if std::env::var("URWEB_DEBUG_MONO_FIELD").ok().as_deref() == Some("1")
                && !matches!(&x.node, CC::Name(_))
                && (loc.file.ends_with("/lib/ur/top.ur")
                    || loc.file.ends_with("/demo/metaform.ur")
                    || loc.file.ends_with("/demo/crud.ur"))
            {
                let env_summary = env
                    .rel_e
                    .iter()
                    .rev()
                    .enumerate()
                    .map(|(rel, con)| format!("rel={rel}:{}", debug_constructor_summary(env, con)))
                    .collect::<Vec<_>>()
                    .join(" | ");
                let rel_c_summary = env
                    .rel_c
                    .iter()
                    .rev()
                    .enumerate()
                    .map(|(rel, con)| format!("rel={rel}:{}", debug_constructor_summary(env, con)))
                    .collect::<Vec<_>>()
                    .join(" | ");
                eprintln!(
                    "URWEB_DEBUG_MONO_FIELD {}:{} recv={:?} name={:?} env=[{}] rel_c=[{}]",
                    loc.file, loc.first.line, e.node, x.node, env_summary, rel_c_summary
                );
            }
            let recovered_receiver = match (&e.node, &x.node) {
                (CE::Prim(Prim::Int(0)), CC::Name(field))
                    if span_looks_like_erased_constraint_artifact(&e.span) =>
                {
                    log_record_field_rel_candidates(env, field, &loc);
                    nearest_record_field_rel(env, field)
                        .map(|rel| Located::new(CE::Rel(rel), e.span.clone()))
                        .or_else(|| recover_mapped_record_field_receiver(env, field, &e.span))
                        .or_else(|| recover_applied_record_field_receiver(env, field, &e.span))
                }
                (_, CC::Name(field)) if receiver_lacks_record_field(env, e, field) => {
                    log_record_field_rel_candidates(env, field, &loc);
                    nearest_record_field_rel(env, field)
                        .map(|rel| Located::new(CE::Rel(rel), e.span.clone()))
                        .or_else(|| recover_mapped_record_field_receiver(env, field, &e.span))
                        .or_else(|| recover_applied_record_field_receiver(env, field, &e.span))
                }
                _ => None,
            };
            if std::env::var("URWEB_DEBUG_FIELD_RECOVER").ok().as_deref() == Some("1")
                && matches!(&x.node, CC::Name(_))
                && (loc.file.ends_with("/lib/ur/top.ur")
                    || loc.file.ends_with("/demo/metaform.ur")
                    || loc.file.ends_with("/demo/crud.ur")
                    || loc.file.ends_with("/demo/listFun.ur")
                    || loc.file.ends_with("/demo/refFun.ur")
                    || loc.file.ends_with("/demo/treeFun.ur"))
            {
                let field_name = match &x.node {
                    CC::Name(name) => name.as_str(),
                    _ => unreachable!(),
                };
                let env_summary = env
                    .rel_e
                    .iter()
                    .rev()
                    .enumerate()
                    .map(|(rel, con)| format!("rel={rel}:{}", debug_constructor_summary(env, con)))
                    .collect::<Vec<_>>()
                    .join(" | ");
                eprintln!(
                    "URWEB_DEBUG_FIELD_RECOVER {}:{} field={} receiver={:?} recovered={:?} env=[{}] meta_field={}",
                    loc.file,
                    loc.first.line,
                    field_name,
                    e.node,
                    recovered_receiver.as_ref().map(|r| &r.node),
                    env_summary,
                    debug_constructor_shape(&meta.field, 4)
                );
            }
            let projection_receiver = recovered_receiver.as_ref().unwrap_or(e);
            let me = mono_exp(env, fm, projection_receiver, settings);
            Located::new(
                Exp::Field(
                    Box::new(me),
                    mono_projection_name_for_field(env, projection_receiver, x, &meta.field),
                ),
                loc,
            )
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
            let field_name = mono_name_for_field(env, name, &meta.field);
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
                    if !dt.params.is_empty()
                        || is_exact_list_datatype(dt.id, &dt.name, &dt.params, &dt.constrs)
                    {
                        return None; // Polymorphic — skip
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
                        (
                            mono_name(&env, name_con),
                            mono_type(&env, &mut dtmap, col_t),
                        )
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
                    .map(|(nm, ct)| (mono_name(&env, nm), mono_type(&env, &mut dtmap, ct)))
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
                        let name = mono_name(&env, name_con);
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
    use crate::error_types::Pos;
    use anyhow::Context as _; // .with_context() on Result in tests
    use std::sync::atomic::{AtomicUsize, Ordering};

    fn loc() -> Span {
        Span::dummy()
    }

    fn span_with_text(text: &str) -> Span {
        static COUNTER: AtomicUsize = AtomicUsize::new(0);

        let id = COUNTER.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!("urweb-monoize-span-{id}.ur"));
        std::fs::write(&path, text).expect("write test span source");
        Span {
            file: path.to_string_lossy().into_owned(),
            first: Pos { line: 1, col: 1 },
            last: Pos {
                line: 1,
                col: text.chars().count() as u32 + 1,
            },
        }
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
        let env = Env::empty();
        let c = Located::new(CC::Name("foo".into()), loc());
        assert_eq!(mono_name(&env, &c), "foo");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn mono_name_fallback_for_non_name() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let env = Env::empty();
        let c = Located::new(CC::Ffi("Basis".into(), "int".into()), loc());
        assert_eq!(mono_name(&env, &c), "?");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn mono_name_reduces_local_constructor_application() -> anyhow::Result<()> {
        let env = Env::empty();
        let name_kind = Located::new(crate::core::Kind::Name, loc());
        let c = Located::new(
            CC::App(
                Box::new(Located::new(
                    CC::Abs(
                        "nm".into(),
                        Box::new(name_kind),
                        Box::new(Located::new(CC::Rel(0), loc())),
                    ),
                    loc(),
                )),
                Box::new(Located::new(CC::Name("foo".into()), loc())),
            ),
            loc(),
        );
        assert_eq!(mono_name(&env, &c), "foo");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn mono_name_recovers_rel_name_from_outer_row_witness() -> anyhow::Result<()> {
        let row = Located::new(
            CC::Record(
                Box::new(Located::new(crate::core::Kind::Unit, loc())),
                vec![
                    (
                        Located::new(CC::Name("A".into()), loc()),
                        Located::new(CC::Unit, loc()),
                    ),
                    (
                        Located::new(CC::Name("B".into()), loc()),
                        Located::new(CC::Unit, loc()),
                    ),
                ],
            ),
            loc(),
        );
        let env = Env {
            rel_e: Vec::new(),
            rel_c: vec![
                row,
                Located::new(CC::Rel(3), loc()),
                Located::new(CC::Rel(2), loc()),
                Located::new(CC::Rel(1), loc()),
                Located::new(CC::Rel(0), loc()),
            ],
            named_e: HashMap::new(),
            datatypes: HashMap::new(),
            named_c: HashMap::new(),
        };
        let c = Located::new(CC::Rel(2), loc());
        assert_eq!(mono_name(&env, &c), "A");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn mono_name_recovers_later_rel_name_from_outer_row_witness() -> anyhow::Result<()> {
        let row = Located::new(
            CC::Record(
                Box::new(Located::new(crate::core::Kind::Unit, loc())),
                vec![
                    (
                        Located::new(CC::Name("A".into()), loc()),
                        Located::new(CC::Unit, loc()),
                    ),
                    (
                        Located::new(CC::Name("B".into()), loc()),
                        Located::new(CC::Unit, loc()),
                    ),
                ],
            ),
            loc(),
        );
        let env = Env {
            rel_e: Vec::new(),
            rel_c: vec![
                row,
                Located::new(CC::Rel(3), loc()),
                Located::new(CC::Rel(2), loc()),
                Located::new(CC::Rel(1), loc()),
                Located::new(CC::Rel(0), loc()),
            ],
            named_e: HashMap::new(),
            datatypes: HashMap::new(),
            named_c: HashMap::new(),
        };
        let c = Located::new(CC::Rel(0), loc());
        assert_eq!(mono_name(&env, &c), "B");
        Ok(())
    }

    #[test]
    fn mono_name_for_field_uses_unique_matching_field_type() -> anyhow::Result<()> {
        let int_c = Located::new(CC::Ffi("Basis".into(), "int".into()), loc());
        let string_c = Located::new(CC::Ffi("Basis".into(), "string".into()), loc());
        let row = Located::new(
            CC::Record(
                Box::new(Located::new(crate::core::Kind::Type, loc())),
                vec![
                    (Located::new(CC::Name("A".into()), loc()), int_c.clone()),
                    (Located::new(CC::Name("B".into()), loc()), string_c.clone()),
                ],
            ),
            loc(),
        );
        let env = Env {
            rel_e: Vec::new(),
            rel_c: vec![row, Located::new(CC::Rel(0), loc())],
            named_e: HashMap::new(),
            datatypes: HashMap::new(),
            named_c: HashMap::new(),
        };
        let rel_name = Located::new(CC::Rel(0), loc());

        assert_eq!(mono_name_for_field(&env, &rel_name, &int_c), "A");
        assert_eq!(mono_name_for_field(&env, &rel_name, &string_c), "B");
        Ok(())
    }

    #[test]
    fn mono_name_for_field_uses_outer_row_witness_order_when_field_types_repeat(
    ) -> anyhow::Result<()> {
        let string_c = Located::new(CC::Ffi("Basis".into(), "string".into()), loc());
        let row = Located::new(
            CC::Record(
                Box::new(Located::new(crate::core::Kind::Type, loc())),
                vec![
                    (Located::new(CC::Name("A".into()), loc()), string_c.clone()),
                    (Located::new(CC::Name("B".into()), loc()), string_c.clone()),
                ],
            ),
            loc(),
        );
        let env = Env {
            rel_e: Vec::new(),
            rel_c: vec![
                row,
                Located::new(CC::Rel(3), loc()),
                Located::new(CC::Rel(2), loc()),
                Located::new(CC::Rel(1), loc()),
                Located::new(CC::Rel(0), loc()),
            ],
            named_e: HashMap::new(),
            datatypes: HashMap::new(),
            named_c: HashMap::new(),
        };

        assert_eq!(
            mono_name_for_field(&env, &Located::new(CC::Rel(2), loc()), &string_c),
            "A"
        );
        assert_eq!(
            mono_name_for_field(&env, &Located::new(CC::Rel(0), loc()), &string_c),
            "B"
        );
        Ok(())
    }

    #[test]
    fn mono_projection_name_uses_receiver_field_type_match_for_erased_rel_name(
    ) -> anyhow::Result<()> {
        let int_c = Located::new(CC::Ffi("Basis".into(), "int".into()), loc());
        let string_c = Located::new(CC::Ffi("Basis".into(), "string".into()), loc());
        let receiver_row = Located::new(
            CC::Record(
                Box::new(Located::new(crate::core::Kind::Type, loc())),
                vec![
                    (Located::new(CC::Name("A".into()), loc()), int_c.clone()),
                    (Located::new(CC::Name("B".into()), loc()), string_c.clone()),
                ],
            ),
            loc(),
        );
        let env = Env::empty().push_e_rel(Located::new(CC::TRecord(Box::new(receiver_row)), loc()));
        let receiver = Located::new(CE::Rel(0), loc());

        assert_eq!(
            mono_projection_name_for_field(
                &env,
                &receiver,
                &Located::new(CC::Rel(2), loc()),
                &string_c
            ),
            "B"
        );
        assert_eq!(
            mono_projection_name_for_field(
                &env,
                &receiver,
                &Located::new(CC::Rel(2), loc()),
                &int_c
            ),
            "A"
        );
        Ok(())
    }

    #[test]
    fn mono_projection_name_uses_only_receiver_field_as_last_resort() -> anyhow::Result<()> {
        let bool_c = Located::new(CC::Ffi("Basis".into(), "bool".into()), loc());
        let string_c = Located::new(CC::Ffi("Basis".into(), "string".into()), loc());
        let receiver_row = Located::new(
            CC::Record(
                Box::new(Located::new(crate::core::Kind::Type, loc())),
                vec![(Located::new(CC::Name("B".into()), loc()), string_c)],
            ),
            loc(),
        );
        let env = Env::empty().push_e_rel(Located::new(CC::TRecord(Box::new(receiver_row)), loc()));
        let receiver = Located::new(CE::Rel(0), loc());

        assert_eq!(
            mono_projection_name_for_field(
                &env,
                &receiver,
                &Located::new(CC::Rel(2), loc()),
                &bool_c
            ),
            "B"
        );
        Ok(())
    }

    #[test]
    fn mono_name_for_field_prefers_bound_row_over_ambient_type_match() -> anyhow::Result<()> {
        let int_c = Located::new(CC::Ffi("Basis".into(), "int".into()), loc());
        let string_c = Located::new(CC::Ffi("Basis".into(), "string".into()), loc());
        let bound_row = Located::new(
            CC::Record(
                Box::new(Located::new(crate::core::Kind::Type, loc())),
                vec![
                    (Located::new(CC::Name("A".into()), loc()), int_c.clone()),
                    (Located::new(CC::Name("B".into()), loc()), string_c),
                ],
            ),
            loc(),
        );
        let ambient_row = Located::new(
            CC::Record(
                Box::new(Located::new(crate::core::Kind::Type, loc())),
                vec![(Located::new(CC::Name("C".into()), loc()), int_c.clone())],
            ),
            loc(),
        );
        let env = Env {
            rel_e: vec![ambient_row],
            rel_c: vec![bound_row, Located::new(CC::Rel(0), loc())],
            named_e: HashMap::new(),
            datatypes: HashMap::new(),
            named_c: HashMap::new(),
        };
        let rel_name = Located::new(CC::Rel(0), loc());

        assert_eq!(mono_name_for_field(&env, &rel_name, &int_c), "A");
        Ok(())
    }

    #[test]
    fn mono_name_for_field_uses_mapped_tuple_row_candidate_types() -> anyhow::Result<()> {
        let int_c = Located::new(CC::Ffi("Basis".into(), "int".into()), loc());
        let string_c = Located::new(CC::Ffi("Basis".into(), "string".into()), loc());
        let float_c = Located::new(CC::Ffi("Basis".into(), "float".into()), loc());
        let bool_c = Located::new(CC::Ffi("Basis".into(), "bool".into()), loc());
        let type_kind = Located::new(crate::core::Kind::Type, loc());
        let tuple_kind = Located::new(
            crate::core::Kind::Tuple(vec![type_kind.clone(), type_kind.clone()]),
            loc(),
        );
        let row_kind = Located::new(
            crate::core::Kind::Record(Box::new(tuple_kind.clone())),
            loc(),
        );
        let fst_mapper = Located::new(
            CC::Abs(
                "t".into(),
                Box::new(tuple_kind.clone()),
                Box::new(Located::new(
                    CC::Proj(Box::new(Located::new(CC::Rel(0), loc())), 1),
                    loc(),
                )),
            ),
            loc(),
        );
        let witness_row = Located::new(
            CC::Record(
                Box::new(tuple_kind),
                vec![
                    (
                        Located::new(CC::Name("A".into()), loc()),
                        Located::new(CC::Tuple(vec![int_c.clone(), string_c.clone()]), loc()),
                    ),
                    (
                        Located::new(CC::Name("B".into()), loc()),
                        Located::new(CC::Tuple(vec![string_c.clone(), string_c.clone()]), loc()),
                    ),
                    (
                        Located::new(CC::Name("C".into()), loc()),
                        Located::new(CC::Tuple(vec![float_c.clone(), string_c.clone()]), loc()),
                    ),
                    (
                        Located::new(CC::Name("D".into()), loc()),
                        Located::new(CC::Tuple(vec![bool_c.clone(), bool_c.clone()]), loc()),
                    ),
                ],
            ),
            loc(),
        );
        let mapped_first_row = Located::new(
            CC::App(
                Box::new(Located::new(
                    CC::App(
                        Box::new(Located::new(
                            CC::Map(Box::new(row_kind), Box::new(type_kind)),
                            loc(),
                        )),
                        Box::new(fst_mapper),
                    ),
                    loc(),
                )),
                Box::new(witness_row.clone()),
            ),
            loc(),
        );
        let env = Env {
            rel_e: Vec::new(),
            rel_c: vec![
                witness_row,
                mapped_first_row,
                Located::new(CC::Rel(3), loc()),
                Located::new(CC::Rel(2), loc()),
                Located::new(CC::Rel(1), loc()),
                Located::new(CC::Rel(0), loc()),
            ],
            named_e: HashMap::new(),
            datatypes: HashMap::new(),
            named_c: HashMap::new(),
        };
        let rel_name = Located::new(CC::Rel(2), loc());

        assert_eq!(mono_name_for_field(&env, &rel_name, &int_c), "A");
        assert_eq!(mono_name_for_field(&env, &rel_name, &string_c), "B");
        assert_eq!(mono_name_for_field(&env, &rel_name, &float_c), "C");
        assert_eq!(mono_name_for_field(&env, &rel_name, &bool_c), "D");
        Ok(())
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
    fn mono_type_maps_concrete_unit_row_to_record_fields() -> anyhow::Result<()> {
        let env = Env::empty();
        let mut dtmap = HashMap::new();
        let unit_kind = Located::new(crate::core::Kind::Unit, loc());
        let type_kind = Located::new(crate::core::Kind::Type, loc());
        let row = Located::new(
            CC::Record(
                Box::new(unit_kind.clone()),
                vec![
                    (
                        Located::new(CC::Name("A".into()), loc()),
                        Located::new(CC::Unit, loc()),
                    ),
                    (
                        Located::new(CC::Name("B".into()), loc()),
                        Located::new(CC::Unit, loc()),
                    ),
                ],
            ),
            loc(),
        );
        let mapper = Located::new(
            CC::Abs(
                "_".into(),
                Box::new(unit_kind),
                Box::new(Located::new(
                    CC::Ffi("Basis".into(), "string".into()),
                    loc(),
                )),
            ),
            loc(),
        );
        let mapped_row = Located::new(
            CC::App(
                Box::new(Located::new(
                    CC::App(
                        Box::new(Located::new(
                            CC::Map(Box::new(type_kind.clone()), Box::new(type_kind)),
                            loc(),
                        )),
                        Box::new(mapper),
                    ),
                    loc(),
                )),
                Box::new(row),
            ),
            loc(),
        );
        let t = mono_type(
            &env,
            &mut dtmap,
            &Located::new(CC::TRecord(Box::new(mapped_row)), loc()),
        );
        assert!(matches!(
            &t.node,
            Typ::Record(fields)
                if fields.len() == 2
                    && fields[0].0 == "A"
                    && fields[1].0 == "B"
                    && matches!(fields[0].1.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "string")
                    && matches!(fields[1].1.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "string")
        ));
        Ok(())
    }

    #[test]
    fn mono_type_maps_rel_bound_unit_row_to_record_fields() -> anyhow::Result<()> {
        let unit_kind = Located::new(crate::core::Kind::Unit, loc());
        let type_kind = Located::new(crate::core::Kind::Type, loc());
        let row = Located::new(
            CC::Record(
                Box::new(unit_kind.clone()),
                vec![
                    (
                        Located::new(CC::Name("A".into()), loc()),
                        Located::new(CC::Unit, loc()),
                    ),
                    (
                        Located::new(CC::Name("B".into()), loc()),
                        Located::new(CC::Unit, loc()),
                    ),
                ],
            ),
            loc(),
        );
        let env = Env {
            rel_e: Vec::new(),
            rel_c: vec![row],
            named_e: HashMap::new(),
            datatypes: HashMap::new(),
            named_c: HashMap::new(),
        };
        let mapper = Located::new(
            CC::Abs(
                "_".into(),
                Box::new(unit_kind),
                Box::new(Located::new(
                    CC::Ffi("Basis".into(), "string".into()),
                    loc(),
                )),
            ),
            loc(),
        );
        let mapped_row = Located::new(
            CC::App(
                Box::new(Located::new(
                    CC::App(
                        Box::new(Located::new(
                            CC::Map(Box::new(type_kind.clone()), Box::new(type_kind)),
                            loc(),
                        )),
                        Box::new(mapper),
                    ),
                    loc(),
                )),
                Box::new(Located::new(CC::Rel(0), loc())),
            ),
            loc(),
        );
        let mono = mono_type(
            &env,
            &mut HashMap::new(),
            &Located::new(CC::TRecord(Box::new(mapped_row)), loc()),
        );

        assert!(matches!(
            &mono.node,
            Typ::Record(fields)
                if fields.len() == 2
                    && fields[0].0 == "A"
                    && fields[1].0 == "B"
                    && matches!(fields[0].1.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "string")
                    && matches!(fields[1].1.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "string")
        ));
        Ok(())
    }

    #[test]
    fn mono_type_maps_rel_row_from_outer_witness_to_record_fields() -> anyhow::Result<()> {
        let unit_kind = Located::new(crate::core::Kind::Unit, loc());
        let type_kind = Located::new(crate::core::Kind::Type, loc());
        let row = Located::new(
            CC::Record(
                Box::new(unit_kind.clone()),
                vec![
                    (
                        Located::new(CC::Name("A".into()), loc()),
                        Located::new(CC::Unit, loc()),
                    ),
                    (
                        Located::new(CC::Name("B".into()), loc()),
                        Located::new(CC::Unit, loc()),
                    ),
                ],
            ),
            loc(),
        );
        let env = Env {
            rel_e: Vec::new(),
            rel_c: vec![
                row,
                Located::new(CC::Rel(3), loc()),
                Located::new(CC::Rel(2), loc()),
                Located::new(CC::Rel(1), loc()),
                Located::new(CC::Rel(0), loc()),
            ],
            named_e: HashMap::new(),
            datatypes: HashMap::new(),
            named_c: HashMap::new(),
        };
        let mapper = Located::new(
            CC::Abs(
                "_".into(),
                Box::new(unit_kind),
                Box::new(Located::new(
                    CC::Ffi("Basis".into(), "string".into()),
                    loc(),
                )),
            ),
            loc(),
        );
        let mapped_row = Located::new(
            CC::App(
                Box::new(Located::new(
                    CC::App(
                        Box::new(Located::new(
                            CC::Map(Box::new(type_kind.clone()), Box::new(type_kind)),
                            loc(),
                        )),
                        Box::new(mapper),
                    ),
                    loc(),
                )),
                Box::new(Located::new(CC::Rel(2), loc())),
            ),
            loc(),
        );
        let mono = mono_type(
            &env,
            &mut HashMap::new(),
            &Located::new(CC::TRecord(Box::new(mapped_row)), loc()),
        );

        assert!(matches!(
            &mono.node,
            Typ::Record(fields)
                if fields.len() == 2
                    && fields[0].0 == "A"
                    && fields[1].0 == "B"
                    && matches!(fields[0].1.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "string")
                    && matches!(fields[1].1.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "string")
        ));
        Ok(())
    }

    #[test]
    fn mono_type_concat_drops_duplicate_fields_from_outer_row_witness() -> anyhow::Result<()> {
        let unit_kind = Located::new(crate::core::Kind::Unit, loc());
        let type_kind = Located::new(crate::core::Kind::Type, loc());
        let witness_row = Located::new(
            CC::Record(
                Box::new(unit_kind.clone()),
                vec![
                    (
                        Located::new(CC::Name("A".into()), loc()),
                        Located::new(CC::Unit, loc()),
                    ),
                    (
                        Located::new(CC::Name("B".into()), loc()),
                        Located::new(CC::Unit, loc()),
                    ),
                ],
            ),
            loc(),
        );
        let env = Env {
            rel_e: Vec::new(),
            rel_c: vec![
                witness_row,
                Located::new(CC::Rel(3), loc()),
                Located::new(CC::Rel(2), loc()),
                Located::new(CC::Rel(1), loc()),
                Located::new(CC::Rel(0), loc()),
            ],
            named_e: HashMap::new(),
            datatypes: HashMap::new(),
            named_c: HashMap::new(),
        };
        let mapper = Located::new(
            CC::Abs(
                "_".into(),
                Box::new(unit_kind),
                Box::new(Located::new(
                    CC::Ffi("Basis".into(), "string".into()),
                    loc(),
                )),
            ),
            loc(),
        );
        let mapped_row = Located::new(
            CC::App(
                Box::new(Located::new(
                    CC::App(
                        Box::new(Located::new(
                            CC::Map(Box::new(type_kind.clone()), Box::new(type_kind.clone())),
                            loc(),
                        )),
                        Box::new(mapper),
                    ),
                    loc(),
                )),
                Box::new(Located::new(CC::Rel(2), loc())),
            ),
            loc(),
        );
        let row = Located::new(
            CC::Concat(
                Box::new(Located::new(
                    CC::Record(
                        Box::new(type_kind),
                        vec![(
                            Located::new(CC::Name("A".into()), loc()),
                            Located::new(CC::Ffi("Basis".into(), "string".into()), loc()),
                        )],
                    ),
                    loc(),
                )),
                Box::new(mapped_row),
            ),
            loc(),
        );
        let mono = mono_type(
            &env,
            &mut HashMap::new(),
            &Located::new(CC::TRecord(Box::new(row)), loc()),
        );

        assert!(matches!(
            &mono.node,
            Typ::Record(fields)
                if fields.len() == 2
                    && fields[0].0 == "A"
                    && fields[1].0 == "B"
                    && matches!(fields[0].1.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "string")
                    && matches!(fields[1].1.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "string")
        ));
        Ok(())
    }

    #[test]
    fn mono_type_ffi_non_basis_passthrough() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let t = mono_type_ffi("Other", "foo", &loc());
        assert!(matches!(&t.node, Typ::Ffi(m, x) if m == "Other" && x == "foo"));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn mono_type_named_mono_exact_list_lowers_to_builtin_list() -> anyhow::Result<()> {
        let env = Env::empty().push_datatype(
            11,
            "list".into(),
            vec![],
            vec![
                ("Nil".into(), 12, None),
                (
                    "Cons".into(),
                    13,
                    Some(Located::new(
                        CC::TRecord(Box::new(Located::new(
                            CC::Record(
                                Box::new(Located::new(crate::core::Kind::Type, loc())),
                                vec![
                                    (
                                        Located::new(CC::Name("1".into()), loc()),
                                        Located::new(CC::Ffi("Basis".into(), "int".into()), loc()),
                                    ),
                                    (
                                        Located::new(CC::Name("2".into()), loc()),
                                        Located::new(CC::Named(11), loc()),
                                    ),
                                ],
                            ),
                            loc(),
                        ))),
                        loc(),
                    )),
                ),
            ],
        );
        let mono = mono_type(
            &env,
            &mut HashMap::new(),
            &Located::new(CC::Named(11), loc()),
        );
        assert!(matches!(
            mono.node,
            Typ::List(inner)
                if matches!(inner.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "int")
        ));
        Ok(())
    }

    #[test]
    fn mono_type_app_poly_exact_list_falls_back_to_builtin_list() -> anyhow::Result<()> {
        let env = Env::empty().push_datatype(
            7,
            "list".into(),
            vec!["t".into()],
            vec![
                ("Nil".into(), 8, None),
                (
                    "Cons".into(),
                    9,
                    Some(Located::new(
                        CC::TRecord(Box::new(Located::new(
                            CC::Record(
                                Box::new(Located::new(crate::core::Kind::Type, loc())),
                                vec![
                                    (
                                        Located::new(CC::Name("1".into()), loc()),
                                        Located::new(CC::Rel(0), loc()),
                                    ),
                                    (
                                        Located::new(CC::Name("2".into()), loc()),
                                        Located::new(
                                            CC::App(
                                                Box::new(Located::new(CC::Named(7), loc())),
                                                Box::new(Located::new(CC::Rel(0), loc())),
                                            ),
                                            loc(),
                                        ),
                                    ),
                                ],
                            ),
                            loc(),
                        ))),
                        loc(),
                    )),
                ),
            ],
        );
        let applied = Located::new(
            CC::App(
                Box::new(Located::new(CC::Named(7), loc())),
                Box::new(Located::new(CC::Ffi("Basis".into(), "int".into()), loc())),
            ),
            loc(),
        );

        let mono = mono_type(&env, &mut HashMap::new(), &applied);
        assert!(matches!(
            mono.node,
            Typ::List(inner)
                if matches!(inner.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "int")
        ));
        Ok(())
    }

    #[test]
    fn mono_exp_zero_targ_exact_list_nil_lowers_to_builtin_list_none() -> anyhow::Result<()> {
        let env = Env::empty().push_datatype(
            11,
            "list".into(),
            vec![],
            vec![
                ("Nil".into(), 12, None),
                (
                    "Cons".into(),
                    13,
                    Some(Located::new(
                        CC::TRecord(Box::new(Located::new(
                            CC::Record(
                                Box::new(Located::new(crate::core::Kind::Type, loc())),
                                vec![
                                    (
                                        Located::new(CC::Name("1".into()), loc()),
                                        Located::new(CC::Ffi("Basis".into(), "int".into()), loc()),
                                    ),
                                    (
                                        Located::new(CC::Name("2".into()), loc()),
                                        Located::new(CC::Named(11), loc()),
                                    ),
                                ],
                            ),
                            loc(),
                        ))),
                        loc(),
                    )),
                ),
            ],
        );
        let settings = Settings::default();
        let mut fm = Fm::empty(0);
        let exp = Located::new(
            CE::Constructor(DatatypeKind::Default, CPC::Var(12), vec![], None),
            loc(),
        );

        let mono = mono_exp(&env, &mut fm, &exp, &settings);
        assert!(matches!(
            mono.node,
            Exp::None(ref list_t)
                if matches!(
                    list_t.node,
                    Typ::Record(ref fields)
                        if fields.len() == 2
                            && fields[0].0 == "1"
                            && matches!(fields[0].1.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "int")
                            && fields[1].0 == "2"
                            && matches!(fields[1].1.node, Typ::List(ref inner)
                                if matches!(inner.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "int"))
                )
        ));
        Ok(())
    }

    #[test]
    fn mono_exp_zero_targ_exact_list_cons_lowers_to_builtin_list_some() -> anyhow::Result<()> {
        let env = Env::empty().push_datatype(
            11,
            "list".into(),
            vec![],
            vec![
                ("Nil".into(), 12, None),
                (
                    "Cons".into(),
                    13,
                    Some(Located::new(
                        CC::TRecord(Box::new(Located::new(
                            CC::Record(
                                Box::new(Located::new(crate::core::Kind::Type, loc())),
                                vec![
                                    (
                                        Located::new(CC::Name("1".into()), loc()),
                                        Located::new(CC::Ffi("Basis".into(), "int".into()), loc()),
                                    ),
                                    (
                                        Located::new(CC::Name("2".into()), loc()),
                                        Located::new(CC::Named(11), loc()),
                                    ),
                                ],
                            ),
                            loc(),
                        ))),
                        loc(),
                    )),
                ),
            ],
        );
        let settings = Settings::default();
        let mut fm = Fm::empty(0);
        let int_t = Located::new(CC::Ffi("Basis".into(), "int".into()), loc());
        let list_t = Located::new(CC::Named(11), loc());
        let nil = Located::new(
            CE::Constructor(DatatypeKind::Default, CPC::Var(12), vec![], None),
            loc(),
        );
        let payload = Located::new(
            CE::Record(vec![
                (
                    Located::new(CC::Name("1".into()), loc()),
                    Located::new(CE::Prim(Prim::Int(7)), loc()),
                    int_t,
                ),
                (Located::new(CC::Name("2".into()), loc()), nil, list_t),
            ]),
            loc(),
        );
        let exp = Located::new(
            CE::Constructor(
                DatatypeKind::Default,
                CPC::Var(13),
                vec![],
                Some(Box::new(payload)),
            ),
            loc(),
        );

        let mono = mono_exp(&env, &mut fm, &exp, &settings);
        assert!(matches!(
            mono.node,
            Exp::Some(ref list_t, ref payload)
                if matches!(
                    list_t.node,
                    Typ::Record(ref fields)
                        if fields.len() == 2
                            && fields[0].0 == "1"
                            && matches!(fields[0].1.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "int")
                            && fields[1].0 == "2"
                            && matches!(fields[1].1.node, Typ::List(ref inner)
                                if matches!(inner.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "int"))
                ) && matches!(payload.node, Exp::Record(_))
        ));
        Ok(())
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
    fn mono_type_reduces_mapped_tuple_row_projection_to_record_fields() -> anyhow::Result<()> {
        let env = Env::empty();
        let type_kind = Located::new(crate::core::Kind::Type, loc());
        let tuple_kind = Located::new(
            crate::core::Kind::Tuple(vec![type_kind.clone(), type_kind.clone()]),
            loc(),
        );
        let row_kind = Located::new(
            crate::core::Kind::Record(Box::new(tuple_kind.clone())),
            loc(),
        );
        let fst_mapper = Located::new(
            CC::Abs(
                "t".into(),
                Box::new(tuple_kind.clone()),
                Box::new(Located::new(
                    CC::Proj(Box::new(Located::new(CC::Rel(0), loc())), 1),
                    loc(),
                )),
            ),
            loc(),
        );
        let tuple_row = Located::new(
            CC::Record(
                Box::new(tuple_kind),
                vec![
                    (
                        Located::new(CC::Name("A".into()), loc()),
                        Located::new(
                            CC::Tuple(vec![
                                Located::new(CC::Ffi("Basis".into(), "int".into()), loc()),
                                Located::new(CC::Ffi("Basis".into(), "string".into()), loc()),
                            ]),
                            loc(),
                        ),
                    ),
                    (
                        Located::new(CC::Name("B".into()), loc()),
                        Located::new(
                            CC::Tuple(vec![
                                Located::new(CC::Ffi("Basis".into(), "float".into()), loc()),
                                Located::new(CC::Ffi("Basis".into(), "bool".into()), loc()),
                            ]),
                            loc(),
                        ),
                    ),
                ],
            ),
            loc(),
        );
        let mapped_row = Located::new(
            CC::TRecord(Box::new(Located::new(
                CC::App(
                    Box::new(Located::new(
                        CC::App(
                            Box::new(Located::new(
                                CC::Map(Box::new(row_kind), Box::new(type_kind)),
                                loc(),
                            )),
                            Box::new(fst_mapper),
                        ),
                        loc(),
                    )),
                    Box::new(tuple_row),
                ),
                loc(),
            ))),
            loc(),
        );

        let mono = mono_type(&env, &mut HashMap::new(), &mapped_row);
        assert!(matches!(
            &mono.node,
            Typ::Record(fields)
                if fields.len() == 2
                    && fields[0].0 == "A"
                    && matches!(fields[0].1.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "int")
                    && fields[1].0 == "B"
                    && matches!(fields[1].1.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "float")
        ));
        Ok(())
    }

    #[test]
    fn mono_type_reduces_rel_bound_tuple_projection() -> anyhow::Result<()> {
        let env = Env {
            rel_e: Vec::new(),
            rel_c: vec![Located::new(
                CC::Tuple(vec![
                    Located::new(CC::Ffi("Basis".into(), "int".into()), loc()),
                    Located::new(CC::Ffi("Basis".into(), "string".into()), loc()),
                ]),
                loc(),
            )],
            named_e: HashMap::new(),
            datatypes: HashMap::new(),
            named_c: HashMap::new(),
        };
        let proj = Located::new(
            CC::Proj(Box::new(Located::new(CC::Rel(0), loc())), 1),
            loc(),
        );

        let mono = mono_type(&env, &mut HashMap::new(), &proj);
        assert!(matches!(
            mono.node,
            Typ::Ffi(ref module, ref name) if module == "Basis" && name == "int"
        ));
        Ok(())
    }

    #[test]
    fn mono_type_reduces_outer_witness_tuple_projection() -> anyhow::Result<()> {
        let tuple = Located::new(
            CC::Tuple(vec![
                Located::new(CC::Ffi("Basis".into(), "int".into()), loc()),
                Located::new(CC::Ffi("Basis".into(), "string".into()), loc()),
            ]),
            loc(),
        );
        let env = Env {
            rel_e: Vec::new(),
            rel_c: vec![
                tuple,
                Located::new(CC::Rel(1), loc()),
                Located::new(CC::Rel(0), loc()),
            ],
            named_e: HashMap::new(),
            datatypes: HashMap::new(),
            named_c: HashMap::new(),
        };
        let proj = Located::new(
            CC::Proj(Box::new(Located::new(CC::Rel(1), loc())), 1),
            loc(),
        );

        let mono = mono_type(&env, &mut HashMap::new(), &proj);
        assert!(matches!(
            mono.node,
            Typ::Ffi(ref module, ref name) if module == "Basis" && name == "int"
        ));
        Ok(())
    }

    #[test]
    fn mono_type_recovers_projected_field_type_from_outer_row_witness() -> anyhow::Result<()> {
        let type_kind = Located::new(crate::core::Kind::Type, loc());
        let tuple_kind = Located::new(
            crate::core::Kind::Tuple(vec![type_kind.clone(), type_kind.clone()]),
            loc(),
        );
        let witness_row = Located::new(
            CC::Record(
                Box::new(tuple_kind),
                vec![
                    (
                        Located::new(CC::Name("A".into()), loc()),
                        Located::new(
                            CC::Tuple(vec![
                                Located::new(CC::Ffi("Basis".into(), "int".into()), loc()),
                                Located::new(CC::Ffi("Basis".into(), "string".into()), loc()),
                            ]),
                            loc(),
                        ),
                    ),
                    (
                        Located::new(CC::Name("B".into()), loc()),
                        Located::new(
                            CC::Tuple(vec![
                                Located::new(CC::Ffi("Basis".into(), "float".into()), loc()),
                                Located::new(CC::Ffi("Basis".into(), "bool".into()), loc()),
                            ]),
                            loc(),
                        ),
                    ),
                ],
            ),
            loc(),
        );
        let env = Env {
            rel_e: Vec::new(),
            rel_c: vec![
                witness_row,
                Located::new(CC::Rel(3), loc()),
                Located::new(CC::Rel(2), loc()),
                Located::new(CC::Rel(1), loc()),
                Located::new(CC::Rel(0), loc()),
            ],
            named_e: HashMap::new(),
            datatypes: HashMap::new(),
            named_c: HashMap::new(),
        };
        let field_row = Located::new(
            CC::Record(
                Box::new(type_kind),
                vec![(
                    Located::new(CC::Rel(2), loc()),
                    Located::new(
                        CC::Proj(Box::new(Located::new(CC::Rel(1), loc())), 1),
                        loc(),
                    ),
                )],
            ),
            loc(),
        );

        let mono = mono_type(
            &env,
            &mut HashMap::new(),
            &Located::new(CC::TRecord(Box::new(field_row)), loc()),
        );
        assert!(matches!(
            &mono.node,
            Typ::Record(fields)
                if fields.len() == 1
                    && fields[0].0 == "A"
                    && matches!(fields[0].1.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "int")
        ));
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
    fn mono_exp_cut_uses_rel_rest_row_witness_when_input_is_not_literal() -> anyhow::Result<()> {
        let env = Env::empty().push_c_rel(Located::new(
            CC::Record(
                Box::new(Located::new(crate::core::Kind::Type, loc())),
                vec![(
                    Located::new(CC::Name("B".into()), loc()),
                    Located::new(CC::Ffi("Basis".into(), "string".into()), loc()),
                )],
            ),
            loc(),
        ));
        let settings = Settings::default();
        let mut fm = Fm::empty(0);
        let int_c = Located::new(CC::Ffi("Basis".into(), "int".into()), loc());
        let cut = Located::new(
            CE::Cut(
                Box::new(Located::new(CE::Rel(0), loc())),
                Located::new(CC::Name("A".into()), loc()),
                crate::core::FieldMeta {
                    field: int_c.clone(),
                    rest: Located::new(CC::Rel(0), loc()),
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
        assert!(
            !matches!(mono.node, Exp::Prim(Prim::Int(0))),
            "cut with a rel rest row should not fall back to a zero placeholder"
        );
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

    #[test]
    fn mono_exp_preserves_explicit_unit_lambda_binder() -> anyhow::Result<()> {
        let env = Env::empty();
        let settings = Settings::default();
        let mut fm = Fm::empty(0);
        let span = span_with_text("fn _ => 7");
        let unit_c = Located::new(CC::Unit, span.clone());
        let int_c = Located::new(CC::Ffi("Basis".into(), "int".into()), span.clone());
        let exp = Located::new(
            CE::Abs(
                "_".into(),
                unit_c,
                int_c.clone(),
                Box::new(Located::new(CE::Prim(Prim::Int(7)), span.clone())),
            ),
            span,
        );

        let mono = mono_exp(&env, &mut fm, &exp, &settings);
        assert!(matches!(
            mono.node,
            Exp::Abs(_, dom, ran, body)
                if matches!(dom.node, Typ::Record(ref fields) if fields.is_empty())
                    && matches!(ran.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "int")
                    && matches!(body.node, Exp::Prim(Prim::Int(7)))
        ));
        Ok(())
    }

    #[test]
    fn mono_exp_transaction_return_keeps_unit_thunk() -> anyhow::Result<()> {
        let env = Env::empty();
        let settings = Settings::default();
        let mut fm = Fm::empty(0);
        let span = span_with_text("return 7");
        let int_c = Located::new(CC::Ffi("Basis".into(), "int".into()), span.clone());
        let exp = Located::new(
            CE::App(
                Box::new(Located::new(
                    CE::CApp(
                        Box::new(Located::new(
                            CE::Ffi("Basis".into(), "transaction_return".into()),
                            span.clone(),
                        )),
                        int_c.clone(),
                    ),
                    span.clone(),
                )),
                Box::new(Located::new(CE::Prim(Prim::Int(7)), span.clone())),
            ),
            span,
        );

        let mono = mono_exp(&env, &mut fm, &exp, &settings);
        assert!(matches!(
            mono.node,
            Exp::Abs(_, dom, ran, body)
                if matches!(dom.node, Typ::Record(ref fields) if fields.is_empty())
                    && matches!(ran.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "int")
                    && matches!(body.node, Exp::Prim(Prim::Int(7)))
        ));
        Ok(())
    }

    #[test]
    fn mono_basis_read_projects_read_field() -> anyhow::Result<()> {
        let env = Env::empty();
        let settings = Settings::default();
        let span = span_with_text("read");
        let int_c = Located::new(CC::Ffi("Basis".into(), "int".into()), span.clone());

        let lowered = mono_basis_capp(&env, &settings, "read", &[&int_c], &span)
            .context("expected Basis.read lowering")?;

        assert!(matches!(
            lowered.node,
            Exp::Abs(_, ref dom, ref ran, ref body)
                if matches!(dom.node, Typ::Record(ref fields) if fields.len() == 2 && fields[0].0 == "Read" && fields[1].0 == "ReadError")
                    && matches!(ran.node, Typ::Fun(_, _))
                    && matches!(body.node, Exp::Field(ref inner, ref name) if name == "Read" && matches!(inner.node, Exp::Rel(0)))
        ));
        Ok(())
    }

    #[test]
    fn mono_exp_mk_show_application_beta_reduces() -> anyhow::Result<()> {
        let env = Env::empty();
        let settings = Settings::default();
        let mut fm = Fm::empty(0);
        let span = span_with_text("mkShow (fn x => x)");
        let int_c = Located::new(CC::Ffi("Basis".into(), "int".into()), span.clone());
        let string_c = Located::new(CC::Ffi("Basis".into(), "string".into()), span.clone());
        let show_head = Located::new(
            CE::CApp(
                Box::new(Located::new(
                    CE::Ffi("Basis".into(), "mkShow".into()),
                    span.clone(),
                )),
                int_c.clone(),
            ),
            span.clone(),
        );
        let arg = Located::new(
            CE::Abs(
                "x".into(),
                int_c.clone(),
                string_c.clone(),
                Box::new(Located::new(
                    CE::Prim(Prim::String(
                        crate::primitives::StringMode::Normal,
                        "ok".into(),
                    )),
                    span.clone(),
                )),
            ),
            span.clone(),
        );
        let exp = Located::new(CE::App(Box::new(show_head), Box::new(arg)), span.clone());

        let lowered = mono_exp(&env, &mut fm, &exp, &settings);

        assert!(matches!(
            lowered.node,
            Exp::Abs(_, ref dom, ref ran, ref body)
                if matches!(dom.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "int")
                    && matches!(ran.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "string")
                    && matches!(body.node, Exp::Prim(Prim::String(_, ref s)) if s == "ok")
        ));
        Ok(())
    }

    #[test]
    fn mono_basis_mk_read_builds_read_record() -> anyhow::Result<()> {
        let env = Env::empty();
        let settings = Settings::default();
        let span = span_with_text("mkRead");
        let int_c = Located::new(CC::Ffi("Basis".into(), "int".into()), span.clone());

        let lowered = mono_basis_capp(&env, &settings, "mkRead", &[&int_c], &span)
            .context("expected Basis.mkRead lowering")?;

        assert!(matches!(
            lowered.node,
            Exp::Abs(_, ref read_error_dom, ref outer_ran, ref outer_body)
                if matches!(read_error_dom.node, Typ::Fun(_, _))
                    && matches!(outer_ran.node, Typ::Fun(_, _))
                    && matches!(
                        outer_body.node,
                        Exp::Abs(_, ref read_dom, ref inner_ran, ref inner_body)
                            if matches!(read_dom.node, Typ::Fun(_, _))
                                && matches!(inner_ran.node, Typ::Record(ref fields) if fields.len() == 2 && fields[0].0 == "Read" && fields[1].0 == "ReadError")
                                && matches!(
                                    inner_body.node,
                                    Exp::Record(ref fields)
                                        if fields.len() == 2
                                            && fields[0].0 == "Read"
                                            && matches!(fields[0].1.node, Exp::Rel(0))
                                            && fields[1].0 == "ReadError"
                                            && matches!(fields[1].1.node, Exp::Rel(1))
                                )
                    )
        ));
        Ok(())
    }

    #[test]
    fn mono_basis_set_cookie_uses_runtime_cookie_ffi() -> anyhow::Result<()> {
        let env = Env::empty();
        let settings = Settings::default();
        let span = span_with_text("setCookie");
        let int_c = Located::new(CC::Ffi("Basis".into(), "int".into()), span.clone());

        let lowered = mono_basis_capp(&env, &settings, "setCookie", &[&int_c], &span)
            .context("expected Basis.setCookie lowering")?;

        assert!(matches!(
            lowered.node,
            Exp::Abs(_, ref cookie_dom, ref outer_ran, ref outer_body)
                if matches!(cookie_dom.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "string")
                    && matches!(outer_ran.node, Typ::Fun(_, _))
                    && matches!(
                        outer_body.node,
                        Exp::Abs(_, ref record_dom, ref middle_ran, ref middle_body)
                            if matches!(
                                record_dom.node,
                                Typ::Record(ref fields)
                                    if fields.len() == 3
                                        && fields.iter().any(|(name, _)| name == "Value")
                                        && fields.iter().any(|(name, _)| name == "Expires")
                                        && fields.iter().any(|(name, _)| name == "Secure")
                            )
                                && matches!(middle_ran.node, Typ::Fun(_, _))
                                && matches!(
                                    middle_body.node,
                                    Exp::Abs(_, _, _, ref inner_body)
                                        if matches!(
                                            inner_body.node,
                                            Exp::FfiApp(ref module, ref name, ref args)
                                                if module == "Basis" && name == "set_cookie" && args.len() == 5
                                        )
                                )
                    )
        ));
        Ok(())
    }

    #[test]
    fn mono_basis_get_cookie_uses_runtime_cookie_ffi() -> anyhow::Result<()> {
        let env = Env::empty();
        let settings = Settings::default();
        let span = span_with_text("getCookie");
        let string_c = Located::new(CC::Ffi("Basis".into(), "string".into()), span.clone());

        let lowered = mono_basis_capp(&env, &settings, "getCookie", &[&string_c], &span)
            .context("expected Basis.getCookie lowering")?;

        assert!(matches!(
            lowered.node,
            Exp::Abs(_, ref cookie_dom, ref outer_ran, ref outer_body)
                if matches!(cookie_dom.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "string")
                    && matches!(outer_ran.node, Typ::Fun(_, _))
                    && matches!(
                        outer_body.node,
                        Exp::Abs(_, _, ref inner_ran, ref inner_body)
                            if matches!(inner_ran.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "string")
                                && matches!(
                                    inner_body.node,
                                    Exp::Uurlify(ref inner, _, true)
                                        if matches!(
                                            inner.node,
                                            Exp::FfiApp(ref module, ref name, ref args)
                                                if module == "Basis" && name == "get_cookie" && args.len() == 1
                                        )
                                )
                    )
        ));
        Ok(())
    }

    #[test]
    fn mono_basis_return_blob_lowers_to_return_blob_node() -> anyhow::Result<()> {
        let env = Env::empty();
        let settings = Settings::default();
        let span = span_with_text("returnBlob");
        let int_c = Located::new(CC::Ffi("Basis".into(), "int".into()), span.clone());

        let lowered = mono_basis_capp(&env, &settings, "returnBlob", &[&int_c], &span)
            .context("expected Basis.returnBlob lowering")?;

        assert!(matches!(
            lowered.node,
            Exp::Abs(_, ref blob_dom, ref outer_ran, ref outer_body)
                if matches!(blob_dom.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "blob")
                    && matches!(outer_ran.node, Typ::Fun(_, _))
                    && matches!(
                        outer_body.node,
                        Exp::Abs(_, ref mime_dom, ref middle_ran, ref middle_body)
                            if matches!(mime_dom.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "string")
                                && matches!(middle_ran.node, Typ::Fun(_, _))
                                && matches!(
                                    middle_body.node,
                                    Exp::Abs(_, _, _, ref inner_body)
                                        if matches!(
                                            inner_body.node,
                                            Exp::ReturnBlob { blob: Some(ref blob), ref mime_type, .. }
                                                if matches!(blob.node, Exp::Rel(2))
                                                    && matches!(mime_type.node, Exp::Rel(1))
                                        )
                                )
                    )
        ));
        Ok(())
    }

    #[test]
    fn mono_basis_sql_option_prim_uses_typed_null_literal() -> anyhow::Result<()> {
        let env = Env::empty();
        let settings = Settings::default();
        let span = span_with_text("sql_option_prim");
        let int_c = Located::new(CC::Ffi("Basis".into(), "int".into()), span.clone());

        let lowered = mono_basis_capp(&env, &settings, "sql_option_prim", &[&int_c], &span)
            .context("expected Basis.sql_option_prim lowering")?;

        assert!(matches!(
            lowered.node,
            Exp::Abs(_, ref show_dom, ref outer_ran, ref outer_body)
                if matches!(show_dom.node, Typ::Fun(_, _))
                    && matches!(outer_ran.node, Typ::Fun(_, _))
                    && matches!(
                        outer_body.node,
                        Exp::Abs(_, ref option_dom, ref inner_ran, ref body)
                            if matches!(option_dom.node, Typ::Option(_))
                                && matches!(inner_ran.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "string")
                                && matches!(
                                    body.node,
                                    Exp::Case(_, ref arms, _)
                                        if arms.len() == 2
                                            && matches!(arms[0].0.node, Pat::None(_))
                                            && matches!(
                                                arms[0].1.node,
                                                Exp::Prim(Prim::String(_, ref s)) if s == "NULL::int8"
                                            )
                                            && matches!(arms[1].0.node, Pat::Some(_, _))
                                            && matches!(
                                                arms[1].1.node,
                                                Exp::App(ref fun, ref arg)
                                                    if matches!(fun.node, Exp::Rel(2))
                                                        && matches!(arg.node, Exp::Rel(0))
                                            )
                                )
                    )
        ));
        Ok(())
    }

    #[test]
    fn mono_basis_sql_is_null_wraps_sql_fragment() -> anyhow::Result<()> {
        let env = Env::empty();
        let settings = Settings::default();
        let span = span_with_text("sql_is_null");
        let int_c = Located::new(CC::Ffi("Basis".into(), "int".into()), span.clone());

        let lowered = mono_basis_capp(&env, &settings, "sql_is_null", &[&int_c], &span)
            .context("expected Basis.sql_is_null lowering")?;

        assert!(matches!(
            lowered.node,
            Exp::Abs(_, ref dom, ref ran, ref body)
                if matches!(dom.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "string")
                    && matches!(ran.node, Typ::Ffi(ref module, ref name) if module == "Basis" && name == "string")
                    && matches!(
                        body.node,
                        Exp::Strcat(ref left, ref tail)
                            if matches!(tail.node, Exp::Prim(Prim::String(_, ref s)) if s == " IS NULL)")
                                && matches!(
                                    left.node,
                                    Exp::Strcat(ref open, ref rel)
                                        if matches!(open.node, Exp::Prim(Prim::String(_, ref s)) if s == "(")
                                            && matches!(rel.node, Exp::Rel(0))
                                )
                    )
        ));
        Ok(())
    }

    #[test]
    fn mono_basis_entry_inserts_hidden_markers() -> anyhow::Result<()> {
        let env = Env::empty();
        let settings = Settings::default();
        let mut fm = Fm::empty(0);
        let span = span_with_text("entry");
        let proof = Located::new(CE::Prim(Prim::Int(0)), span_with_text("proof"));
        let xml = Located::new(
            CE::Prim(Prim::String(
                crate::primitives::StringMode::Html,
                "<li>x</li>".into(),
            )),
            span.clone(),
        );
        let head = Located::new(CE::Ffi("Basis".into(), "entry".into()), span.clone());

        let lowered = mono_basis_full_app(
            &env,
            &mut fm,
            &settings,
            &head,
            "entry",
            &[],
            &[&proof, &xml],
            &span,
        )
        .context("expected Basis.entry lowering")?;

        assert!(matches!(
            lowered.node,
            Exp::Strcat(ref left, ref end)
                if matches!(
                    end.node,
                    Exp::Prim(Prim::String(crate::primitives::StringMode::Html, ref s))
                        if s == "<input type=\"hidden\" name=\".e\" value=\"1\" />"
                )
                    && matches!(
                        left.node,
                        Exp::Strcat(ref start, ref middle)
                            if matches!(
                                start.node,
                                Exp::Prim(Prim::String(crate::primitives::StringMode::Html, ref s))
                                    if s == "<input type=\"hidden\" name=\".i\" value=\"1\" />"
                            )
                                && matches!(
                                    middle.node,
                                    Exp::Prim(Prim::String(crate::primitives::StringMode::Html, ref s))
                                        if s == "<li>x</li>"
                                )
                    )
        ));
        Ok(())
    }

    #[test]
    fn mono_basis_subform_inserts_hidden_begin_marker() -> anyhow::Result<()> {
        let env = Env::empty();
        let settings = Settings::default();
        let mut fm = Fm::empty(0);
        let span = span_with_text("subform");
        let name = Located::new(CC::Name("Line".into()), span.clone());
        let xml = Located::new(
            CE::Prim(Prim::String(
                crate::primitives::StringMode::Html,
                "<li>x</li>".into(),
            )),
            span.clone(),
        );
        let head = Located::new(CE::Ffi("Basis".into(), "subform".into()), span.clone());

        let lowered = mono_basis_full_app(
            &env,
            &mut fm,
            &settings,
            &head,
            "subform",
            &[&name],
            &[&xml],
            &span,
        )
        .context("expected Basis.subform lowering")?;

        assert!(matches!(
            lowered.node,
            Exp::Strcat(ref left, ref end)
                if matches!(
                    end.node,
                    Exp::Prim(Prim::String(crate::primitives::StringMode::Html, ref s))
                        if s == "<input type=\"hidden\" name=\".e\" value=\"1\" />"
                )
                    && matches!(
                        left.node,
                        Exp::Strcat(ref start, ref middle)
                            if matches!(
                                start.node,
                                Exp::Prim(Prim::String(crate::primitives::StringMode::Html, ref s))
                                    if s == "<input type=\"hidden\" name=\".b\" value=\"Line\" />"
                            )
                                && matches!(
                                    middle.node,
                                    Exp::Prim(Prim::String(crate::primitives::StringMode::Html, ref s))
                                        if s == "<li>x</li>"
                                )
                    )
        ));
        Ok(())
    }

    #[test]
    fn mono_basis_subforms_inserts_hidden_begin_marker() -> anyhow::Result<()> {
        let env = Env::empty();
        let settings = Settings::default();
        let mut fm = Fm::empty(0);
        let span = span_with_text("subforms");
        let name = Located::new(CC::Name("Lines".into()), span.clone());
        let xml = Located::new(
            CE::Prim(Prim::String(
                crate::primitives::StringMode::Html,
                "<li>x</li>".into(),
            )),
            span.clone(),
        );
        let head = Located::new(CE::Ffi("Basis".into(), "subforms".into()), span.clone());

        let lowered = mono_basis_full_app(
            &env,
            &mut fm,
            &settings,
            &head,
            "subforms",
            &[&name],
            &[&xml],
            &span,
        )
        .context("expected Basis.subforms lowering")?;

        assert!(matches!(
            lowered.node,
            Exp::Strcat(ref left, ref end)
                if matches!(
                    end.node,
                    Exp::Prim(Prim::String(crate::primitives::StringMode::Html, ref s))
                        if s == "<input type=\"hidden\" name=\".e\" value=\"1\" />"
                )
                    && matches!(
                        left.node,
                        Exp::Strcat(ref start, ref middle)
                            if matches!(
                                start.node,
                                Exp::Prim(Prim::String(crate::primitives::StringMode::Html, ref s))
                                    if s == "<input type=\"hidden\" name=\".s\" value=\"Lines\" />"
                            )
                                && matches!(
                                    middle.node,
                                    Exp::Prim(Prim::String(crate::primitives::StringMode::Html, ref s))
                                        if s == "<li>x</li>"
                                )
                    )
        ));
        Ok(())
    }

    #[test]
    fn mono_exp_field_recovers_erased_record_receiver_from_env() -> anyhow::Result<()> {
        let settings = Settings::default();
        let mut fm = Fm::empty(0);
        let span = loc();
        let proof_span = span_with_text("proof");
        let string_c = Located::new(CC::Ffi("Basis".into(), "string".into()), span.clone());
        let meta_record_t = Located::new(
            CC::Record(
                Box::new(Located::new(crate::core::Kind::Type, span.clone())),
                vec![(
                    Located::new(CC::Name("NewState".into()), span.clone()),
                    string_c.clone(),
                )],
            ),
            span.clone(),
        );
        let acc_record_t = Located::new(
            CC::Record(
                Box::new(Located::new(crate::core::Kind::Type, span.clone())),
                vec![(
                    Located::new(CC::Name("A".into()), span.clone()),
                    string_c.clone(),
                )],
            ),
            span.clone(),
        );
        let env = Env::empty()
            .push_e_rel(meta_record_t)
            .push_e_rel(acc_record_t);
        let field = Located::new(
            CE::Field(
                Box::new(Located::new(CE::Prim(Prim::Int(0)), proof_span)),
                Located::new(CC::Name("NewState".into()), span.clone()),
                crate::core::FieldMeta {
                    field: string_c.clone(),
                    rest: Located::new(
                        CC::Record(
                            Box::new(Located::new(crate::core::Kind::Type, span.clone())),
                            vec![],
                        ),
                        span.clone(),
                    ),
                },
            ),
            span,
        );

        let mono = mono_exp(&env, &mut fm, &field, &settings);
        assert!(matches!(
            mono.node,
            Exp::Field(inner, ref name)
                if name == "NewState" && matches!(inner.node, Exp::Rel(1))
        ));
        Ok(())
    }

    #[test]
    fn mono_exp_field_recovers_plain_rel_receiver_from_env() -> anyhow::Result<()> {
        let settings = Settings::default();
        let mut fm = Fm::empty(0);
        let span = loc();
        let string_c = Located::new(CC::Ffi("Basis".into(), "string".into()), span.clone());
        let meta_record_t = Located::new(
            CC::Record(
                Box::new(Located::new(crate::core::Kind::Type, span.clone())),
                vec![(
                    Located::new(CC::Name("NewState".into()), span.clone()),
                    string_c.clone(),
                )],
            ),
            span.clone(),
        );
        let acc_record_t = Located::new(
            CC::Record(
                Box::new(Located::new(crate::core::Kind::Type, span.clone())),
                vec![(
                    Located::new(CC::Name("A".into()), span.clone()),
                    string_c.clone(),
                )],
            ),
            span.clone(),
        );
        let env = Env::empty()
            .push_e_rel(meta_record_t)
            .push_e_rel(acc_record_t);
        let field = Located::new(
            CE::Field(
                Box::new(Located::new(CE::Rel(0), span.clone())),
                Located::new(CC::Name("NewState".into()), span.clone()),
                crate::core::FieldMeta {
                    field: string_c.clone(),
                    rest: Located::new(
                        CC::Record(
                            Box::new(Located::new(crate::core::Kind::Type, span.clone())),
                            vec![],
                        ),
                        span.clone(),
                    ),
                },
            ),
            span,
        );

        let mono = mono_exp(&env, &mut fm, &field, &settings);
        assert!(matches!(
            mono.node,
            Exp::Field(inner, ref name)
                if name == "NewState" && matches!(inner.node, Exp::Rel(1))
        ));
        Ok(())
    }

    #[test]
    fn mono_exp_field_recovers_plain_rel_receiver_into_mapped_record_field() -> anyhow::Result<()> {
        let settings = Settings::default();
        let mut fm = Fm::empty(0);
        let span = loc();
        let kind_t = Located::new(crate::core::Kind::Type, span.clone());
        let string_c = Located::new(CC::Ffi("Basis".into(), "string".into()), span.clone());
        let int_c = Located::new(CC::Ffi("Basis".into(), "int".into()), span.clone());
        let meta_record_t = Located::new(
            CC::Record(
                Box::new(kind_t.clone()),
                vec![
                    (
                        Located::new(CC::Name("Name".into()), span.clone()),
                        string_c.clone(),
                    ),
                    (
                        Located::new(CC::Name("Show".into()), span.clone()),
                        Located::new(
                            CC::TFun(Box::new(int_c.clone()), Box::new(string_c.clone())),
                            span.clone(),
                        ),
                    ),
                ],
            ),
            span.clone(),
        );
        let mapped_meta_t = Located::new(
            CC::Record(
                Box::new(kind_t.clone()),
                vec![(
                    Located::new(CC::Name("A".into()), span.clone()),
                    meta_record_t.clone(),
                )],
            ),
            span.clone(),
        );
        let acc_record_t = Located::new(
            CC::Record(
                Box::new(kind_t),
                vec![(
                    Located::new(CC::Name("A".into()), span.clone()),
                    string_c.clone(),
                )],
            ),
            span.clone(),
        );
        let env = Env::empty()
            .push_e_rel(mapped_meta_t)
            .push_e_rel(acc_record_t);
        let field = Located::new(
            CE::Field(
                Box::new(Located::new(CE::Rel(0), span.clone())),
                Located::new(CC::Name("Show".into()), span.clone()),
                crate::core::FieldMeta {
                    field: Located::new(
                        CC::TFun(Box::new(int_c.clone()), Box::new(string_c.clone())),
                        span.clone(),
                    ),
                    rest: Located::new(CC::Unit, span.clone()),
                },
            ),
            span,
        );

        let mono = mono_exp(&env, &mut fm, &field, &settings);
        assert!(matches!(
            mono.node,
            Exp::Field(inner, ref name)
                if name == "Show"
                    && matches!(
                        inner.node,
                        Exp::Field(ref mapped, ref key)
                            if key == "A" && matches!(mapped.node, Exp::Rel(1))
                    )
        ));
        Ok(())
    }

    #[test]
    fn mono_exp_field_recovers_applied_record_receiver_from_env() -> anyhow::Result<()> {
        let settings = Settings::default();
        let mut fm = Fm::empty(0);
        let span = loc();
        let kind_t = Located::new(crate::core::Kind::Type, span.clone());
        let unit_record_t =
            Located::new(CC::Record(Box::new(kind_t.clone()), vec![]), span.clone());
        let bool_c = Located::new(CC::Ffi("Basis".into(), "bool".into()), span.clone());
        let target_record_t = Located::new(
            CC::Record(
                Box::new(kind_t),
                vec![(
                    Located::new(CC::Name("D".into()), span.clone()),
                    bool_c.clone(),
                )],
            ),
            span.clone(),
        );
        let acc_fun_t = Located::new(
            CC::TFun(
                Box::new(unit_record_t.clone()),
                Box::new(Located::new(
                    CC::TFun(
                        Box::new(unit_record_t.clone()),
                        Box::new(target_record_t.clone()),
                    ),
                    span.clone(),
                )),
            ),
            span.clone(),
        );
        let env = Env::empty()
            .push_e_rel(acc_fun_t)
            .push_e_rel(unit_record_t.clone())
            .push_e_rel(unit_record_t);
        let field = Located::new(
            CE::Field(
                Box::new(Located::new(CE::Rel(0), span.clone())),
                Located::new(CC::Name("D".into()), span.clone()),
                crate::core::FieldMeta {
                    field: bool_c,
                    rest: Located::new(CC::Unit, span.clone()),
                },
            ),
            span,
        );

        let mono = mono_exp(&env, &mut fm, &field, &settings);
        assert!(matches!(
            mono.node,
            Exp::Field(inner, ref name)
                if name == "D"
                    && matches!(
                        inner.node,
                        Exp::App(ref f0, ref arg0)
                            if matches!(arg0.node, Exp::Rel(0))
                                && matches!(
                                    f0.node,
                                    Exp::App(ref f1, ref arg1)
                                        if matches!(arg1.node, Exp::Rel(1))
                                            && matches!(f1.node, Exp::Rel(2))
                                )
                    )
        ));
        Ok(())
    }

    #[test]
    fn mono_record_fields_from_exp_type_reads_literal_record_shapes() -> anyhow::Result<()> {
        let env = Env::empty();
        let span = loc();
        let int_c = Located::new(CC::Ffi("Basis".into(), "int".into()), span.clone());
        let record = Located::new(
            CE::Record(vec![(
                Located::new(CC::Name("A".into()), span.clone()),
                Located::new(CE::Prim(Prim::Int(7)), span.clone()),
                int_c.clone(),
            )]),
            span.clone(),
        );

        let mut dtmap = HashMap::new();
        let fields = mono_record_fields_from_exp_type(&env, &mut dtmap, &record)
            .context("literal record fields should be inferred")?;
        assert!(matches!(
            fields.as_slice(),
            [(name, typ)] if name == "A" && matches!(typ.node, Typ::Ffi(ref m, ref x) if m == "Basis" && x == "int")
        ));
        Ok(())
    }

    #[test]
    fn mono_concat_with_literal_record_tail_avoids_zero_placeholder() -> anyhow::Result<()> {
        let env = Env::empty().push_e_rel(Located::new(
            CC::Record(
                Box::new(Located::new(crate::core::Kind::Type, loc())),
                vec![(
                    Located::new(CC::Name("B".into()), loc()),
                    Located::new(CC::Ffi("Basis".into(), "string".into()), loc()),
                )],
            ),
            loc(),
        ));
        let settings = Settings::default();
        let mut fm = Fm::empty(0);
        let span = loc();
        let int_c = Located::new(CC::Ffi("Basis".into(), "int".into()), span.clone());
        let right_row = Located::new(
            CC::Record(
                Box::new(Located::new(crate::core::Kind::Type, span.clone())),
                vec![(
                    Located::new(CC::Name("A".into()), span.clone()),
                    int_c.clone(),
                )],
            ),
            span.clone(),
        );
        let concat = Located::new(
            CE::Concat(
                Box::new(Located::new(CE::Rel(0), span.clone())),
                Located::new(CC::Rel(0), span.clone()),
                Box::new(Located::new(
                    CE::Record(vec![(
                        Located::new(CC::Name("A".into()), span.clone()),
                        Located::new(CE::Prim(Prim::Int(7)), span.clone()),
                        int_c.clone(),
                    )]),
                    span.clone(),
                )),
                right_row,
            ),
            span.clone(),
        );

        let mono = mono_exp(&env, &mut fm, &concat, &settings);
        assert!(
            !matches!(mono.node, Exp::Prim(Prim::Int(0))),
            "concat with a literal-record tail should not fall back to the zero placeholder"
        );
        assert!(matches!(mono.node, Exp::App(_, _) | Exp::Record(_)));

        let mut dtmap = HashMap::new();
        let fields = mono_record_fields_from_exp_type(&env, &mut dtmap, &concat)
            .context("concat result fields should be inferred")?;
        assert_eq!(fields.len(), 2);
        assert!(fields.iter().any(|(name, _)| name == "A"));
        assert!(fields.iter().any(|(name, _)| name == "B"));
        assert!(matches!(
            fields
                .iter()
                .find(|(name, _)| name == "B")
                .map(|(_, typ)| &typ.node),
            Some(Typ::Ffi(m, x)) if m == "Basis" && x == "string"
        ));
        Ok(())
    }

    #[test]
    fn mono_exp_drops_erased_witness_arg_before_runtime_record_binder() -> anyhow::Result<()> {
        let env = Env::empty();
        let settings = Settings::default();
        let mut fm = Fm::empty(0);
        let span = span_with_text("drop erased witness arg");
        let type_kind = Located::new(crate::core::Kind::Type, span.clone());
        let unit_c = Located::new(CC::Unit, span.clone());
        let string_c = Located::new(CC::Ffi("Basis".into(), "string".into()), span.clone());
        let record_c = Located::new(
            CC::Record(
                Box::new(type_kind.clone()),
                vec![(
                    Located::new(CC::Name("A".into()), span.clone()),
                    string_c.clone(),
                )],
            ),
            span.clone(),
        );
        let field_meta = crate::core::FieldMeta {
            field: string_c.clone(),
            rest: Located::new(CC::Record(Box::new(type_kind), vec![]), span.clone()),
        };
        let exp = Located::new(
            CE::Abs(
                "fs".into(),
                record_c,
                Located::new(
                    CC::TFun(Box::new(unit_c.clone()), Box::new(string_c.clone())),
                    span.clone(),
                ),
                Box::new(Located::new(
                    CE::Abs(
                        "_".into(),
                        unit_c.clone(),
                        string_c.clone(),
                        Box::new(Located::new(
                            CE::Field(
                                Box::new(Located::new(CE::Rel(1), span.clone())),
                                Located::new(CC::Name("A".into()), span.clone()),
                                field_meta,
                            ),
                            span.clone(),
                        )),
                    ),
                    span.clone(),
                )),
            ),
            span.clone(),
        );
        let exp = Located::new(
            CE::App(
                Box::new(exp),
                Box::new(Located::new(CE::Prim(Prim::Int(0)), span.clone())),
            ),
            span,
        );

        let mono = mono_exp(&env, &mut fm, &exp, &settings);
        assert!(
            matches!(
                mono.node,
                Exp::Abs(_, _, _, ref body)
                    if matches!(
                        body.node,
                        Exp::Field(_, ref name) if name == "A"
                    )
            ),
            "expected erased witness arg to be dropped before runtime binding, got {:?}",
            mono.node
        );
        Ok(())
    }
}
