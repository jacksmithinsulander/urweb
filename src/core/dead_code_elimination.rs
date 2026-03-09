//! Dead-code elimination for the Core AST.
//!
//! The shake pass removes unreachable definitions from a Core file.  Starting
//! from a set of *root* declarations — exported pages/actions, SQL tables,
//! views, indexes and (optionally) tasks, policies and cookies — it
//! transitively collects every constructor and expression that those roots
//! depend on, then discards everything else.
//!
//! The algorithm runs in three phases:
//!
//! 1. **Build definition maps** — for each [`Declaration::Constructor`] / [`Declaration::Datatype`]
//!    record its constructor-level deps; for each [`Declaration::Val`] /
//!    [`Declaration::ValRec`] / [`Declaration::Table`] / … record its type and body.
//! 2. **Seed used sets from roots** — traverse root declarations directly,
//!    marking every [`Constructor::Named`] / [`Expression::Named`] / [`Expression::ServerCall`] id
//!    encountered.  Each new mark triggers recursive transitive closure via the
//!    definition maps.
//! 3. **Filter** — keep a declaration iff its id appears in the used sets, or
//!    iff it is unconditionally retained (tables, views, indexes, sequences).
//!
//! Mirrors `shake.sml`.

#![allow(dead_code)]

use std::collections::{BTreeSet, HashMap};

use crate::core::{
    Constructor, Declaration, Expression, LocatedConstructor, LocatedDeclaration,
    LocatedExpression, LocatedPattern, Pattern, PatternConstructor,
};

// ---------------------------------------------------------------------------
// ExpressionDef — what an expression id depends on
// ---------------------------------------------------------------------------

/// All dependencies that an expression id brings in when it is used.
///
/// For a simple value binding `val f : T = body`, the constructor dep is `T`
/// and the expression dep is `body`.  For a table, the constructor deps are
/// the column type, primary-key type and unique-constraint type; the
/// expression deps are the policy and primary-key expressions.  For a mutually
/// recursive group all member ids are listed in `mutual_group_ids` so that
/// marking any one member transitively marks all of them.
#[derive(Clone)]
struct ExpressionDef {
    /// The ids of all other members of a `ValRec` mutual recursion group.
    /// When this expression id is marked used, every id in this vec is also
    /// marked used (triggering their own definitions in turn).
    mutual_group_ids: Vec<usize>,
    /// Constructor-level (type) sub-trees to traverse for [`Constructor::Named`] refs.
    constructor_deps: Vec<LocatedConstructor>,
    /// Expression-level sub-trees to traverse for [`Expression::Named`] /
    /// [`Expression::ServerCall`] refs.
    expression_deps: Vec<LocatedExpression>,
}

// ---------------------------------------------------------------------------
// Shaker — mutable transitive-closure state
// ---------------------------------------------------------------------------

/// Mutable state driving the transitive-closure phase of shake.
struct Shaker {
    /// For each constructor id, the list of constructors that define it
    /// (the body of a `DCon`, or the argument types of a `DDatatype`).
    constructor_defs: HashMap<usize, Vec<LocatedConstructor>>,
    /// For each expression id, its type and body (and mutual group, if any).
    expression_defs: HashMap<usize, ExpressionDef>,
    /// Constructor ids that are reachable from the roots.
    used_constructors: BTreeSet<usize>,
    /// Expression ids that are reachable from the roots.
    used_expressions: BTreeSet<usize>,
}

impl Shaker {
    fn new(
        constructor_defs: HashMap<usize, Vec<LocatedConstructor>>,
        expression_defs: HashMap<usize, ExpressionDef>,
    ) -> Self {
        Shaker {
            constructor_defs,
            expression_defs,
            used_constructors: BTreeSet::new(),
            used_expressions: BTreeSet::new(),
        }
    }

    // -----------------------------------------------------------------------
    // Transitive-closure entrypoints
    // -----------------------------------------------------------------------

    /// Mark a constructor id as used, then recursively mark everything its
    /// definition depends on.
    ///
    /// If `id` is already in `used_constructors` we return immediately to
    /// avoid infinite loops through mutually recursive constructors.  If `id`
    /// has no entry in `constructor_defs` (e.g. an FFI or standard-library
    /// reference that is external to this file) we still add it to the used
    /// set — we just cannot follow its dependencies.
    fn mark_constructor_used(&mut self, id: usize) {
        if !self.used_constructors.insert(id) {
            return; // already visited
        }
        // Clone to release the borrow on self before recursing.
        if let Some(deps) = self.constructor_defs.get(&id).cloned() {
            for dep in deps {
                self.collect_named_from_constructor(&dep);
            }
        }
    }

    /// Mark an expression id as used, then recursively mark everything its
    /// definition depends on.
    ///
    /// If `id` is already in `used_expressions` we return immediately.  When
    /// the definition has a non-empty `mutual_group_ids`, every member of
    /// the mutual-recursion group is also marked (so a `ValRec` group is
    /// always kept or dropped as a unit).
    fn mark_expression_used(&mut self, id: usize) {
        if !self.used_expressions.insert(id) {
            return; // already visited
        }
        if let Some(def) = self.expression_defs.get(&id).cloned() {
            for constructor in def.constructor_deps {
                self.collect_named_from_constructor(&constructor);
            }
            for expression in def.expression_deps {
                self.collect_named_from_expression(&expression);
            }
            for mutual_id in def.mutual_group_ids {
                self.mark_expression_used(mutual_id);
            }
        }
    }

    // -----------------------------------------------------------------------
    // Recursive AST traversal — find Named references
    // -----------------------------------------------------------------------

    /// Recursively traverse a constructor, calling [`mark_constructor_used`]
    /// for every [`Constructor::Named`] encountered.
    fn collect_named_from_constructor(&mut self, constructor: &LocatedConstructor) {
        match &constructor.node {
            Constructor::Named(id) => self.mark_constructor_used(*id),

            Constructor::TFun(left, right)
            | Constructor::App(left, right)
            | Constructor::Concat(left, right) => {
                self.collect_named_from_constructor(left);
                self.collect_named_from_constructor(right);
            }

            Constructor::TRecord(inner) | Constructor::Proj(inner, _) => {
                self.collect_named_from_constructor(inner);
            }

            // TCFun and Abs bind a type variable; only their body has Named refs.
            // (Kinds cannot contain Named constructors.)
            Constructor::TCFun(_, _kind, body) | Constructor::Abs(_, _kind, body) => {
                self.collect_named_from_constructor(body);
            }

            // KAbs and TKFun bind a kind variable; only their body matters.
            Constructor::KAbs(_, body) | Constructor::TKFun(_, body) => {
                self.collect_named_from_constructor(body);
            }

            // KApp: kind argument cannot have Named; only the constructor part.
            Constructor::KApp(inner, _kind) => {
                self.collect_named_from_constructor(inner);
            }

            Constructor::Record(_kind, fields) => {
                for (field_name, field_type) in fields {
                    self.collect_named_from_constructor(field_name);
                    self.collect_named_from_constructor(field_type);
                }
            }

            Constructor::Tuple(members) => {
                for member in members {
                    self.collect_named_from_constructor(member);
                }
            }

            // These carry no Named constructor references.
            Constructor::Rel(_)
            | Constructor::Ffi(_, _)
            | Constructor::Name(_)
            | Constructor::Unit
            | Constructor::Map(_, _) => {}
        }
    }

    /// Recursively traverse an expression, calling [`mark_expression_used`]
    /// for every [`Expression::Named`] or [`Expression::ServerCall`] and calling
    /// [`collect_named_from_constructor`] for every [`Constructor::Named`] embedded
    /// in type annotations.
    ///
    /// This matches the SML `shakeExp` which also runs the `con` callback on
    /// every embedded constructor, ensuring that type-level references are also
    /// transitively included.
    fn collect_named_from_expression(&mut self, expression: &LocatedExpression) {
        match &expression.node {
            Expression::Named(id) => self.mark_expression_used(*id),

            Expression::ServerCall(id, args, result_type, _failure_mode) => {
                self.mark_expression_used(*id);
                for arg in args {
                    self.collect_named_from_expression(arg);
                }
                self.collect_named_from_constructor(result_type);
            }

            // Leaves with no Named refs.
            Expression::Prim(_) | Expression::Rel(_) | Expression::Ffi(_, _) => {}

            Expression::Constructor(_datatype_kind, _pat_con, type_args, payload) => {
                for type_arg in type_args {
                    self.collect_named_from_constructor(type_arg);
                }
                if let Some(payload_exp) = payload {
                    self.collect_named_from_expression(payload_exp);
                }
            }

            Expression::FfiApp(_module, _name, args) => {
                for (arg_exp, arg_type) in args {
                    self.collect_named_from_expression(arg_exp);
                    self.collect_named_from_constructor(arg_type);
                }
            }

            Expression::App(function, argument) => {
                self.collect_named_from_expression(function);
                self.collect_named_from_expression(argument);
            }

            Expression::Abs(_param_name, domain_type, range_type, body) => {
                self.collect_named_from_constructor(domain_type);
                self.collect_named_from_constructor(range_type);
                self.collect_named_from_expression(body);
            }

            Expression::CApp(function, type_arg) => {
                self.collect_named_from_expression(function);
                self.collect_named_from_constructor(type_arg);
            }

            Expression::CAbs(_type_param, _kind, body) => {
                self.collect_named_from_expression(body);
            }

            Expression::KAbs(_kind_param, body) => {
                self.collect_named_from_expression(body);
            }

            Expression::KApp(function, _kind) => {
                self.collect_named_from_expression(function);
            }

            Expression::Record(fields) => {
                for (field_name_con, field_value_exp, field_type_con) in fields {
                    self.collect_named_from_constructor(field_name_con);
                    self.collect_named_from_expression(field_value_exp);
                    self.collect_named_from_constructor(field_type_con);
                }
            }

            Expression::Field(record_exp, field_con, meta) => {
                self.collect_named_from_expression(record_exp);
                self.collect_named_from_constructor(field_con);
                self.collect_named_from_constructor(&meta.field);
                self.collect_named_from_constructor(&meta.rest);
            }

            Expression::Concat(left_exp, left_type, right_exp, right_type) => {
                self.collect_named_from_expression(left_exp);
                self.collect_named_from_constructor(left_type);
                self.collect_named_from_expression(right_exp);
                self.collect_named_from_constructor(right_type);
            }

            Expression::Cut(record_exp, field_con, meta) => {
                self.collect_named_from_expression(record_exp);
                self.collect_named_from_constructor(field_con);
                self.collect_named_from_constructor(&meta.field);
                self.collect_named_from_constructor(&meta.rest);
            }

            Expression::CutMulti(record_exp, fields_con, meta) => {
                self.collect_named_from_expression(record_exp);
                self.collect_named_from_constructor(fields_con);
                self.collect_named_from_constructor(&meta.rest);
            }

            Expression::Case(discriminant, arms, meta) => {
                self.collect_named_from_expression(discriminant);
                for (pattern, arm_expression) in arms {
                    self.collect_named_from_pattern(pattern);
                    self.collect_named_from_expression(arm_expression);
                }
                self.collect_named_from_constructor(&meta.disc);
                self.collect_named_from_constructor(&meta.result);
            }

            Expression::Write(inner) => {
                self.collect_named_from_expression(inner);
            }

            Expression::Closure(_function_id, captured_expressions) => {
                for captured in captured_expressions {
                    self.collect_named_from_expression(captured);
                }
            }

            Expression::Let(_binding_name, binding_type, binding_value, body) => {
                self.collect_named_from_constructor(binding_type);
                self.collect_named_from_expression(binding_value);
                self.collect_named_from_expression(body);
            }
        }
    }

    /// Recursively traverse a pattern, collecting [`Constructor::Named`] refs from
    /// any type annotations within it.
    fn collect_named_from_pattern(&mut self, pattern: &LocatedPattern) {
        match &pattern.node {
            Pattern::Var(_name, var_type) => {
                self.collect_named_from_constructor(var_type);
            }
            Pattern::Prim(_) => {}
            Pattern::Constructor(_datatype_kind, pat_con, type_args, sub_pattern) => {
                // The FFI constructor pattern may carry a constructor argument type.
                if let PatternConstructor::Ffi { arg, .. } = pat_con {
                    if let Some(arg_con) = arg {
                        self.collect_named_from_constructor(arg_con);
                    }
                }
                for type_arg in type_args {
                    self.collect_named_from_constructor(type_arg);
                }
                if let Some(nested) = sub_pattern {
                    self.collect_named_from_pattern(nested);
                }
            }
            Pattern::Record(fields) => {
                for (_field_name, field_pattern, field_type) in fields {
                    self.collect_named_from_pattern(field_pattern);
                    self.collect_named_from_constructor(field_type);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Phase 2 helpers — build definition maps
// ---------------------------------------------------------------------------

/// Build the constructor-def and expression-def maps from the full file.
///
/// This populates:
/// - `constructor_defs[n]` = the list of constructors that define `n`
///   (the body for a [`Declaration::Constructor`], the payload types for a [`Declaration::Datatype`]).
/// - `expression_defs[n]` = the type and body expressions for `n`
///   (from [`Declaration::Val`], [`Declaration::ValRec`], [`Declaration::Table`], etc.).
fn build_definition_maps(
    file: &[LocatedDeclaration],
) -> (
    HashMap<usize, Vec<LocatedConstructor>>,
    HashMap<usize, ExpressionDef>,
) {
    let mut constructor_defs: HashMap<usize, Vec<LocatedConstructor>> = HashMap::new();
    let mut expression_defs: HashMap<usize, ExpressionDef> = HashMap::new();

    for located_decl in file {
        match &located_decl.node {
            Declaration::Constructor(_name, id, _kind, body_con) => {
                // A type alias: CNamed id unfolds to body_con.
                constructor_defs.insert(*id, vec![body_con.clone()]);
            }

            Declaration::Datatype(datatype_decls) => {
                for datatype in datatype_decls {
                    // For a datatype, the deps are the argument types of its
                    // constructors (nullary constructors have no deps).
                    let payload_types: Vec<LocatedConstructor> = datatype
                        .constrs
                        .iter()
                        .filter_map(|(_constr_name, _constr_id, arg_type)| arg_type.clone())
                        .collect();
                    constructor_defs.insert(datatype.id, payload_types);
                }
            }

            Declaration::Val(_name, id, val_type, val_body, _comment) => {
                expression_defs.insert(
                    *id,
                    ExpressionDef {
                        mutual_group_ids: vec![],
                        constructor_deps: vec![val_type.clone()],
                        expression_deps: vec![val_body.clone()],
                    },
                );
            }

            Declaration::ValRec(bindings) => {
                // All members of the mutual-recursion group must be kept together.
                let all_ids_in_group: Vec<usize> = bindings
                    .iter()
                    .map(|(_name, id, _ty, _body, _comment)| *id)
                    .collect();
                for (_name, id, val_type, val_body, _comment) in bindings {
                    expression_defs.insert(
                        *id,
                        ExpressionDef {
                            mutual_group_ids: all_ids_in_group.clone(),
                            constructor_deps: vec![val_type.clone()],
                            expression_deps: vec![val_body.clone()],
                        },
                    );
                }
            }

            Declaration::Table {
                id,
                con,
                exp,
                pk_con,
                pk_exp,
                unique_con,
                ..
            } => {
                // The table's deps: column type, pk type, unique type (cons)
                // and policy expression, pk expression (exps).
                expression_defs.insert(
                    *id,
                    ExpressionDef {
                        mutual_group_ids: vec![],
                        constructor_deps: vec![con.clone(), pk_con.clone(), unique_con.clone()],
                        expression_deps: vec![exp.clone(), pk_exp.clone()],
                    },
                );
            }

            Declaration::Sequence(_name, id, _sql_name) => {
                // Sequences have no type or body deps.
                expression_defs.insert(
                    *id,
                    ExpressionDef {
                        mutual_group_ids: vec![],
                        constructor_deps: vec![],
                        expression_deps: vec![],
                    },
                );
            }

            Declaration::View(_name, id, _sql_name, view_exp, view_con) => {
                expression_defs.insert(
                    *id,
                    ExpressionDef {
                        mutual_group_ids: vec![],
                        constructor_deps: vec![view_con.clone()],
                        expression_deps: vec![view_exp.clone()],
                    },
                );
            }

            Declaration::Cookie(_name, id, cookie_type, _sql_name) => {
                expression_defs.insert(
                    *id,
                    ExpressionDef {
                        mutual_group_ids: vec![],
                        constructor_deps: vec![cookie_type.clone()],
                        expression_deps: vec![],
                    },
                );
            }

            Declaration::Style(_name, id, _sql_name) => {
                expression_defs.insert(
                    *id,
                    ExpressionDef {
                        mutual_group_ids: vec![],
                        constructor_deps: vec![],
                        expression_deps: vec![],
                    },
                );
            }

            // These declarations do not participate in name-based reachability.
            Declaration::Export(_, _, _)
            | Declaration::Index(_, _)
            | Declaration::Database(_)
            | Declaration::Task(_, _)
            | Declaration::Policy(_)
            | Declaration::OnError(_) => {}
        }
    }

    (constructor_defs, expression_defs)
}

// ---------------------------------------------------------------------------
// Phase 1 — seed used sets from root declarations
// ---------------------------------------------------------------------------

/// Traverse each root declaration and seed the shaker with the Named ids
/// it directly references.
///
/// A declaration is a *root* if it is a table, view, index, or (when
/// `slice_for_db` is false) an export, task, policy, cookie or error handler.
fn seed_roots_from_file(shaker: &mut Shaker, file: &[LocatedDeclaration], slice_for_db: bool) {
    for located_decl in file {
        match &located_decl.node {
            Declaration::Export(_kind, exported_id, _has_state) => {
                // Exports are roots in normal mode; suppressed when slicing for DB.
                if !slice_for_db {
                    shaker.mark_expression_used(*exported_id);
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
                // Tables are always roots regardless of slice_for_db.
                shaker.collect_named_from_constructor(con);
                shaker.collect_named_from_constructor(pk_con);
                shaker.collect_named_from_constructor(unique_con);
                shaker.collect_named_from_expression(exp);
                shaker.collect_named_from_expression(pk_exp);
            }

            Declaration::View(_name, _id, _sql, view_exp, view_con) => {
                // Views are always roots.
                shaker.collect_named_from_constructor(view_con);
                shaker.collect_named_from_expression(view_exp);
            }

            Declaration::Index(index_exp1, index_exp2) => {
                // Indexes are always roots.
                shaker.collect_named_from_expression(index_exp1);
                shaker.collect_named_from_expression(index_exp2);
            }

            Declaration::Task(task_exp1, task_exp2) => {
                // Tasks are roots in normal mode; suppressed when slicing for DB.
                if !slice_for_db {
                    shaker.collect_named_from_expression(task_exp1);
                    shaker.collect_named_from_expression(task_exp2);
                }
            }

            Declaration::Policy(policy_exp) => {
                if !slice_for_db {
                    shaker.collect_named_from_expression(policy_exp);
                }
            }

            Declaration::OnError(error_handler_id) => {
                if !slice_for_db {
                    shaker.mark_expression_used(*error_handler_id);
                }
            }

            // Con, Datatype, Val, ValRec, Sequence, Database, Cookie, Style:
            // not roots; they are only included when reachable from a root.
            _ => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Phase 4 — filter declarations
// ---------------------------------------------------------------------------

/// Decide whether a declaration should be retained in the shaken output.
fn should_keep_declaration(
    decl: &Declaration,
    used_constructors: &BTreeSet<usize>,
    used_expressions: &BTreeSet<usize>,
    slice_for_db: bool,
) -> bool {
    match decl {
        Declaration::Constructor(_name, id, _kind, _body) => used_constructors.contains(id),

        Declaration::Datatype(datatype_decls) => {
            // Keep the entire `DDatatype` node if any member id is used.
            datatype_decls
                .iter()
                .any(|dt| used_constructors.contains(&dt.id))
        }

        Declaration::Val(_name, id, _ty, _body, _comment) => used_expressions.contains(id),

        Declaration::ValRec(bindings) => {
            // Keep the entire `DValRec` node if any member id is used.
            bindings
                .iter()
                .any(|(_name, id, _ty, _body, _comment)| used_expressions.contains(id))
        }

        // Always retained regardless of used sets.
        Declaration::View(_, _, _, _, _)
        | Declaration::Index(_, _)
        | Declaration::Sequence(_, _, _)
        | Declaration::Table { .. } => true,

        // Retained in normal mode; removed when slicing for DB.
        Declaration::Export(_, _, _)
        | Declaration::Database(_)
        | Declaration::Cookie(_, _, _, _)
        | Declaration::Style(_, _, _)
        | Declaration::Task(_, _)
        | Declaration::Policy(_)
        | Declaration::OnError(_) => !slice_for_db,
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Remove unreachable definitions from `file`, keeping everything reachable
/// from exported page/action handlers, tables, views, indexes, tasks,
/// policies and error handlers.
///
/// This is the standard shake pass used during compilation.  Use
/// [`shake_slicing_for_db`] when you want to extract only database-related
/// code for the `sliceDb` analysis mode.
///
/// Mirrors `Shake.shake` with `sliceDb = false`.
pub fn shake(file: crate::core::File) -> crate::core::File {
    shake_with_options(file, false)
}

/// Like [`shake`] but operates in "slice for DB" mode: exports, tasks,
/// policies, cookies, styles, and error handlers are *not* roots and are
/// removed from the output.  Only tables, views, indexes and the
/// constructors/expressions they depend on survive.
///
/// Mirrors `Shake.shake` with `sliceDb = true`.
pub fn shake_slicing_for_db(file: crate::core::File) -> crate::core::File {
    shake_with_options(file, true)
}

fn shake_with_options(file: crate::core::File, slice_for_db: bool) -> crate::core::File {
    // Phase 2: build definition maps.
    let (constructor_defs, expression_defs) = build_definition_maps(&file);

    // Phase 1 + 3: seed from roots and close transitively.
    let mut shaker = Shaker::new(constructor_defs, expression_defs);
    seed_roots_from_file(&mut shaker, &file, slice_for_db);

    let used_constructors = shaker.used_constructors;
    let used_expressions = shaker.used_expressions;

    // Phase 4: filter.
    file.into_iter()
        .filter(|located_decl| {
            should_keep_declaration(
                &located_decl.node,
                &used_constructors,
                &used_expressions,
                slice_for_db,
            )
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{CaseMeta, DatatypeDecl, Declaration, LocatedDeclaration, Pattern};
    use crate::error_types::{Located, Span};
    use crate::export::ExportKind;
    use crate::primitives::Prim;

    // -----------------------------------------------------------------------
    // Test helpers
    // -----------------------------------------------------------------------

    fn dummy_span() -> Span {
        Span::dummy()
    }

    fn dummy_kind() -> crate::core::LocatedKind {
        Located::new(crate::core::Kind::Type, dummy_span())
    }

    fn named_con(id: usize) -> LocatedConstructor {
        Located::new(Constructor::Named(id), dummy_span())
    }

    fn unit_con() -> LocatedConstructor {
        Located::new(Constructor::Unit, dummy_span())
    }

    fn named_exp(id: usize) -> LocatedExpression {
        Located::new(Expression::Named(id), dummy_span())
    }

    fn prim_exp() -> LocatedExpression {
        Located::new(
            Expression::Prim(Prim::String(
                crate::primitives::StringMode::Normal,
                String::new(),
            )),
            dummy_span(),
        )
    }

    fn con_decl(id: usize, body: LocatedConstructor) -> LocatedDeclaration {
        Located::new(
            Declaration::Constructor(format!("T{id}"), id, dummy_kind(), body),
            dummy_span(),
        )
    }

    fn val_decl(id: usize, body: LocatedExpression) -> LocatedDeclaration {
        Located::new(
            Declaration::Val(format!("f{id}"), id, unit_con(), body, String::new()),
            dummy_span(),
        )
    }

    fn export_decl(exported_id: usize) -> LocatedDeclaration {
        Located::new(
            Declaration::Export(
                ExportKind::Link(crate::export::Effect::ReadOnly),
                exported_id,
                false,
            ),
            dummy_span(),
        )
    }

    fn table_decl(id: usize) -> LocatedDeclaration {
        Located::new(
            Declaration::Table {
                sql_name: format!("t{id}"),
                id,
                con: unit_con(),
                sql_con: String::new(),
                exp: prim_exp(),
                pk_con: unit_con(),
                pk_exp: prim_exp(),
                unique_con: unit_con(),
            },
            dummy_span(),
        )
    }

    fn sequence_decl(id: usize) -> LocatedDeclaration {
        Located::new(
            Declaration::Sequence(format!("seq{id}"), id, format!("seq{id}")),
            dummy_span(),
        )
    }

    // -----------------------------------------------------------------------
    // Basic reachability
    // -----------------------------------------------------------------------

    #[test]
    fn exported_value_is_kept() {
        // Catches mutant: shake drops the exported binding.
        let file = vec![val_decl(1, prim_exp()), export_decl(1)];
        let result = shake(file);
        let ids: Vec<usize> = result
            .iter()
            .filter_map(|d| match &d.node {
                Declaration::Val(_, id, _, _, _) => Some(*id),
                _ => None,
            })
            .collect();
        assert!(ids.contains(&1), "exported val must be kept");
    }

    #[test]
    fn unreachable_value_is_removed() {
        // Catches mutant: shake keeps all vals unconditionally.
        let file = vec![
            val_decl(1, prim_exp()),
            val_decl(2, prim_exp()), // not exported, not reachable
            export_decl(1),
        ];
        let result = shake(file);
        let ids: Vec<usize> = result
            .iter()
            .filter_map(|d| match &d.node {
                Declaration::Val(_, id, _, _, _) => Some(*id),
                _ => None,
            })
            .collect();
        assert!(!ids.contains(&2), "unreachable val must be removed");
    }

    #[test]
    fn transitive_expression_dependency_is_kept() {
        // Catches mutant: transitive closure only goes one level deep.
        let file = vec![
            val_decl(1, prim_exp()),   // id=1: base val, not directly exported
            val_decl(2, named_exp(1)), // id=2: depends on id=1
            export_decl(2),
        ];
        let result = shake(file);
        let ids: Vec<usize> = result
            .iter()
            .filter_map(|d| match &d.node {
                Declaration::Val(_, id, _, _, _) => Some(*id),
                _ => None,
            })
            .collect();
        assert!(ids.contains(&1), "transitively needed val must be kept");
        assert!(ids.contains(&2), "directly exported val must be kept");
    }

    #[test]
    fn transitive_constructor_dependency_is_kept() {
        // Catches mutant: constructor deps are not traversed transitively.
        let file = vec![
            con_decl(10, unit_con()),    // id=10: base type
            con_decl(11, named_con(10)), // id=11: depends on id=10
            // val whose type annotation is Named(11)
            Located::new(
                Declaration::Val(
                    "f".into(),
                    5,
                    named_con(11), // type references id=11, which references id=10
                    prim_exp(),
                    String::new(),
                ),
                dummy_span(),
            ),
            export_decl(5),
        ];
        let result = shake(file);
        let con_ids: Vec<usize> = result
            .iter()
            .filter_map(|d| match &d.node {
                Declaration::Constructor(_, id, _, _) => Some(*id),
                _ => None,
            })
            .collect();
        assert!(con_ids.contains(&11), "direct type dep must be kept");
        assert!(con_ids.contains(&10), "transitive type dep must be kept");
    }

    // -----------------------------------------------------------------------
    // Always-kept declarations
    // -----------------------------------------------------------------------

    #[test]
    fn tables_are_always_kept() {
        // Catches mutant: tables are filtered the same as vals.
        let file = vec![table_decl(99)];
        let result = shake(file);
        assert!(
            result
                .iter()
                .any(|d| matches!(&d.node, Declaration::Table { id, .. } if *id == 99)),
            "table must always be kept"
        );
    }

    #[test]
    fn sequences_are_always_kept() {
        // Catches mutant: sequences are filtered when not in used_expressions.
        let file = vec![sequence_decl(42)];
        let result = shake(file);
        assert!(
            result
                .iter()
                .any(|d| matches!(&d.node, Declaration::Sequence(_, id, _) if *id == 42)),
            "sequence must always be kept"
        );
    }

    #[test]
    fn views_are_always_kept() {
        // Catches mutant: views are filtered when not in used_expressions.
        let file = vec![Located::new(
            Declaration::View("v".into(), 7, "v_sql".into(), prim_exp(), unit_con()),
            dummy_span(),
        )];
        let result = shake(file);
        assert!(
            result
                .iter()
                .any(|d| matches!(&d.node, Declaration::View(_, id, _, _, _) if *id == 7)),
            "view must always be kept"
        );
    }

    #[test]
    fn indexes_are_always_kept() {
        // Catches mutant: indexes are filtered.
        let file = vec![Located::new(
            Declaration::Index(prim_exp(), prim_exp()),
            dummy_span(),
        )];
        let result = shake(file);
        assert!(
            result
                .iter()
                .any(|d| matches!(&d.node, Declaration::Index(_, _))),
            "index must always be kept"
        );
    }

    /// Catches mutant: delete match arm Declaration::View in seed_roots_from_file.
    /// If we don't seed from the view, the constructor/expression ids it references
    /// won't be in used sets and the corresponding Val/Con would be dropped.
    #[test]
    fn view_seeds_expression_and_constructor_deps() {
        let file = vec![
            con_decl(10, unit_con()),
            val_decl(1, prim_exp()),
            Located::new(
                Declaration::View("v".into(), 7, "v_sql".into(), named_exp(1), named_con(10)),
                dummy_span(),
            ),
        ];
        let result = shake(file);
        let con_ids: Vec<usize> = result
            .iter()
            .filter_map(|d| match &d.node {
                Declaration::Constructor(_, id, _, _) => Some(*id),
                _ => None,
            })
            .collect();
        let exp_ids: Vec<usize> = result
            .iter()
            .filter_map(|d| match &d.node {
                Declaration::Val(_, id, _, _, _) => Some(*id),
                _ => None,
            })
            .collect();
        assert!(
            con_ids.contains(&10),
            "constructor referenced by view must be kept"
        );
        assert!(
            exp_ids.contains(&1),
            "expression referenced by view must be kept"
        );
    }

    /// Catches mutant: delete match arm Declaration::Index in seed_roots_from_file.
    #[test]
    fn index_seeds_expression_deps() {
        let file = vec![
            val_decl(1, prim_exp()),
            Located::new(Declaration::Index(named_exp(1), prim_exp()), dummy_span()),
        ];
        let result = shake(file);
        let exp_ids: Vec<usize> = result
            .iter()
            .filter_map(|d| match &d.node {
                Declaration::Val(_, id, _, _, _) => Some(*id),
                _ => None,
            })
            .collect();
        assert!(
            exp_ids.contains(&1),
            "expression referenced by index must be kept"
        );
    }

    /// Catches mutant: delete match arm Declaration::Task or delete !slice_for_db in Task arm.
    #[test]
    fn task_seeds_expression_deps_in_normal_mode() {
        let file = vec![
            val_decl(1, prim_exp()),
            Located::new(Declaration::Task(named_exp(1), prim_exp()), dummy_span()),
        ];
        let result = shake(file);
        let exp_ids: Vec<usize> = result
            .iter()
            .filter_map(|d| match &d.node {
                Declaration::Val(_, id, _, _, _) => Some(*id),
                _ => None,
            })
            .collect();
        assert!(
            exp_ids.contains(&1),
            "expression referenced by task must be kept in normal mode"
        );
    }

    /// Catches mutant: delete match arm Declaration::Policy or delete !slice_for_db in Policy arm.
    #[test]
    fn policy_seeds_expression_deps_in_normal_mode() {
        let file = vec![
            val_decl(1, prim_exp()),
            Located::new(Declaration::Policy(named_exp(1)), dummy_span()),
        ];
        let result = shake(file);
        let exp_ids: Vec<usize> = result
            .iter()
            .filter_map(|d| match &d.node {
                Declaration::Val(_, id, _, _, _) => Some(*id),
                _ => None,
            })
            .collect();
        assert!(
            exp_ids.contains(&1),
            "expression referenced by policy must be kept in normal mode"
        );
    }

    /// Catches mutant: replace Shaker::collect_named_from_pattern with () (skip pattern traversal).
    /// A Case expression's arm pattern can have a type annotation that references a constructor;
    /// that constructor id must be collected so the Con is kept.
    #[test]
    fn case_pattern_type_annotation_constructor_kept() {
        let pat_with_ty = Located::new(Pattern::Var("x".into(), named_con(50)), dummy_span());
        let case_meta = CaseMeta {
            disc: unit_con(),
            result: unit_con(),
        };
        let case_exp = Located::new(
            Expression::Case(
                Box::new(prim_exp()),
                vec![(pat_with_ty, prim_exp())],
                case_meta,
            ),
            dummy_span(),
        );
        let file = vec![
            con_decl(50, unit_con()),
            val_decl(5, case_exp),
            export_decl(5),
        ];
        let result = shake(file);
        let con_ids: Vec<usize> = result
            .iter()
            .filter_map(|d| match &d.node {
                Declaration::Constructor(_, id, _, _) => Some(*id),
                _ => None,
            })
            .collect();
        assert!(
            con_ids.contains(&50),
            "constructor referenced in case pattern type must be kept"
        );
    }

    // -----------------------------------------------------------------------
    // Mutual recursion
    // -----------------------------------------------------------------------

    #[test]
    fn val_rec_group_kept_as_unit_when_one_used() {
        // Catches mutant: ValRec members are filtered individually.
        let file = vec![
            Located::new(
                Declaration::ValRec(vec![
                    ("a".into(), 10, unit_con(), named_exp(11), String::new()),
                    ("b".into(), 11, unit_con(), named_exp(10), String::new()),
                ]),
                dummy_span(),
            ),
            export_decl(10), // only id=10 is directly exported
        ];
        let result = shake(file);
        // The entire ValRec node must appear (with both members).
        let val_rec: Vec<_> = result
            .iter()
            .filter_map(|d| match &d.node {
                Declaration::ValRec(vis) => Some(vis.clone()),
                _ => None,
            })
            .flatten()
            .collect();
        let group_ids: Vec<usize> = val_rec.iter().map(|(_, id, _, _, _)| *id).collect();
        assert!(group_ids.contains(&10), "referenced member must be present");
        assert!(group_ids.contains(&11), "mutual partner must be present");
    }

    #[test]
    fn val_rec_group_entirely_removed_when_not_used() {
        // Catches mutant: ValRec is kept even when none of its ids are used.
        let file = vec![
            Located::new(
                Declaration::ValRec(vec![
                    ("a".into(), 20, unit_con(), prim_exp(), String::new()),
                    ("b".into(), 21, unit_con(), prim_exp(), String::new()),
                ]),
                dummy_span(),
            ),
            // No export referencing 20 or 21.
        ];
        let result = shake(file);
        assert!(
            result
                .iter()
                .all(|d| !matches!(&d.node, Declaration::ValRec(_))),
            "unreachable ValRec must be entirely removed"
        );
    }

    // -----------------------------------------------------------------------
    // Datatype reachability
    // -----------------------------------------------------------------------

    #[test]
    fn datatype_kept_when_used_by_exported_val_type() {
        // Catches mutant: datatypes are not tracked via constructor deps.
        let file = vec![
            Located::new(
                Declaration::Datatype(vec![DatatypeDecl {
                    name: "Opt".into(),
                    id: 50,
                    params: vec![],
                    constrs: vec![
                        ("None".into(), 100, None),
                        ("Some".into(), 101, Some(unit_con())),
                    ],
                }]),
                dummy_span(),
            ),
            Located::new(
                Declaration::Val("main".into(), 1, named_con(50), prim_exp(), String::new()),
                dummy_span(),
            ),
            export_decl(1),
        ];
        let result = shake(file);
        assert!(
            result.iter().any(|d| matches!(&d.node, Declaration::Datatype(dts) if dts.iter().any(|dt| dt.id == 50))),
            "datatype used by exported val type must be kept"
        );
    }

    #[test]
    fn unreachable_datatype_removed() {
        // Catches mutant: all datatypes are kept unconditionally.
        let file = vec![
            Located::new(
                Declaration::Datatype(vec![DatatypeDecl {
                    name: "Unused".into(),
                    id: 60,
                    params: vec![],
                    constrs: vec![],
                }]),
                dummy_span(),
            ),
            val_decl(1, prim_exp()),
            export_decl(1),
        ];
        let result = shake(file);
        assert!(
            result
                .iter()
                .all(|d| !matches!(&d.node, Declaration::Datatype(dts) if dts.iter().any(|dt| dt.id == 60))),
            "unreachable datatype must be removed"
        );
    }

    // -----------------------------------------------------------------------
    // slice_for_db mode
    // -----------------------------------------------------------------------

    #[test]
    fn exports_removed_in_slice_for_db_mode() {
        // Catches mutant: slice_for_db doesn't suppress exports.
        let file = vec![val_decl(1, prim_exp()), export_decl(1)];
        let result = shake_slicing_for_db(file);
        assert!(
            result
                .iter()
                .all(|d| !matches!(&d.node, Declaration::Export(_, _, _))),
            "Declaration::Export must be removed in slice_for_db mode"
        );
    }

    #[test]
    fn exports_kept_in_normal_mode() {
        // Catches mutant: normal shake drops exports.
        let file = vec![val_decl(1, prim_exp()), export_decl(1)];
        let result = shake(file);
        assert!(
            result
                .iter()
                .any(|d| matches!(&d.node, Declaration::Export(_, _, _))),
            "Declaration::Export must be kept in normal shake"
        );
    }

    #[test]
    fn tasks_removed_in_slice_for_db_mode() {
        // Catches mutant: tasks survive slice_for_db.
        let file = vec![Located::new(
            Declaration::Task(prim_exp(), prim_exp()),
            dummy_span(),
        )];
        let result = shake_slicing_for_db(file);
        assert!(
            result
                .iter()
                .all(|d| !matches!(&d.node, Declaration::Task(_, _))),
            "Declaration::Task must be removed in slice_for_db mode"
        );
    }

    #[test]
    fn tables_kept_in_slice_for_db_mode() {
        // Catches mutant: tables are suppressed by slice_for_db.
        let file = vec![table_decl(5)];
        let result = shake_slicing_for_db(file);
        assert!(
            result
                .iter()
                .any(|d| matches!(&d.node, Declaration::Table { .. })),
            "Declaration::Table must be kept even in slice_for_db mode"
        );
    }

    #[test]
    fn table_constructor_dep_reachable_in_normal_mode() {
        // Catches mutant: table deps are not traversed.
        let file = vec![
            con_decl(99, unit_con()), // the table's column type
            Located::new(
                Declaration::Table {
                    sql_name: "t".into(),
                    id: 1,
                    con: named_con(99), // references id=99
                    sql_con: String::new(),
                    exp: prim_exp(),
                    pk_con: unit_con(),
                    pk_exp: prim_exp(),
                    unique_con: unit_con(),
                },
                dummy_span(),
            ),
        ];
        let result = shake(file);
        assert!(
            result
                .iter()
                .any(|d| matches!(&d.node, Declaration::Constructor(_, id, _, _) if *id == 99)),
            "type referenced by table column must be kept"
        );
    }

    #[test]
    fn on_error_handler_kept_in_normal_mode() {
        // Catches mutant: OnError is always suppressed.
        let file = vec![
            val_decl(3, prim_exp()),
            Located::new(Declaration::OnError(3), dummy_span()),
        ];
        let result = shake(file);
        assert!(
            result
                .iter()
                .any(|d| matches!(&d.node, Declaration::OnError(_))),
            "Declaration::OnError must be kept in normal mode"
        );
        // And the referenced val must be kept.
        assert!(
            result
                .iter()
                .any(|d| matches!(&d.node, Declaration::Val(_, id, _, _, _) if *id == 3)),
            "val referenced by OnError must be kept"
        );
    }

    #[test]
    fn on_error_handler_removed_in_slice_for_db_mode() {
        // Catches mutant: OnError survives slice_for_db.
        let file = vec![Located::new(Declaration::OnError(3), dummy_span())];
        let result = shake_slicing_for_db(file);
        assert!(
            result
                .iter()
                .all(|d| !matches!(&d.node, Declaration::OnError(_))),
            "Declaration::OnError must be removed in slice_for_db mode"
        );
    }

    // -----------------------------------------------------------------------
    // Server call deps
    // -----------------------------------------------------------------------

    #[test]
    fn server_call_target_is_kept() {
        // Catches mutant: Expression::ServerCall id is not treated as a dep.
        let server_fn_exp = Located::new(
            Expression::ServerCall(77, vec![], unit_con(), crate::settings::FailureMode::Error),
            dummy_span(),
        );
        let file = vec![
            val_decl(77, prim_exp()),   // the server function
            val_decl(1, server_fn_exp), // caller
            export_decl(1),
        ];
        let result = shake(file);
        let ids: Vec<usize> = result
            .iter()
            .filter_map(|d| match &d.node {
                Declaration::Val(_, id, _, _, _) => Some(*id),
                _ => None,
            })
            .collect();
        assert!(ids.contains(&77), "server call target must be kept");
    }

    // -----------------------------------------------------------------------
    // Empty file
    // -----------------------------------------------------------------------

    #[test]
    fn empty_file_stays_empty() {
        // Catches mutant: shake panics or adds phantom decls on empty input.
        let result = shake(vec![]);
        assert!(
            result.is_empty(),
            "shaking an empty file must yield an empty file"
        );
    }

    // -----------------------------------------------------------------------
    // Cycle safety (mutually recursive types)
    // -----------------------------------------------------------------------

    #[test]
    fn cyclic_constructor_refs_do_not_loop_forever() {
        // Catches mutant: transitive closure loops forever on cycles.
        // con A = Named(B), con B = Named(A)  — a type cycle.
        let file = vec![
            con_decl(1, named_con(2)),
            con_decl(2, named_con(1)),
            Located::new(
                Declaration::Val("f".into(), 10, named_con(1), prim_exp(), String::new()),
                dummy_span(),
            ),
            export_decl(10),
        ];
        // Should terminate.
        let result = shake(file);
        let con_ids: Vec<usize> = result
            .iter()
            .filter_map(|d| match &d.node {
                Declaration::Constructor(_, id, _, _) => Some(*id),
                _ => None,
            })
            .collect();
        assert!(con_ids.contains(&1));
        assert!(con_ids.contains(&2));
    }
}
