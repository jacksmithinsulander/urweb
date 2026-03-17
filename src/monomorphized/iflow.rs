//! iflow — information-flow analysis pass.
//!
//! Ports `iflow.sml`. Only runs when `settings.debug = true`.
//!
//! The pass performs information-flow analysis to check that database reads
//! satisfy the policies declared by `DPolicy` declarations in the file.
//! It does NOT transform the file; it only reports violations via the
//! ErrorReporter and returns the file reference unchanged.
//!
//! This is a conservative approximation of the full SML implementation,
//! which uses a congruence-closure-based constraint solver.  Here we
//! implement a simplified taint-tracking approach:
//!  - Collect all `Decl::Policy` declarations.
//!  - For each `Decl::Val`/`Decl::Export`, scan the expression for `Exp::Query`
//!    nodes and check that the tables accessed are covered by a policy.
//!  - Report a warning for each uncovered table access when debug mode is on.

#![allow(dead_code, unused_variables)]

use std::collections::BTreeSet;

use crate::error_types::{CompileError, ErrorReporter, Span};
use crate::monomorphized::{Decl, Exp, File, LocDecl, LocExp, Policy};
use crate::settings::Settings;

// ---------------------------------------------------------------------------
// Internal representation of flow constraints (simplified)
// ---------------------------------------------------------------------------

/// A collected policy entry: describes which table (by name) is covered
/// and by which policy kind.
#[derive(Debug, Clone)]
enum PolicyEntry {
    /// `DPolicy (Client e)` — client policy governing reads
    Client,
    /// `DPolicy (Insert e)` — insert policy
    Insert,
    /// `DPolicy (Delete e)` — delete policy
    Delete,
    /// `DPolicy (Update e)` — update policy
    Update,
    /// `DPolicy (Sequence e)` — sequence policy
    Sequence,
}

/// Tracks which tables have explicit policies.
#[derive(Debug, Default)]
struct PolicyEnv {
    /// Table names that appear in some policy expression.
    covered: BTreeSet<String>,
    /// Whether any client policy was declared.
    has_client_policy: bool,
}

impl PolicyEnv {
    fn from_decls(decls: &[LocDecl]) -> Self {
        let mut env = PolicyEnv::default();
        for d in decls {
            match &d.node {
                Decl::Policy(pol) => {
                    match pol {
                        Policy::Client(e) => {
                            env.has_client_policy = true;
                            collect_table_names(e, &mut env.covered);
                        }
                        Policy::Insert(e)
                        | Policy::Delete(e)
                        | Policy::Update(e)
                        | Policy::Sequence(e) => {
                            collect_table_names(e, &mut env.covered);
                        }
                    }
                }
                _ => {}
            }
        }
        env
    }
}

/// Collect any table names referenced in an expression (heuristic: look for
/// `Named` or `Ffi` references whose names look like table names, and for
/// `Query` nodes whose table list is known).
fn collect_table_names(e: &LocExp, out: &mut BTreeSet<String>) {
    match &e.node {
        Exp::Query(qm) => {
            for (tbl, _) in &qm.tables {
                out.insert(tbl.clone());
            }
            collect_table_names(&qm.query, out);
            collect_table_names(&qm.body, out);
            collect_table_names(&qm.initial, out);
        }
        Exp::App(e1, e2) => {
            collect_table_names(e1, out);
            collect_table_names(e2, out);
        }
        Exp::Abs(_, _, _, body) => collect_table_names(body, out),
        Exp::Let(_, _, e1, e2) => {
            collect_table_names(e1, out);
            collect_table_names(e2, out);
        }
        Exp::Seq(e1, e2) => {
            collect_table_names(e1, out);
            collect_table_names(e2, out);
        }
        Exp::Case(disc, arms, _) => {
            collect_table_names(disc, out);
            for (_, arm_e) in arms {
                collect_table_names(arm_e, out);
            }
        }
        Exp::Record(xets) => {
            for (_, e, _) in xets {
                collect_table_names(e, out);
            }
        }
        Exp::FfiApp(_, _, args) => {
            for (a, _) in args {
                collect_table_names(a, out);
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Query-access collection
// ---------------------------------------------------------------------------

/// Collect all `(table_name, span)` pairs accessed inside queries in `e`.
fn collect_query_accesses(e: &LocExp, out: &mut Vec<(String, Span)>) {
    match &e.node {
        Exp::Query(qm) => {
            for (tbl, _) in &qm.tables {
                out.push((tbl.clone(), e.span.clone()));
            }
            collect_query_accesses(&qm.query, out);
            collect_query_accesses(&qm.body, out);
            collect_query_accesses(&qm.initial, out);
        }
        Exp::App(e1, e2) => {
            collect_query_accesses(e1, out);
            collect_query_accesses(e2, out);
        }
        Exp::Abs(_, _, _, body) => collect_query_accesses(body, out),
        Exp::Let(_, _, e1, e2) => {
            collect_query_accesses(e1, out);
            collect_query_accesses(e2, out);
        }
        Exp::Seq(e1, e2) => {
            collect_query_accesses(e1, out);
            collect_query_accesses(e2, out);
        }
        Exp::Case(disc, arms, _) => {
            collect_query_accesses(disc, out);
            for (_, arm_e) in arms {
                collect_query_accesses(arm_e, out);
            }
        }
        Exp::Record(xets) => {
            for (_, e, _) in xets {
                collect_query_accesses(e, out);
            }
        }
        Exp::FfiApp(_, _, args) => {
            for (a, _) in args {
                collect_query_accesses(a, out);
            }
        }
        Exp::Write(e1)
        | Exp::Field(e1, _)
        | Exp::Unop(_, e1)
        | Exp::Dml(e1, _)
        | Exp::Nextval(e1)
        | Exp::Uurlify(e1, _, _)
        | Exp::JavaScript(_, e1)
        | Exp::Recv(e1, _)
        | Exp::Sleep(e1)
        | Exp::Spawn(e1)
        | Exp::ServerCall(e1, _, _, _)
        | Exp::SignalReturn(e1)
        | Exp::SignalSource(e1) => collect_query_accesses(e1, out),
        Exp::Binop(_, _, e1, e2)
        | Exp::Strcat(e1, e2)
        | Exp::Setval(e1, e2)
        | Exp::SignalBind(e1, e2) => {
            collect_query_accesses(e1, out);
            collect_query_accesses(e2, out);
        }
        Exp::Error(e1, _) => collect_query_accesses(e1, out),
        Exp::Redirect(e1, _) => collect_query_accesses(e1, out),
        Exp::ReturnBlob { blob, mime_type, .. } => {
            if let std::option::Option::Some(b) = blob {
                collect_query_accesses(b, out);
            }
            collect_query_accesses(mime_type, out);
        }
        Exp::Closure(_, envs) => {
            for a in envs {
                collect_query_accesses(a, out);
            }
        }
        Exp::Con(_, _, arg) => {
            if let std::option::Option::Some(a) = arg {
                collect_query_accesses(a, out);
            }
        }
        Exp::Some(_, inner) => collect_query_accesses(inner, out),
        Exp::Prim(_) | Exp::Rel(_) | Exp::Named(_) | Exp::Ffi(_, _) | Exp::None(_) => {}
    }
}

// ---------------------------------------------------------------------------
// Check a single exported function
// ---------------------------------------------------------------------------

/// Check the expression `e` (belonging to declaration named `decl_name`)
/// for uncovered table accesses.  Reports each violation via `errors`.
fn check_exp(
    decl_name: &str,
    e: &LocExp,
    policies: &PolicyEnv,
    errors: &mut ErrorReporter,
) {
    let mut accesses: Vec<(String, Span)> = Vec::new();
    collect_query_accesses(e, &mut accesses);

    // If there are no policies at all, do not report (the app simply has no
    // access-control requirements declared).
    if !policies.has_client_policy && policies.covered.is_empty() {
        return;
    }

    for (tbl, span) in accesses {
        if !policies.covered.contains(&tbl) {
            // The table is accessed but has no explicit policy covering it.
            errors.report(CompileError::at(
                span,
                format!(
                    "iflow: '{}' reads from table '{}' which has no declared client policy",
                    decl_name, tbl
                ),
            ));
        }
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Information-flow analysis pass.
///
/// When `settings.debug` is `false` this is a no-op.  When `true` it
/// collects policy declarations and checks each exported function body for
/// uncovered table reads, reporting violations via `errors`.
///
/// The file is never modified by this pass.
pub fn check(file: &File, settings: &Settings, errors: &mut ErrorReporter) {
    if !settings.debug {
        return;
    }

    let (decls, _exports) = file;

    // Phase 1: collect policies.
    let policies = PolicyEnv::from_decls(decls);

    // Phase 2: check every value declaration.
    for d in decls {
        match &d.node {
            Decl::Val(name, _, _, e, _) => {
                check_exp(name, e, &policies, errors);
            }
            Decl::ValRec(vis) => {
                for (name, _, _, e, _) in vis {
                    check_exp(name, e, &policies, errors);
                }
            }
            Decl::Export(_, url, _, _, _, _) => {
                // Export declarations don't carry an expression directly;
                // the body is in the corresponding Val/ValRec.
            }
            _ => {}
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
    use crate::monomorphized::{Decl, Exp, File, QueryMeta, Typ};
    use crate::settings::Settings;

    fn dummy_typ() -> crate::monomorphized::LocTyp {
        Located::dummy(Typ::Record(vec![]))
    }

    fn dummy_exp() -> crate::monomorphized::LocExp {
        Located::dummy(Exp::Record(vec![]))
    }

    fn make_query_exp(table: &str) -> crate::monomorphized::LocExp {
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
    fn check_passthrough_when_debug_false() {
        let file: File = (vec![], vec![]);
        let settings = Settings::default();
        assert!(!settings.debug, "default settings must have debug=false");
        let mut errors = ErrorReporter::new();
        check(&file, &settings, &mut errors);
        assert!(
            !errors.has_errors(),
            "check must be no-op when debug=false"
        );
    }

    #[test]
    fn check_empty_file_no_errors() {
        let file: File = (vec![], vec![]);
        let mut settings = Settings::default();
        settings.debug = true;
        let mut errors = ErrorReporter::new();
        check(&file, &settings, &mut errors);
        assert!(
            !errors.has_errors(),
            "empty file must not produce errors"
        );
    }

    #[test]
    fn check_no_policy_no_error_for_query() {
        // Without any policies, we don't report (no access control requirements).
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
        let mut settings = Settings::default();
        settings.debug = true;
        let mut errors = ErrorReporter::new();
        check(&file, &settings, &mut errors);
        assert!(
            !errors.has_errors(),
            "no policies declared → no iflow errors"
        );
    }

    #[test]
    fn check_with_policy_covering_all_tables_no_error() {
        // A client policy that mentions table "t1" — accessing t1 should be fine.
        let policy_e = make_query_exp("t1");
        let file: File = (
            vec![
                Located::dummy(Decl::Policy(Policy::Client(policy_e))),
                Located::dummy(Decl::Val(
                    "f".into(),
                    1,
                    dummy_typ(),
                    make_query_exp("t1"),
                    "f".into(),
                )),
            ],
            vec![],
        );
        let mut settings = Settings::default();
        settings.debug = true;
        let mut errors = ErrorReporter::new();
        check(&file, &settings, &mut errors);
        assert!(
            !errors.has_errors(),
            "table covered by policy must not trigger iflow error"
        );
    }

    #[test]
    fn check_with_policy_missing_table_reports_error() {
        // A client policy exists (for t1), but the function accesses t2.
        let policy_e = make_query_exp("t1");
        let file: File = (
            vec![
                Located::dummy(Decl::Policy(Policy::Client(policy_e))),
                Located::dummy(Decl::Val(
                    "f".into(),
                    1,
                    dummy_typ(),
                    make_query_exp("t2"),
                    "f".into(),
                )),
            ],
            vec![],
        );
        let mut settings = Settings::default();
        settings.debug = true;
        let mut errors = ErrorReporter::new();
        check(&file, &settings, &mut errors);
        assert!(
            errors.has_errors(),
            "table not covered by any policy must trigger iflow error"
        );
    }

    #[test]
    fn check_valrec_checked() {
        // ValRec entries are also checked.
        let policy_e = make_query_exp("t1");
        let file: File = (
            vec![
                Located::dummy(Decl::Policy(Policy::Client(policy_e))),
                Located::dummy(Decl::ValRec(vec![(
                    "g".into(),
                    2,
                    dummy_typ(),
                    make_query_exp("t3"),
                    "g".into(),
                )])),
            ],
            vec![],
        );
        let mut settings = Settings::default();
        settings.debug = true;
        let mut errors = ErrorReporter::new();
        check(&file, &settings, &mut errors);
        assert!(
            errors.has_errors(),
            "ValRec bodies must also be checked for iflow violations"
        );
    }
}
