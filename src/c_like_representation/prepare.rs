//! Prepare pass: CJR → CJR with prepared SQL statements.
//!
//! Scans SQL query/DML/nextval string expressions for parameterized
//! placeholders (sqlifyInt, sqlifyFloat, etc.) and converts them into
//! prepared statements with numbered parameter slots.
//!
//! Mirrors `Prepare.prepare` in `prepare.sml`.

use std::collections::HashMap;

use crate::c_like_representation::{
    Decl, DmlMeta, Exp, File, LocDecl, LocExp, PreparedDml, PreparedNextval, PreparedQuery,
    QueryMeta,
};
use crate::error_types::Located;
use crate::primitives::{Prim, StringMode};
use crate::settings::{Settings, SqlType};

// ---------------------------------------------------------------------------
// PrepareState — tracks string→id mapping for deduplication
// ---------------------------------------------------------------------------

/// Mutable state threaded through the prepare pass.
///
/// Maps already-seen query strings to their assigned prepared-statement IDs,
/// so identical queries share the same prepared statement.
struct PrepareState {
    map: HashMap<String, usize>,
    /// In insertion order (for emitting DPreparedStatements).
    list: Vec<(String, usize)>,
    count: usize,
}

impl PrepareState {
    fn new() -> Self {
        PrepareState {
            map: HashMap::new(),
            list: Vec::new(),
            count: 0,
        }
    }

    /// Return the ID for query string `s`, inserting if new.
    fn name_of(&mut self, s: String) -> usize {
        if let Some(&id) = self.map.get(&s) {
            return id;
        }
        let id = self.count;
        self.map.insert(s.clone(), id);
        self.list.push((s, id));
        self.count += 1;
        id
    }
}

// ---------------------------------------------------------------------------
// p_blank — parameter placeholder for the current DBMS
// ---------------------------------------------------------------------------

/// Return the SQL parameter placeholder for parameter `n` (1-based) of SQL type `t`.
///
/// - Postgres: `$N::sql_type`  (typed cast)
/// - MySQL / other: `?`
fn p_blank(n: usize, t: &SqlType, settings: &Settings) -> String {
    if settings.dbms == "mysql" {
        "?".to_string()
    } else {
        // Postgres (default): $N::cast
        let cast = postgres_sql_type(t);
        format!("${n}::{cast}")
    }
}

fn postgres_sql_type(t: &SqlType) -> &'static str {
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
        SqlType::Nullable(inner) => postgres_sql_type(inner),
    }
}

// ---------------------------------------------------------------------------
// prepString — try to convert an expression to a prepared statement template
// ---------------------------------------------------------------------------

/// Try to convert the query-string expression `e` into a prepared-statement
/// template.
///
/// On success, returns `(id, template_string)` and updates `st`.
/// Returns `None` if `e` cannot be fully templatized (e.g. contains dynamic
/// SQL that isn't a simple parameter).
fn prep_string(
    e: &LocExp,
    st: &mut PrepareState,
    n: &mut usize,
    parts: &mut Vec<String>,
    settings: &Settings,
) -> bool {
    match &e.node {
        Exp::Prim(Prim::String(_, s)) => {
            parts.push(s.clone());
            true
        }
        Exp::FfiApp(m, f, args) if m == "Basis" && f == "strcat" => {
            if let [(e1, _), (e2, _)] = args.as_slice() {
                prep_string(e1, st, n, parts, settings) && prep_string(e2, st, n, parts, settings)
            } else {
                false
            }
        }
        Exp::FfiApp(m, f, _) if m == "Basis" => {
            let sql_t = sqlify_type(f);
            if let Some(t) = sql_t {
                *n += 1;
                parts.push(p_blank(*n, &t, settings));
                true
            } else {
                false
            }
        }
        // ECase for option: ((PNone, "NULL"), (PSome(PVar), FfiApp(m, x, [Rel 0])))
        // Recognize only the pattern where the nullable value is sqlified
        Exp::Case(scrutinee, arms, _) => {
            // Try to detect the nullable pattern used in prepare.sml:
            // case e of (None => "NULL") | (Some(x) => sqlifyX(x))
            // In our Rust CJR this is ECase with two arms: PNone and PSome(PVar)
            if arms.len() == 2 {
                // Check if arm[0] is (PNone, "NULL") and arm[1] is (PSome(PVar), FfiApp)
                use crate::c_like_representation::Pat;
                let arm0_null = matches!(&arms[0].0.node, Pat::None(_))
                    && matches!(&arms[0].1.node, Exp::Prim(Prim::String(_, s)) if s == "NULL");
                let arm1_sqlify = matches!(&arms[1].0.node, Pat::Some(_, inner) if matches!(&inner.node, Pat::Var(_, _)));
                if arm0_null && arm1_sqlify {
                    if let Exp::FfiApp(m, f, _) = &arms[1].1.node {
                        if m == "Basis" {
                            if let Some(inner_t) = sqlify_type(f) {
                                let nullable_t = SqlType::Nullable(Box::new(inner_t));
                                *n += 1;
                                parts.push(p_blank(*n, &nullable_t, settings));
                                return true;
                            }
                        }
                    }
                    // Try a recursive approach: replace the case with the
                    // inner sqlify call's parameter
                    if let Exp::FfiApp(m, f, inner_args) = &arms[1].1.node {
                        if m == "Basis" {
                            if let Some(inner_t) = sqlify_type(f) {
                                let _ = inner_args; // argument is Rel 0, already handled above
                                let nullable_t = SqlType::Nullable(Box::new(inner_t));
                                *n += 1;
                                parts.push(p_blank(*n, &nullable_t, settings));
                                return true;
                            }
                        }
                    }
                }

                // Alternative pattern: case e of (True => "TRUE") | (False => "FALSE")
                let arm0_true =
                    matches!(&arms[0].1.node, Exp::Prim(Prim::String(_, s)) if s == "TRUE");
                let arm1_false =
                    matches!(&arms[1].1.node, Exp::Prim(Prim::String(_, s)) if s == "FALSE");
                if arm0_true && arm1_false {
                    *n += 1;
                    parts.push(p_blank(*n, &SqlType::Bool, settings));
                    // Use the scrutinee for parameter binding (emit as placeholder)
                    let _ = scrutinee;
                    return true;
                }
            }
            false
        }
        _ => false,
    }
}

/// Maps a `sqlifyX` FFI function name to the corresponding `SqlType`.
fn sqlify_type(f: &str) -> Option<SqlType> {
    match f {
        "sqlifyInt" => Some(SqlType::Int),
        "sqlifyFloat" => Some(SqlType::Float),
        "sqlifyString" => Some(SqlType::String),
        "sqlifyChar" => Some(SqlType::Char),
        "sqlifyBool" => Some(SqlType::Bool),
        "sqlifyTime" => Some(SqlType::Time),
        "sqlifyClocktime" => Some(SqlType::Clocktime),
        "sqlifyCalendardate" => Some(SqlType::Calendardate),
        "sqlifyBlob" => Some(SqlType::Blob),
        "sqlifyChannel" => Some(SqlType::Channel),
        "sqlifyClient" => Some(SqlType::Client),
        _ => None,
    }
}

/// Try to turn the expression `e` into a prepared statement template.
///
/// Returns `Some((id, template))` on success, `None` if the expression
/// contains dynamic SQL that cannot be templatized.
fn try_prepare(e: &LocExp, st: &mut PrepareState, settings: &Settings) -> Option<(usize, String)> {
    let mut parts = Vec::new();
    let mut n = 0usize;
    if prep_string(e, st, &mut n, &mut parts, settings) {
        let template = parts.join("");
        let id = st.name_of(template.clone());
        Some((id, template))
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Expression traversal
// ---------------------------------------------------------------------------

fn prep_exp(e: LocExp, st: &mut PrepareState, settings: &Settings) -> LocExp {
    let loc = e.span.clone();
    let new_node = match e.node {
        Exp::Prim(_) | Exp::Rel(_) | Exp::Named(_) | Exp::Ffi(_, _) => return e,

        Exp::Con(dk, pc, opt_e) => {
            let opt_e = opt_e.map(|inner| Box::new(prep_exp(*inner, st, settings)));
            Exp::Con(dk, pc, opt_e)
        }
        Exp::None(_) => return e,
        Exp::Some(t, inner) => Exp::Some(t, Box::new(prep_exp(*inner, st, settings))),

        Exp::FfiApp(m, f, args) => {
            let args = args
                .into_iter()
                .map(|(ae, at)| (prep_exp(ae, st, settings), at))
                .collect();
            Exp::FfiApp(m, f, args)
        }
        Exp::App(e1, args) => {
            let e1 = Box::new(prep_exp(*e1, st, settings));
            let args = args
                .into_iter()
                .map(|ae| prep_exp(ae, st, settings))
                .collect();
            Exp::App(e1, args)
        }

        Exp::Unop(op, inner) => Exp::Unop(op, Box::new(prep_exp(*inner, st, settings))),
        Exp::Binop(op, e1, e2) => Exp::Binop(
            op,
            Box::new(prep_exp(*e1, st, settings)),
            Box::new(prep_exp(*e2, st, settings)),
        ),

        Exp::Record(id, fields) => {
            let fields = fields
                .into_iter()
                .map(|(name, fe)| (name, prep_exp(fe, st, settings)))
                .collect();
            Exp::Record(id, fields)
        }
        Exp::Field(inner, f) => Exp::Field(Box::new(prep_exp(*inner, st, settings)), f),

        Exp::Case(scrutinee, arms, meta) => {
            let scrutinee = Box::new(prep_exp(*scrutinee, st, settings));
            let arms = arms
                .into_iter()
                .map(|(p, ae)| (p, prep_exp(ae, st, settings)))
                .collect();
            Exp::Case(scrutinee, arms, meta)
        }

        Exp::Error(inner, t) => Exp::Error(Box::new(prep_exp(*inner, st, settings)), t),
        Exp::ReturnBlob { blob, mime_type, t } => {
            let blob = blob.map(|b| Box::new(prep_exp(*b, st, settings)));
            let mime_type = Box::new(prep_exp(*mime_type, st, settings));
            Exp::ReturnBlob { blob, mime_type, t }
        }
        Exp::Redirect(inner, t) => Exp::Redirect(Box::new(prep_exp(*inner, st, settings)), t),

        Exp::Write(inner) => Exp::Write(Box::new(prep_exp(*inner, st, settings))),
        Exp::Seq(e1, e2) => Exp::Seq(
            Box::new(prep_exp(*e1, st, settings)),
            Box::new(prep_exp(*e2, st, settings)),
        ),
        Exp::Let(x, t, e1, e2) => Exp::Let(
            x,
            t,
            Box::new(prep_exp(*e1, st, settings)),
            Box::new(prep_exp(*e2, st, settings)),
        ),

        // ---------------- The interesting cases ----------------
        Exp::Query(qm) => {
            // Recursively prepare the body.
            let body = Box::new(prep_exp(*qm.body, st, settings));

            // Try to templatize the query string.
            let prepared = try_prepare(&qm.query, st, settings).map(|(id, query)| PreparedQuery {
                id,
                query,
                nested: true,
            });

            Exp::Query(QueryMeta {
                body,
                prepared,
                ..qm
            })
        }

        Exp::Dml(dm) => {
            // Try to templatize the DML string.
            let prepared =
                try_prepare(&dm.dml, st, settings).map(|(id, dml)| PreparedDml { id, dml });
            Exp::Dml(DmlMeta { prepared, ..dm })
        }

        Exp::Nextval { seq, prepared: _ } => {
            // If the DBMS supports NEXTVAL, wrap as SELECT NEXTVAL(...)
            if settings.dbms != "mysql" {
                // Build SELECT NEXTVAL('seq')
                let select_nextval = build_nextval_query(&seq, &loc);
                let prepared = try_prepare(&select_nextval, st, settings)
                    .map(|(id, query)| PreparedNextval { id, query });
                Exp::Nextval { seq, prepared }
            } else {
                Exp::Nextval {
                    seq,
                    prepared: None,
                }
            }
        }

        Exp::Setval { seq, count } => Exp::Setval {
            seq: Box::new(prep_exp(*seq, st, settings)),
            count: Box::new(prep_exp(*count, st, settings)),
        },

        Exp::Uurlify(inner, t, b) => Exp::Uurlify(Box::new(prep_exp(*inner, st, settings)), t, b),
    };
    Located::new(new_node, loc)
}

/// Build a `SELECT NEXTVAL('seq')` expression from a sequence name expression.
fn build_nextval_query(seq: &LocExp, loc: &crate::error_types::Span) -> LocExp {
    let str_t = Located::new(
        crate::c_like_representation::Typ::Ffi("Basis".into(), "string".into()),
        loc.clone(),
    );
    match &seq.node {
        Exp::Prim(Prim::String(_, s)) => Located::new(
            Exp::Prim(Prim::String(
                StringMode::Normal,
                format!("SELECT NEXTVAL('{s}')"),
            )),
            loc.clone(),
        ),
        _ => {
            // "SELECT NEXTVAL('" ^ seq ^ "')"
            let prefix = Located::new(
                Exp::Prim(Prim::String(StringMode::Normal, "SELECT NEXTVAL('".into())),
                loc.clone(),
            );
            let suffix = Located::new(
                Exp::Prim(Prim::String(StringMode::Normal, "')".into())),
                loc.clone(),
            );
            let inner = Located::new(
                Exp::FfiApp(
                    "Basis".into(),
                    "strcat".into(),
                    vec![(seq.clone(), str_t.clone()), (suffix, str_t.clone())],
                ),
                loc.clone(),
            );
            Located::new(
                Exp::FfiApp(
                    "Basis".into(),
                    "strcat".into(),
                    vec![
                        (prefix, str_t),
                        (
                            inner,
                            Located::new(
                                crate::c_like_representation::Typ::Ffi(
                                    "Basis".into(),
                                    "string".into(),
                                ),
                                loc.clone(),
                            ),
                        ),
                    ],
                ),
                loc.clone(),
            )
        }
    }
}

// ---------------------------------------------------------------------------
// Declaration traversal
// ---------------------------------------------------------------------------

fn prep_decl(d: LocDecl, st: &mut PrepareState, settings: &Settings) -> LocDecl {
    let loc = d.span.clone();
    let new_node = match d.node {
        Decl::Val(x, n, t, e) => Decl::Val(x, n, t, prep_exp(e, st, settings)),
        Decl::Fun(x, n, params, t, e) => Decl::Fun(x, n, params, t, prep_exp(e, st, settings)),
        Decl::FunRec(fs) => {
            let fs = fs
                .into_iter()
                .map(|(x, n, params, t, e)| (x, n, params, t, prep_exp(e, st, settings)))
                .collect();
            Decl::FunRec(fs)
        }
        Decl::Task(task, x1, x2, e) => Decl::Task(task, x1, x2, prep_exp(e, st, settings)),
        // All other declarations pass through unchanged.
        other => other,
    };
    Located::new(new_node, loc)
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Run the prepare pass on a CJR file.
///
/// Scans all SQL query/DML/nextval expressions, converts them to prepared
/// statements where possible, and prepends a `DPreparedStatements` declaration
/// with the resulting list of (query_string, id) pairs.
///
/// Mirrors `Prepare.prepare` in `prepare.sml`.
pub fn prepare(file: File, settings: &Settings) -> File {
    let (decls, exports) = file;
    let mut st = PrepareState::new();

    let decls: Vec<LocDecl> = decls
        .into_iter()
        .map(|d| prep_decl(d, &mut st, settings))
        .collect();

    // Prepend the DPreparedStatements declaration (like the SML does).
    let ps_decl = Located::dummy(Decl::PreparedStatements(st.list));
    let mut out = Vec::with_capacity(decls.len() + 1);
    out.push(ps_decl);
    out.extend(decls);

    (out, exports)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::c_like_representation::File;
    use crate::settings::Settings;

    fn empty_file() -> File {
        (vec![], vec![])
    }

    #[test]
    fn prepare_empty_file_adds_empty_prepared_stmts() {
        let settings = Settings::default();
        let (decls, exports) = prepare(empty_file(), &settings);
        assert!(exports.is_empty());
        // First decl must be PreparedStatements with zero entries.
        assert_eq!(decls.len(), 1);
        assert!(matches!(
            &decls[0].node,
            Decl::PreparedStatements(v) if v.is_empty()
        ));
    }

    #[test]
    fn prep_string_literal_becomes_template() {
        let mut st = PrepareState::new();
        let settings = Settings::default();
        let e = Located::dummy(Exp::Prim(Prim::String(
            StringMode::Normal,
            "SELECT 1".into(),
        )));
        let result = try_prepare(&e, &mut st, &settings);
        assert!(result.is_some());
        let (id, tmpl) = result.unwrap();
        assert_eq!(id, 0);
        assert_eq!(tmpl, "SELECT 1");
    }

    #[test]
    fn prep_string_sqlify_int_postgres() {
        let mut st = PrepareState::new();
        let mut settings = Settings::default();
        settings.dbms = "postgres".into();

        // sqlifyInt(x) → $1::int8
        let arg = Located::dummy(Exp::Rel(0));
        let t = Located::dummy(crate::c_like_representation::Typ::Ffi(
            "Basis".into(),
            "int".into(),
        ));
        let e = Located::dummy(Exp::FfiApp(
            "Basis".into(),
            "sqlifyInt".into(),
            vec![(arg, t)],
        ));
        let result = try_prepare(&e, &mut st, &settings);
        assert!(result.is_some());
        let (_, tmpl) = result.unwrap();
        assert_eq!(tmpl, "$1::int8");
    }

    #[test]
    fn prep_string_sqlify_int_mysql() {
        let mut st = PrepareState::new();
        let mut settings = Settings::default();
        settings.dbms = "mysql".into();

        let arg = Located::dummy(Exp::Rel(0));
        let t = Located::dummy(crate::c_like_representation::Typ::Ffi(
            "Basis".into(),
            "int".into(),
        ));
        let e = Located::dummy(Exp::FfiApp(
            "Basis".into(),
            "sqlifyInt".into(),
            vec![(arg, t)],
        ));
        let result = try_prepare(&e, &mut st, &settings);
        assert!(result.is_some());
        let (_, tmpl) = result.unwrap();
        assert_eq!(tmpl, "?");
    }

    #[test]
    fn prep_string_strcat_combines() {
        let mut st = PrepareState::new();
        let mut settings = Settings::default();
        settings.dbms = "postgres".into();

        let str_t = Located::dummy(crate::c_like_representation::Typ::Ffi(
            "Basis".into(),
            "string".into(),
        ));
        let lit = Located::dummy(Exp::Prim(Prim::String(
            StringMode::Normal,
            "SELECT * FROM t WHERE id = ".into(),
        )));
        let arg = Located::dummy(Exp::Rel(0));
        let int_t = Located::dummy(crate::c_like_representation::Typ::Ffi(
            "Basis".into(),
            "int".into(),
        ));
        let sqlify = Located::dummy(Exp::FfiApp(
            "Basis".into(),
            "sqlifyInt".into(),
            vec![(arg, int_t)],
        ));
        let e = Located::dummy(Exp::FfiApp(
            "Basis".into(),
            "strcat".into(),
            vec![(lit, str_t.clone()), (sqlify, str_t)],
        ));
        let result = try_prepare(&e, &mut st, &settings);
        assert!(result.is_some());
        let (_, tmpl) = result.unwrap();
        assert_eq!(tmpl, "SELECT * FROM t WHERE id = $1::int8");
    }

    #[test]
    fn prep_string_dynamic_returns_none() {
        let mut st = PrepareState::new();
        let settings = Settings::default();
        // A dynamic expression that can't be templatized.
        let e = Located::dummy(Exp::Rel(0));
        let result = try_prepare(&e, &mut st, &settings);
        assert!(result.is_none());
    }

    #[test]
    fn deduplication_same_query_gets_same_id() {
        let mut st = PrepareState::new();
        let settings = Settings::default();
        let e = Located::dummy(Exp::Prim(Prim::String(
            StringMode::Normal,
            "SELECT 1".into(),
        )));
        let (id1, _) = try_prepare(&e, &mut st, &settings).unwrap();
        let (id2, _) = try_prepare(&e, &mut st, &settings).unwrap();
        assert_eq!(id1, id2);
    }

    #[test]
    fn different_queries_get_different_ids() {
        let mut st = PrepareState::new();
        let settings = Settings::default();
        let e1 = Located::dummy(Exp::Prim(Prim::String(
            StringMode::Normal,
            "SELECT 1".into(),
        )));
        let e2 = Located::dummy(Exp::Prim(Prim::String(
            StringMode::Normal,
            "SELECT 2".into(),
        )));
        let (id1, _) = try_prepare(&e1, &mut st, &settings).unwrap();
        let (id2, _) = try_prepare(&e2, &mut st, &settings).unwrap();
        assert_ne!(id1, id2);
    }
}
