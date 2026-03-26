//! Relational SQL runtime emission (SQLite, MySQL, PostgreSQL clients).
//!
//! The **`uw_*` contract** for these drivers is documented under [`crate::c_like_representation::db_drivers`].

use crate::c_like_representation::LocTyp;
use crate::db::{ProjectDb, ProjectDbCtx, SqlFlavor};
use crate::settings::Settings;

pub(crate) fn emit_dbms_c_code(
    settings: &Settings,
    tables: &[(String, Vec<(String, LocTyp)>)],
    prepared_stmts: &[(String, usize)],
) -> String {
    let dbstring = settings
        .dbstring
        .as_deref()
        .unwrap_or("")
        .replace('"', "\\\"");

    let mut out = match ProjectDbCtx::new(&settings.db_backend).resolved() {
        ProjectDb::Sql(SqlFlavor::Sqlite) => gen_sqlite_c_code(&dbstring, tables, prepared_stmts),
        ProjectDb::Sql(SqlFlavor::Mysql) => gen_mysql_c_code(&dbstring, tables, prepared_stmts),
        ProjectDb::Sql(SqlFlavor::Postgresql) => {
            gen_postgres_c_code(&dbstring, tables, prepared_stmts)
        }
        ProjectDb::Rocksdb => crate::c_like_representation::native_db_runtime::emit_rocksdb_c_code(
            &dbstring,
            tables,
            prepared_stmts,
        ),
        ProjectDb::Persy => crate::c_like_representation::native_db_runtime::emit_persy_c_code(
            &dbstring,
            tables,
            prepared_stmts,
        ),
        ProjectDb::Ndb => crate::c_like_representation::native_db_runtime::emit_ndb_c_code(
            &dbstring,
            tables,
            prepared_stmts,
        ),
        ProjectDb::Tigerbeetle => {
            crate::c_like_representation::native_db_runtime::emit_tigerbeetle_c_code(
                &dbstring,
                tables,
                prepared_stmts,
            )
        }
    };
    out.push_str(
        &crate::c_like_representation::native_db_runtime::emit_urweb_native_ffi_bundle(settings),
    );
    out
}

fn gen_sqlite_c_code(
    dbpath: &str,
    tables: &[(String, Vec<(String, LocTyp)>)],
    prepared: &[(String, usize)],
) -> String {
    let mut out = String::new();

    // sqlite3 header
    out.push_str("#include <sqlite3.h>\n\n");

    // uw_client_init: set SQLite-specific format strings
    out.push_str(concat!(
        "static void uw_client_init(void) {\n",
        "uw_sqlfmtInt = \"%lld%n\";\n",
        "uw_sqlfmtFloat = \"%.16g%n\";\n",
        "uw_Estrings = 0;\n",
        "uw_sql_type_annotations = 0;\n",
        "uw_sqlsuffixString = \"\";\n",
        "uw_sqlsuffixChar = \"\";\n",
        "uw_sqlsuffixBlob = \"\";\n",
        "uw_sqlfmtUint4 = \"%u%n\";\n",
        "}\n\n",
    ));

    // uw_conn: SQLite connection wrapper with prepared statement slots
    out.push_str("typedef struct {\nsqlite3 *conn;\n");
    for i in 0..prepared.len() {
        out.push_str(&format!("sqlite3_stmt *p{};\n", i));
    }
    out.push_str("} uw_conn;\n\n");

    // uw_db_validate: check schema exists
    out.push_str("static void uw_db_validate(uw_context ctx) {\n");
    if !tables.is_empty() {
        out.push_str("uw_conn *conn = uw_get_db(ctx);\n");
        out.push_str("sqlite3_stmt *stmt;\n");
        out.push_str("int res;\n");
        for (tbl, _) in tables {
            out.push_str(&format!(
                "res = sqlite3_prepare_v2(conn->conn, \"SELECT COUNT(*) FROM {tbl}\", -1, &stmt, NULL);\n",
            ));
            out.push_str(&format!(
                "if (res != SQLITE_OK) uw_error(ctx, FATAL, \"Table {tbl} does not exist in the database.\");\n",
            ));
            out.push_str("sqlite3_finalize(stmt);\n");
        }
    }
    out.push_str("}\n\n");

    // uw_db_prepare: prepare SQL statements
    if !prepared.is_empty() {
        out.push_str("static void uw_db_prepare(uw_context ctx) {\n");
        out.push_str("uw_conn *conn = uw_get_db(ctx);\n\n");
        for (i, (sql, _)) in prepared.iter().enumerate() {
            let escaped = sql.replace('\\', "\\\\").replace('"', "\\\"");
            out.push_str("{ int _pr;\n");
            out.push_str(&format!(
                "do {{ _pr = sqlite3_prepare_v2(conn->conn, \"{escaped}\", -1, &conn->p{i}, NULL); if (_pr == SQLITE_BUSY) sleep(1); }} while (_pr == SQLITE_BUSY);\n"
            ));
            out.push_str("if (_pr != SQLITE_OK) {\n");
            out.push_str("char msg[1024];\n");
            out.push_str("strncpy(msg, sqlite3_errmsg(conn->conn), 1024);\n");
            out.push_str("msg[1023] = 0;\n");
            for j in 0..i {
                out.push_str(&format!("sqlite3_finalize(conn->p{j});\n"));
            }
            out.push_str(&format!("sqlite3_finalize(conn->p{i});\n"));
            out.push_str("sqlite3_close(conn->conn);\n");
            out.push_str(&format!(
                "uw_error(ctx, FATAL, \"Error preparing statement: {escaped}<br />%s\", msg);\n"
            ));
            out.push_str("}\n}\n");
        }
        out.push_str("}\n\n");
    } else {
        out.push_str("static void uw_db_prepare(uw_context ctx) { }\n\n");
    }

    // uw_db_init: open database
    out.push_str("static void uw_db_init(uw_context ctx) {\n");
    out.push_str("sqlite3 *sqlite;\n");
    out.push_str("sqlite3_stmt *stmt;\n");
    out.push_str("uw_conn *conn;\n\n");
    out.push_str(&format!(
        "if (sqlite3_open(\"{dbpath}\", &sqlite) != SQLITE_OK) uw_error(ctx, FATAL, \"Can't open SQLite database.\");\n\n"
    ));
    out.push_str(
        "if (sqlite3_exec(sqlite, \"PRAGMA foreign_keys = ON\", NULL, NULL, NULL) != SQLITE_OK)\n",
    );
    out.push_str("uw_error(ctx, FATAL, \"Can't enable foreign_keys for SQLite database\");\n\n");
    out.push_str("if (uw_database_max < SIZE_MAX) {\n");
    out.push_str("char buf[100];\n\n");
    out.push_str("sprintf(buf, \"PRAGMA max_page_count = %llu\", (unsigned long long)(uw_database_max / 1024));\n\n");
    out.push_str("if (sqlite3_prepare_v2(sqlite, buf, -1, &stmt, NULL) != SQLITE_OK) {\n");
    out.push_str("sqlite3_close(sqlite);\n");
    out.push_str(
        "uw_error(ctx, FATAL, \"Can't prepare max_page_count query for SQLite database\");\n",
    );
    out.push_str("}\n\n");
    out.push_str("if (sqlite3_step(stmt) != SQLITE_ROW) {\n");
    out.push_str("sqlite3_finalize(stmt);\n");
    out.push_str("sqlite3_close(sqlite);\n");
    out.push_str(
        "uw_error(ctx, FATAL, \"Can't set max_page_count parameter for SQLite database\");\n",
    );
    out.push_str("}\n\n");
    out.push_str("sqlite3_finalize(stmt);\n");
    out.push_str("}\n\n");
    out.push_str("conn = calloc(1, sizeof(uw_conn));\n");
    out.push_str("conn->conn = sqlite;\n");
    out.push_str("uw_set_db(ctx, conn);\n");
    out.push_str("uw_db_validate(ctx);\n");
    out.push_str("uw_db_prepare(ctx);\n");
    out.push_str("}\n\n");

    // uw_db_close: finalize prepared statements then close
    out.push_str("static void uw_db_close(uw_context ctx) {\n");
    out.push_str("uw_conn *conn = uw_get_db(ctx);\n");
    for i in 0..prepared.len() {
        out.push_str(&format!("if (conn->p{i}) sqlite3_finalize(conn->p{i});\n"));
    }
    out.push_str("sqlite3_close(conn->conn);\n");
    out.push_str("}\n\n");

    // uw_db_begin
    out.push_str(concat!(
        "static int uw_db_begin(uw_context ctx, int could_write) {\n",
        "uw_conn *conn = uw_get_db(ctx);\n\n",
        "if (sqlite3_exec(conn->conn, \"BEGIN\", NULL, NULL, NULL) == SQLITE_OK)\n",
        "return 0;\n",
        "else {\n",
        "fprintf(stderr, \"Begin error: %s<br />\", sqlite3_errmsg(conn->conn));\n",
        "return 1;\n",
        "}\n",
        "}\n",
    ));

    // uw_db_commit
    out.push_str(concat!(
        "static int uw_db_commit(uw_context ctx) {\n",
        "uw_conn *conn = uw_get_db(ctx);\n",
        "if (sqlite3_exec(conn->conn, \"COMMIT\", NULL, NULL, NULL) == SQLITE_OK)\n",
        "return 0;\n",
        "else {\n",
        "fprintf(stderr, \"Commit error: %s<br />\", sqlite3_errmsg(conn->conn));\n",
        "return 1;\n",
        "}\n",
        "}\n\n",
    ));

    // uw_db_rollback
    out.push_str(concat!(
        "static int uw_db_rollback(uw_context ctx) {\n",
        "uw_conn *conn = uw_get_db(ctx);\n",
        "if (sqlite3_exec(conn->conn, \"ROLLBACK\", NULL, NULL, NULL) == SQLITE_OK)\n",
        "return 0;\n",
        "else {\n",
        "fprintf(stderr, \"Rollback error: %s<br />\", sqlite3_errmsg(conn->conn));\n",
        "return 1;\n",
        "}\n",
        "}\n\n",
    ));

    out
}

fn gen_mysql_c_code(
    dbstring: &str,
    _tables: &[(String, Vec<(String, LocTyp)>)],
    prepared: &[(String, usize)],
) -> String {
    // Parse dbstring: space-separated key=value tokens
    let mut host: Option<String> = None;
    let mut user: Option<String> = None;
    let mut passwd: Option<String> = None;
    let mut db: Option<String> = None;
    let mut port: Option<u32> = None;
    let mut unix_socket: Option<String> = None;

    for token in dbstring.split_whitespace() {
        if let Some((k, v)) = token.split_once('=') {
            match k {
                "host" => {
                    if v.starts_with('/') {
                        unix_socket = Some(v.to_string());
                    } else {
                        host = Some(v.to_string());
                    }
                }
                "hostaddr" => host = Some(v.to_string()),
                "port" => port = v.parse().ok(),
                "dbname" => db = Some(v.to_string()),
                "user" => user = Some(v.to_string()),
                "password" => passwd = Some(v.to_string()),
                _ => {}
            }
        }
    }

    fn c_str_opt(s: &Option<String>) -> String {
        match s {
            None => "NULL".to_string(),
            Some(s) => format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\"")),
        }
    }

    let mut out = String::new();

    out.push_str("#include <mysql.h>\n\n");

    // uw_conn struct
    out.push_str("typedef struct {\nMYSQL *conn;\n");
    for i in 0..prepared.len() {
        out.push_str(&format!("MYSQL_STMT *p{};\n", i));
    }
    out.push_str("} uw_conn;\n\n");

    // uw_client_init
    out.push_str(concat!(
        "static void uw_client_init(void) {\n",
        "uw_sqlfmtInt = \"%lld%n\";\n",
        "uw_sqlfmtFloat = \"%.16g%n\";\n",
        "uw_Estrings = 0;\n",
        "uw_sql_type_annotations = 0;\n",
        "uw_sqlsuffixString = \"\";\n",
        "uw_sqlsuffixChar = \"\";\n",
        "uw_sqlsuffixBlob = \"\";\n",
        "uw_sqlfmtUint4 = \"%u%n\";\n\n",
        "if (mysql_library_init(0, NULL, NULL)) {\n",
        "fprintf(stderr, \"Could not initialize MySQL library\\n\");\n",
        "exit(1);\n",
        "}\n",
        "}\n\n",
    ));

    // uw_db_validate (stub — full table-checking requires persistent protocol check)
    out.push_str("static void uw_db_validate(uw_context ctx) { }\n\n");

    // uw_db_prepare
    if !prepared.is_empty() {
        out.push_str("static void uw_db_prepare(uw_context ctx) {\n");
        out.push_str("uw_conn *conn = uw_get_db(ctx);\n");
        out.push_str("MYSQL_STMT *stmt;\n\n");
        for (i, (sql, _)) in prepared.iter().enumerate() {
            let escaped = sql.replace('\\', "\\\\").replace('"', "\\\"");
            let sql_len = sql.len();
            out.push_str("stmt = mysql_stmt_init(conn->conn);\n");
            out.push_str("if (stmt == NULL) {\n");
            for j in 0..i {
                out.push_str(&format!("mysql_stmt_close(conn->p{j});\n"));
            }
            out.push_str("mysql_close(conn->conn);\n");
            out.push_str(
                "uw_error(ctx, FATAL, \"Out of memory allocating prepared statement\");\n",
            );
            out.push_str("}\n");
            out.push_str(&format!("conn->p{i} = stmt;\n"));
            out.push_str(&format!(
                "if (mysql_stmt_prepare(stmt, \"{escaped}\", {sql_len})) {{\n"
            ));
            out.push_str("char msg[1024];\n");
            out.push_str("strncpy(msg, mysql_stmt_error(stmt), 1024);\n");
            out.push_str("msg[1023] = 0;\n");
            for j in 0..=i {
                out.push_str(&format!("mysql_stmt_close(conn->p{j});\n"));
            }
            out.push_str("mysql_close(conn->conn);\n");
            out.push_str("uw_error(ctx, FATAL, \"Error preparing statement: %s\", msg);\n");
            out.push_str("}\n");
        }
        out.push_str("}\n\n");
    } else {
        out.push_str("static void uw_db_prepare(uw_context ctx) { }\n\n");
    }

    // uw_db_init
    let host_c = c_str_opt(&host);
    let user_c = c_str_opt(&user);
    let passwd_c = c_str_opt(&passwd);
    let db_c = c_str_opt(&db);
    let port_c = port
        .map(|p| p.to_string())
        .unwrap_or_else(|| "0".to_string());
    let sock_c = c_str_opt(&unix_socket);
    out.push_str("static void uw_db_init(uw_context ctx) {\n");
    out.push_str("MYSQL *mysql = mysql_init(NULL);\n");
    out.push_str("uw_conn *conn;\n");
    out.push_str("if (mysql == NULL) uw_error(ctx, FATAL, \"libmysqlclient can't allocate a connection.\");\n");
    out.push_str(&format!(
        "if (mysql_real_connect(mysql, {host_c}, {user_c}, {passwd_c}, {db_c}, {port_c}, {sock_c}, CLIENT_MULTI_STATEMENTS) == NULL) {{\n"
    ));
    out.push_str("char msg[1024];\n");
    out.push_str("strncpy(msg, mysql_error(mysql), 1024);\n");
    out.push_str("msg[1023] = 0;\n");
    out.push_str("mysql_close(mysql);\n");
    out.push_str("uw_error(ctx, FATAL, \"Connection to MySQL server failed: %s\", msg);\n");
    out.push_str("}\n\n");
    out.push_str("if (mysql_set_character_set(mysql, \"utf8\")) {\n");
    out.push_str("char msg[1024];\n");
    out.push_str("strncpy(msg, mysql_error(mysql), 1024);\n");
    out.push_str("msg[1023] = 0;\n");
    out.push_str("mysql_close(mysql);\n");
    out.push_str("uw_error(ctx, FATAL, \"Error setting UTF-8 character set for MySQL connection: %s\", msg);\n");
    out.push_str("}\n\n");
    out.push_str("conn = calloc(1, sizeof(uw_conn));\n");
    out.push_str("conn->conn = mysql;\n");
    out.push_str("uw_set_db(ctx, conn);\n");
    out.push_str("uw_db_validate(ctx);\n");
    out.push_str("uw_db_prepare(ctx);\n");
    out.push_str("}\n\n");

    // uw_db_close
    out.push_str("static void uw_db_close(uw_context ctx) {\n");
    out.push_str("uw_conn *conn = uw_get_db(ctx);\n");
    for i in 0..prepared.len() {
        out.push_str(&format!("if (conn->p{i}) mysql_stmt_close(conn->p{i});\n"));
    }
    out.push_str("mysql_close(conn->conn);\n");
    out.push_str("}\n\n");

    // uw_db_begin
    out.push_str(concat!(
        "static int uw_db_begin(uw_context ctx, int could_write) {\n",
        "uw_conn *conn = uw_get_db(ctx);\n\n",
        "return mysql_query(conn->conn, \"SET TRANSACTION ISOLATION LEVEL SERIALIZABLE; BEGIN\") ? 1 : (mysql_next_result(conn->conn), 0);\n",
        "}\n\n",
    ));

    // uw_db_commit
    out.push_str(concat!(
        "static int uw_db_commit(uw_context ctx) {\n",
        "uw_conn *conn = uw_get_db(ctx);\n",
        "return mysql_commit(conn->conn);\n",
        "}\n\n",
    ));

    // uw_db_rollback
    out.push_str(concat!(
        "static int uw_db_rollback(uw_context ctx) {\n",
        "uw_conn *conn = uw_get_db(ctx);\n",
        "return mysql_rollback(conn->conn);\n",
        "}\n\n",
    ));

    out
}

fn gen_postgres_c_code(
    dbstring: &str,
    _tables: &[(String, Vec<(String, LocTyp)>)],
    prepared: &[(String, usize)],
) -> String {
    let mut out = String::new();

    out.push_str("#include <libpq-fe.h>\n\n");

    // strcmp_nullsafe helper (used by uw_db_commit/rollback for SQLSTATE checks)
    out.push_str(concat!(
        "static int strcmp_nullsafe(const char *a, const char *b) {\n",
        "if (a == NULL || b == NULL) return 1;\n",
        "return strcmp(a, b);\n",
        "}\n\n",
    ));

    // uw_client_init
    out.push_str(concat!(
        "static void uw_client_init(void) {\n",
        "uw_sqlfmtInt = \"%lld::int8%n\";\n",
        "uw_sqlfmtFloat = \"%.16g::float8%n\";\n",
        "uw_Estrings = 1;\n",
        "uw_sql_type_annotations = 1;\n",
        "uw_sqlsuffixString = \"::text\";\n",
        "uw_sqlsuffixChar = \"::char\";\n",
        "uw_sqlsuffixBlob = \"::bytea\";\n",
        "uw_sqlfmtUint4 = \"%u::int4%n\";\n",
        "}\n\n",
    ));

    // uw_db_validate (stub — full Postgres table-checking is complex; matches non-persistent path)
    out.push_str("static void uw_db_validate(uw_context ctx) { }\n\n");

    // uw_db_prepare
    if !prepared.is_empty() {
        out.push_str("static void uw_db_prepare(uw_context ctx) {\n");
        out.push_str("PGconn *conn = uw_get_db(ctx);\n");
        out.push_str("PGresult *res;\n\n");
        for (i, (sql, _)) in prepared.iter().enumerate() {
            let escaped = sql.replace('\\', "\\\\").replace('"', "\\\"");
            out.push_str(&format!(
                "res = PQprepare(conn, \"uw{i}\", \"{escaped}\", 0, NULL);\n"
            ));
            out.push_str("if (PQresultStatus(res) != PGRES_COMMAND_OK) {\n");
            out.push_str("char msg[1024];\n");
            out.push_str("strncpy(msg, PQerrorMessage(conn), 1024);\n");
            out.push_str("msg[1023] = 0;\n");
            out.push_str("PQclear(res);\n");
            out.push_str("PQfinish(conn);\n");
            out.push_str(&format!(
                "uw_error(ctx, FATAL, \"Unable to create prepared statement:\\n{escaped}\\n%s\", msg);\n"
            ));
            out.push_str("}\n");
            out.push_str("PQclear(res);\n");
        }
        out.push_str("}\n\n");
    } else {
        out.push_str("static void uw_db_prepare(uw_context ctx) { }\n\n");
    }

    // uw_db_close
    out.push_str(concat!(
        "static void uw_db_close(uw_context ctx) {\n",
        "PQfinish(uw_get_db(ctx));\n",
        "}\n\n",
    ));

    // uw_db_begin
    out.push_str(concat!(
        "static int uw_db_begin(uw_context ctx, int could_write) {\n",
        "PGconn *conn = uw_get_db(ctx);\n",
        "PGresult *res = PQexec(conn, could_write ? \"BEGIN ISOLATION LEVEL SERIALIZABLE\" : \"BEGIN ISOLATION LEVEL SERIALIZABLE, READ ONLY\");\n\n",
        "if (res == NULL) return 1;\n\n",
        "if (PQresultStatus(res) != PGRES_COMMAND_OK) {\n",
        "PQclear(res);\n",
        "return 1;\n",
        "}\n",
        "PQclear(res);\n",
        "return 0;\n",
        "}\n\n",
    ));

    // uw_db_commit
    out.push_str(concat!(
        "static int uw_db_commit(uw_context ctx) {\n",
        "PGconn *conn = uw_get_db(ctx);\n",
        "PGresult *res = PQexec(conn, \"COMMIT\");\n\n",
        "if (res == NULL) return 1;\n\n",
        "if (PQresultStatus(res) != PGRES_COMMAND_OK) {\n",
        "if (!strcmp_nullsafe(PQresultErrorField(res, PG_DIAG_SQLSTATE), \"40001\")) {\n",
        "PQclear(res);\n",
        "return -1;\n",
        "}\n",
        "if (!strcmp_nullsafe(PQresultErrorField(res, PG_DIAG_SQLSTATE), \"40P01\")) {\n",
        "PQclear(res);\n",
        "return -1;\n",
        "}\n",
        "PQclear(res);\n",
        "return 1;\n",
        "}\n",
        "PQclear(res);\n",
        "return 0;\n",
        "}\n\n",
    ));

    // uw_db_rollback
    out.push_str(concat!(
        "static int uw_db_rollback(uw_context ctx) {\n",
        "PGconn *conn = uw_get_db(ctx);\n",
        "PGresult *res = PQexec(conn, \"ROLLBACK\");\n\n",
        "if (res == NULL) return 1;\n\n",
        "if (PQresultStatus(res) != PGRES_COMMAND_OK) {\n",
        "PQclear(res);\n",
        "return 1;\n",
        "}\n",
        "PQclear(res);\n",
        "return 0;\n",
        "}\n\n",
    ));

    // uw_db_init
    let escaped_ds = dbstring.replace('\\', "\\\\").replace('"', "\\\"");
    out.push_str("static void uw_db_init(uw_context ctx) {\n");
    out.push_str("char *env_db_str = getenv(\"URWEB_PQ_CON\");\n");
    out.push_str(&format!(
        "PGconn *conn = PQconnectdb(env_db_str == NULL ? \"{escaped_ds}\" : env_db_str);\n"
    ));
    out.push_str(
        "if (conn == NULL) uw_error(ctx, FATAL, \"libpq can't allocate a connection.\");\n",
    );
    out.push_str("if (PQstatus(conn) != CONNECTION_OK) {\n");
    out.push_str("char msg[1024];\n");
    out.push_str("strncpy(msg, PQerrorMessage(conn), 1024);\n");
    out.push_str("msg[1023] = 0;\n");
    out.push_str("PQfinish(conn);\n");
    out.push_str(
        "uw_error(ctx, BOUNDED_RETRY, \"Connection to Postgres server failed: %s\", msg);\n",
    );
    out.push_str("}\n");
    out.push_str("uw_set_db(ctx, conn);\n");
    out.push_str("uw_db_validate(ctx);\n");
    out.push_str("uw_db_prepare(ctx);\n");
    out.push_str("}\n\n");

    out
}
