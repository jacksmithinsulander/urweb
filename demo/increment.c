#include "urweb.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#include <sqlite3.h>

static void uw_client_init(void) {
uw_sqlfmtInt = "%lld%n";
uw_sqlfmtFloat = "%.16g%n";
uw_Estrings = 0;
uw_sql_type_annotations = 0;
uw_sqlsuffixString = "";
uw_sqlsuffixChar = "";
uw_sqlsuffixBlob = "";
uw_sqlfmtUint4 = "%u%n";
}

typedef struct {
sqlite3 *conn;
sqlite3_stmt *p0;
} uw_conn;

static void uw_db_validate(uw_context ctx) {
}

static void uw_db_prepare(uw_context ctx) {
uw_conn *conn = uw_get_db(ctx);

{ int _pr;
do { _pr = sqlite3_prepare_v2(conn->conn, "SELECT NEXTVAL('uw_Increment_seq')", -1, &conn->p0, NULL); if (_pr == SQLITE_BUSY) sleep(1); } while (_pr == SQLITE_BUSY);
if (_pr != SQLITE_OK) {
char msg[1024];
strncpy(msg, sqlite3_errmsg(conn->conn), 1024);
msg[1023] = 0;
sqlite3_finalize(conn->p0);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Error preparing statement: SELECT NEXTVAL('uw_Increment_seq')<br />%s", msg);
}
}
}

static void uw_db_init(uw_context ctx) {
sqlite3 *sqlite;
sqlite3_stmt *stmt;
uw_conn *conn;

if (sqlite3_open("/tmp/increment.db", &sqlite) != SQLITE_OK) uw_error(ctx, FATAL, "Can't open SQLite database.");

if (sqlite3_exec(sqlite, "PRAGMA foreign_keys = ON", NULL, NULL, NULL) != SQLITE_OK)
uw_error(ctx, FATAL, "Can't enable foreign_keys for SQLite database");

if (uw_database_max < SIZE_MAX) {
char buf[100];

sprintf(buf, "PRAGMA max_page_count = %llu", (unsigned long long)(uw_database_max / 1024));

if (sqlite3_prepare_v2(sqlite, buf, -1, &stmt, NULL) != SQLITE_OK) {
sqlite3_close(sqlite);
uw_error(ctx, FATAL, "Can't prepare max_page_count query for SQLite database");
}

if (sqlite3_step(stmt) != SQLITE_ROW) {
sqlite3_finalize(stmt);
sqlite3_close(sqlite);
uw_error(ctx, FATAL, "Can't set max_page_count parameter for SQLite database");
}

sqlite3_finalize(stmt);
}

conn = calloc(1, sizeof(uw_conn));
conn->conn = sqlite;
uw_set_db(ctx, conn);
uw_db_validate(ctx);
uw_db_prepare(ctx);
}

static void uw_db_close(uw_context ctx) {
uw_conn *conn = uw_get_db(ctx);
if (conn->p0) sqlite3_finalize(conn->p0);
sqlite3_close(conn->conn);
}

static int uw_db_begin(uw_context ctx, int could_write) {
uw_conn *conn = uw_get_db(ctx);

if (sqlite3_exec(conn->conn, "BEGIN", NULL, NULL, NULL) == SQLITE_OK)
return 0;
else {
fprintf(stderr, "Begin error: %s<br />", sqlite3_errmsg(conn->conn));
return 1;
}
}
static int uw_db_commit(uw_context ctx) {
uw_conn *conn = uw_get_db(ctx);
if (sqlite3_exec(conn->conn, "COMMIT", NULL, NULL, NULL) == SQLITE_OK)
return 0;
else {
fprintf(stderr, "Commit error: %s<br />", sqlite3_errmsg(conn->conn));
return 1;
}
}

static int uw_db_rollback(uw_context ctx) {
uw_conn *conn = uw_get_db(ctx);
if (sqlite3_exec(conn->conn, "ROLLBACK", NULL, NULL, NULL) == SQLITE_OK)
return 0;
else {
fprintf(stderr, "Rollback error: %s<br />", sqlite3_errmsg(conn->conn));
return 1;
}
}

static int uw_input_num(const char *name) { return -1; }

extern void uw_sign(const char *in, char *out);
extern int uw_hash_blocksize;
static uw_Basis_string uw_cookie_sig(uw_context ctx) {
    uw_Basis_string r = uw_malloc(ctx, uw_hash_blocksize);
    uw_sign("", r);
    return uw_Basis_makeSigString(ctx, r);
}

static inline uw_Basis_string uw_Basis_attrOptional(
    struct uw_context *ctx, uw_Basis_string name, uw_Basis_string val) {
    if (val == NULL || val[0] == '\0') return "";
    return uw_Basis_mstrcat(ctx, " ", name, "=\"", val, "\"", NULL);
}

/* Function prototypes */
static uw_unit __uwn_expunger_1760(uw_context, uw_Basis_client);
static uw_unit __uwn_initializer_1761(uw_context, uw_unit);
static uw_Basis_int __uwn_increment_1757(uw_context, uw_unit, uw_unit);
static uw_unit __uwn_wrap_main_1759(uw_context, uw_unit, uw_unit);

static uw_unit __uwn_expunger_1760(uw_context ctx, uw_Basis_client __uwr_cli_0) {
return(0);
}

static uw_unit __uwn_initializer_1761(uw_context ctx, uw_unit __uwr___0) {
return(0);
}

#line 1 "/Users/jacksmith/prog/urweb/demo/increment.ur"
/* SQL sequence uw_Increment_seq */

#line 3 "/Users/jacksmith/prog/urweb/demo/increment.ur"
static uw_Basis_int __uwn_increment_1757(uw_context ctx, uw_unit __uwr__arg_0, uw_unit __uwr___1) {
return(({
uw_Basis_int n;
uw_ensure_transaction(ctx);
PGconn *conn = uw_get_db(ctx);
PGresult *res = PQexecParams(conn, "SELECT NEXTVAL('uw_Increment_seq')", 0, NULL, NULL, NULL, NULL, 0);
if (res == NULL) {
uw_try_reconnecting_and_restarting(ctx);
uw_error(ctx, FATAL, "Ur/Web / SQL: could not run NEXTVAL (out of memory or database unreachable).");
}
if (PQresultStatus(res) != PGRES_TUPLES_OK) {
PQclear(res);
uw_error(ctx, FATAL, "Ur/Web / SQL: NEXTVAL failed.\nSQL: %s\nServer: %s", "SELECT NEXTVAL('uw_Increment_seq')", PQerrorMessage(conn));
}
n = PQntuples(res);
if (n != 1) {
PQclear(res);
uw_error(ctx, FATAL, "Ur/Web / SQL: NEXTVAL returned the wrong row count (expected 1, got %d).\nSQL: %s\nServer: %s", n, "SELECT NEXTVAL('uw_Increment_seq')", PQerrorMessage(conn));
}
n = uw_Basis_stringToInt_error(ctx, PQgetvalue(res, 0, 0));
PQclear(res);
n;
}));
}

static uw_unit __uwn_wrap_main_1759(uw_context ctx, uw_unit __uwr_x0_0, uw_unit __uwr___1) {
return(({
uw_Basis_source __uwr_r_2 = uw_Basis_source(ctx, 0LL, 0);
((uw_write(ctx, "<body"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">\n<dyn"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></dyn>\n<button"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), (uw_write(ctx, "></button>\n</body>"), 0))))))))));
}));
}

static void uw_setup_limits(void) {
}

void uw_global_custom(void) {
uw_setup_limits();
}

static void uw_initializer(uw_context ctx) {
uw_begin_initializing(ctx);
uw_end_initializing(ctx);
__uwn_initializer_1761(ctx, 0);
}

static void uw_expunger(uw_context ctx, uw_Basis_client cli) {
__uwn_expunger_1760(ctx, cli);
}

static uw_periodic my_periodics[] = {
  { NULL, 0 }
};

static int uw_check_url(const char *url) {
  return 1;
}

static int uw_check_mime(const char *mime) {
  return 1;
}

static int uw_check_requestHeader(const char *h) {
  return 1;
}

static int uw_check_responseHeader(const char *h) {
  return 1;
}

static int uw_check_envVar(const char *v) {
  return 1;
}

static int uw_check_meta(const char *m) {
  return 1;
}

static void uw_handle(uw_context ctx, char *request) {
if (!strncmp(request, "/Increment/increment", 20) && (request[20] == 0 || request[20] == '/')) {
request += 20;
if (*request == '/') ++request;
if (uw_hasPostBody(ctx)) {
uw_Basis_postBody pb = uw_getPostBody(ctx);
if (pb.data[0])
request = uw_Basis_strcat(ctx, request, pb.data);
}
{
uw_Basis_string sig = uw_Basis_requestHeader(ctx, "UrWeb-Sig");
if (sig == NULL) uw_error(ctx, FATAL, "Ur/Web security: missing UrWeb-Sig header (CSRF token). Resubmit the form from this app, or open a fresh page.");
if (!uw_streq(sig, uw_cookie_sig(ctx)))
uw_error(ctx, FATAL, "Ur/Web security: UrWeb-Sig does not match this session (possible CSRF, stale tab, or outdated form).");
}
uw_write_header(ctx, "Content-type: text/plain\r\n");
uw_set_could_write_db(ctx, 1);
uw_set_at_most_one_query(ctx, 0);
uw_set_needs_push(ctx, 0);
uw_set_needs_sig(ctx, 0);
uw_login(ctx);
{
uw_unit arg0 = uw_Basis_unurlifyUnit(ctx, &request);
uw_Basis_int it0 = __uwn_increment_1757(ctx, arg0, 0);
uw_write(ctx, uw_get_real_script(ctx));
uw_write(ctx, "\n");
uw_Basis_urlifyInt_w(ctx, it0);
return;
}
}
if (!strncmp(request, "/Increment/main", 15) && (request[15] == 0 || request[15] == '/')) {
request += 15;
if (*request == '/') ++request;
uw_write_header(ctx, "Content-type: text/html; charset=utf-8\r\n");
uw_write(ctx, uw_begin_html5);
uw_mayReturnIndirectly(ctx);
uw_set_could_write_db(ctx, 0);
uw_set_at_most_one_query(ctx, 0);
uw_set_needs_push(ctx, 0);
uw_set_needs_sig(ctx, 0);
uw_login(ctx);
{
uw_unit arg0 = uw_Basis_unurlifyUnit(ctx, &request);
__uwn_wrap_main_1759(ctx, arg0, 0);
uw_write(ctx, "</html>");
return;
}
}
uw_clear_headers(ctx);
uw_write_header(ctx, uw_supports_direct_status ? "HTTP/1.1 404 Not Found\r\n" : "Status: 404 Not Found\r\n");
uw_write_header(ctx, "Content-type: text/plain\r\n");
uw_write(ctx, "Not Found");
}

uw_app uw_application = {
1,
120,
"/",
uw_client_init,
uw_initializer,
uw_expunger,
uw_db_init, uw_db_begin, uw_db_commit, uw_db_rollback, uw_db_close,
uw_handle,
uw_input_num,
uw_cookie_sig,
uw_check_url, uw_check_mime, uw_check_requestHeader, uw_check_responseHeader,
uw_check_envVar, uw_check_meta,
NULL,
my_periodics,
"%c",
1,
NULL
};
