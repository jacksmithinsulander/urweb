#include "urweb.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#include <libpq-fe.h>

static int strcmp_nullsafe(const char *a, const char *b) {
if (a == NULL || b == NULL) return 1;
return strcmp(a, b);
}

static void uw_client_init(void) {
uw_sqlfmtInt = "%lld::int8%n";
uw_sqlfmtFloat = "%.16g::float8%n";
uw_Estrings = 1;
uw_sql_type_annotations = 1;
uw_sqlsuffixString = "::text";
uw_sqlsuffixChar = "::char";
uw_sqlsuffixBlob = "::bytea";
uw_sqlfmtUint4 = "%u::int4%n";
}

static void uw_db_validate(uw_context ctx) { }

static void uw_db_prepare(uw_context ctx) { }

static void uw_db_close(uw_context ctx) {
PQfinish(uw_get_db(ctx));
}

static int uw_db_begin(uw_context ctx, int could_write) {
PGconn *conn = uw_get_db(ctx);
PGresult *res = PQexec(conn, could_write ? "BEGIN ISOLATION LEVEL SERIALIZABLE" : "BEGIN ISOLATION LEVEL SERIALIZABLE, READ ONLY");

if (res == NULL) return 1;

if (PQresultStatus(res) != PGRES_COMMAND_OK) {
PQclear(res);
return 1;
}
PQclear(res);
return 0;
}

static int uw_db_commit(uw_context ctx) {
PGconn *conn = uw_get_db(ctx);
PGresult *res = PQexec(conn, "COMMIT");

if (res == NULL) return 1;

if (PQresultStatus(res) != PGRES_COMMAND_OK) {
if (!strcmp_nullsafe(PQresultErrorField(res, PG_DIAG_SQLSTATE), "40001")) {
PQclear(res);
return -1;
}
if (!strcmp_nullsafe(PQresultErrorField(res, PG_DIAG_SQLSTATE), "40P01")) {
PQclear(res);
return -1;
}
PQclear(res);
return 1;
}
PQclear(res);
return 0;
}

static int uw_db_rollback(uw_context ctx) {
PGconn *conn = uw_get_db(ctx);
PGresult *res = PQexec(conn, "ROLLBACK");

if (res == NULL) return 1;

if (PQresultStatus(res) != PGRES_COMMAND_OK) {
PQclear(res);
return 1;
}
PQclear(res);
return 0;
}

static void uw_db_init(uw_context ctx) {
char *env_db_str = getenv("URWEB_PQ_CON");
PGconn *conn = PQconnectdb(env_db_str == NULL ? "" : env_db_str);
if (conn == NULL) uw_error(ctx, FATAL, "libpq can't allocate a connection.");
if (PQstatus(conn) != CONNECTION_OK) {
char msg[1024];
strncpy(msg, PQerrorMessage(conn), 1024);
msg[1023] = 0;
PQfinish(conn);
uw_error(ctx, BOUNDED_RETRY, "Connection to Postgres server failed: %s", msg);
}
uw_set_db(ctx, conn);
uw_db_validate(ctx);
uw_db_prepare(ctx);
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

static char jslib[] = "";

static void uw_setup_limits(void) {
}

void uw_global_custom(void) {
uw_setup_limits();
}

static void uw_initializer(uw_context ctx) {
uw_begin_initializing(ctx);
uw_end_initializing(ctx);
}

static void uw_expunger(uw_context ctx, uw_Basis_client cli) {
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
