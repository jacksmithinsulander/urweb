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
} uw_conn;

static void uw_db_validate(uw_context ctx) {
uw_conn *conn = uw_get_db(ctx);
sqlite3_stmt *stmt;
int res;
{ int _prepare_rc;
do { _prepare_rc = sqlite3_prepare_v2(conn->conn, "SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Tree_t'", -1, &stmt, NULL); if (_prepare_rc == SQLITE_BUSY) sleep(1); } while (_prepare_rc == SQLITE_BUSY);
if (_prepare_rc != SQLITE_OK) {
char _sqlerrmsg[1024];
strncpy(_sqlerrmsg, sqlite3_errmsg(conn->conn), sizeof(_sqlerrmsg)-1);
_sqlerrmsg[sizeof(_sqlerrmsg)-1] = 0;
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Query preparation failed (%s):<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Tree_t'", _sqlerrmsg); }
}
while ((res = sqlite3_step(stmt)) == SQLITE_BUSY)
sleep(1);
if (res == SQLITE_DONE) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "No row returned:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Tree_t'");
}
if (res != SQLITE_ROW) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Error getting row:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Tree_t'");
}
if (sqlite3_column_count(stmt) != 1) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Bad column count:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Tree_t'");
}
if (sqlite3_column_int(stmt, 0) != 1) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Table 'uw_Tree_t' does not exist.");
}
sqlite3_finalize(stmt);
}

static void uw_db_prepare(uw_context ctx) { }

static void uw_db_init(uw_context ctx) {
sqlite3 *sqlite;
sqlite3_stmt *stmt;
uw_conn *conn;

if (sqlite3_open("/tmp/tree-debug.db", &sqlite) != SQLITE_OK) uw_error(ctx, FATAL, "Can't open SQLite database.");

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

struct __uws_1 {
uw_Basis_int __uwf_Id;
uw_Basis_string __uwf_Nam;
uw_Basis_int* __uwf_Parent;
};

struct __uws_2 {
struct __uws_1 __uwf_Tab;
};

/* Function prototypes */
static uw_unit __uwn_lam_1843_1843(uw_context, uw_Basis_client);
static uw_unit __uwn_expunger_1840(uw_context, uw_Basis_client);
static uw_unit __uwn_initializer_1841(uw_context, uw_unit);
static uw_Basis_string __uwn_lam_1844_1844(uw_context, uw_Basis_int*, uw_unit, uw_unit);
static uw_Basis_string __uwn__recurse_1839(uw_context, uw_Basis_int*, uw_unit);
static uw_Basis_string __uwn_lam_1845_1845(uw_context, struct __uws_1);
static uw_unit __uwn_lam_1846_1846(uw_context, struct __uws_1);
static uw_Basis_string __uwn_row_1832(uw_context, struct __uws_1);
static uw_unit __uwn_row_1842(uw_context, struct __uws_1);
static uw_unit __uwn_wrap_main_1836(uw_context, uw_unit, uw_unit);

static char jslib[] = "";

static uw_unit __uwn_lam_1843_1843(uw_context ctx, uw_Basis_client __uwr_cli_0) {
return(0);
}

static uw_unit __uwn_expunger_1840(uw_context ctx, uw_Basis_client __uwr_x_0) {
return(__uwn_lam_1843_1843(ctx, __uwr_x_0));
}

static uw_unit __uwn_initializer_1841(uw_context ctx, uw_unit __uwr___0) {
return(0);
}

#line 1 "/Users/jacksmith/prog/urweb/demo/tree.ur"
/* SQL sequence uw_Tree_s */

#line 2 "/Users/jacksmith/prog/urweb/demo/tree.ur"
/* SQL table uw_Tree_t uw_Id constraints F: FOREIGN KEY (uw_parent) REFERENCES uw_Tree_t (uw_id) ON DELETE CASCADE */

#line 2 "/Users/jacksmith/prog/urweb/demo/tree.ur"
uw_Basis_string __uwn_t_1793;

static uw_Basis_string __uwn_lam_1844_1844(uw_context ctx, uw_Basis_int* __uwr_root_0, uw_unit __uwr___1, uw_unit __uwr___2) {
return((({
uw_Basis_string acc = "";
int dummy = (uw_begin_region(ctx), 0);
uw_ensure_transaction(ctx);
char *query = uw_Basis_mstrcat(ctx, "SELECT T_Tab.uw_id, T_Tab.uw_nam, T_Tab.uw_parent FROM uw_Tree_t AS T_Tab", ({
uw_Basis_string disc = ({
uw_Basis_int* disc = __uwr_root_0;

(disc == NULL) ? "(T_Tab.uw_parent IS NULL)" : (disc != NULL) && 1 ? ({
uw_Basis_int __uwr___3 = (*disc);
uw_Basis_mstrcat(ctx, "(T_Tab.uw_parent = ", ({
uw_Basis_int* disc = __uwr_root_0;

(disc == NULL) ? "NULL" : (disc != NULL) && 1 ? ({
uw_Basis_int __uwr_y_4 = (*disc);
uw_Basis_sqlifyInt(ctx, __uwr_y_4);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}), ")", NULL);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
});

(!strcmp(disc, "1")) ? "" : 1 ? ({
uw_Basis_string __uwr_frag_3 = disc;
uw_Basis_strcat(ctx, " WHERE ", __uwr_frag_3);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}), " HAVING TRUE", ({
uw_Basis_string disc = "";

(!strcmp(disc, "")) ? "" : 1 ? ({
uw_Basis_string __uwr_orderby_3 = disc;
uw_Basis_strcat(ctx, " ORDER BY ", __uwr_orderby_3);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}), NULL);
uw_conn *conn = uw_get_db(ctx);
sqlite3_stmt *stmt;
if (sqlite3_prepare_v2(conn->conn, query, -1, &stmt, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "Error preparing statement: %s<br />%s", query, sqlite3_errmsg(conn->conn));
uw_push_cleanup(ctx, (void (*)(void *))sqlite3_finalize, stmt);
int r;
sqlite3_reset(stmt);
uw_end_region(ctx);
while ((r = sqlite3_step(stmt)) == SQLITE_ROW) {
struct __uws_2 __uwr_r_3;
uw_Basis_string __uwr_acc_4 = acc;

__uwr_r_3.__uwf_Tab.__uwf_Id = (sqlite3_column_type(stmt, 0) == SQLITE_NULL ? ({ uw_Basis_int tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #0"); tmp; }) : sqlite3_column_int64(stmt, 0));
__uwr_r_3.__uwf_Tab.__uwf_Nam = (sqlite3_column_type(stmt, 1) == SQLITE_NULL ? ({ uw_Basis_string tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #1"); tmp; }) : uw_strdup(ctx, (uw_Basis_string)sqlite3_column_text(stmt, 1)));
__uwr_r_3.__uwf_Tab.__uwf_Parent = (sqlite3_column_type(stmt, 2) == SQLITE_NULL ? NULL : ({
uw_Basis_int *tmp = uw_malloc(ctx, sizeof(uw_Basis_int));
*tmp = sqlite3_column_int64(stmt, 2);
tmp;
}));

acc = ({
uw_Basis_string __uwr_r_5 = ({
uw_Basis_int* arg0 = ({
uw_Basis_int *tmp = uw_malloc(ctx, sizeof(uw_Basis_int));
*tmp = __uwr_r_3.__uwf_Tab.__uwf_Id;
tmp;
});
uw_unit arg1 = 0;
__uwn__recurse_1839(ctx, arg0, arg1);
});
uw_Basis_mstrcat(ctx, __uwr_acc_4, "\n<li", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "> ", __uwn_row_1832(ctx, __uwr_r_3.__uwf_Tab), "</li>\n<ul", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">\n", __uwr_r_5, "\n</ul>\n", NULL);
});
}
if (r == SQLITE_BUSY) {
sleep(1);
uw_error(ctx, UNLIMITED_RETRY, "Database is busy");
}
if (r != SQLITE_DONE) uw_error(ctx, FATAL, "query: query step failed: %s<br />%s", query, sqlite3_errmsg(conn->conn));
uw_pop_cleanup(ctx);
acc;
})));
}

static uw_Basis_string __uwn__recurse_1839(uw_context, uw_Basis_int*, uw_unit);

static uw_Basis_string __uwn__recurse_1839(uw_context ctx, uw_Basis_int* __uwr_x_0, uw_unit __uwr___1) {
restart:
return(({
uw_Basis_int* arg0 = __uwr_x_0;
uw_unit arg1 = __uwr___1;
uw_unit arg2 = 0;
__uwn_lam_1844_1844(ctx, arg0, arg1, arg2);
}));
}


#line 12 "/Users/jacksmith/prog/urweb/demo/tree.ur"
static uw_Basis_string __uwn_lam_1845_1845(uw_context ctx, struct __uws_1 __uwr_r_0) {
return(uw_Basis_mstrcat(ctx, "\n#", uw_Basis_htmlifyInt(ctx, __uwr_r_0.__uwf_Id), ": ", uw_Basis_htmlifyString(ctx, __uwr_r_0.__uwf_Nam), " <form method=\"post\"><input type=\"submit\"", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), " value=\"Delete\" /></form>\n<form method=\"post\">\nAdd child: <div", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "></div> <input type=\"submit\"", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), " />\n</form>\n", NULL));
}

static uw_unit __uwn_lam_1846_1846(uw_context ctx, struct __uws_1 __uwr_r_0) {
return(((uw_write(ctx, "\n#"), 0), (uw_Basis_htmlifyInt_w(ctx, __uwr_r_0.__uwf_Id), ((uw_write(ctx, ": "), 0), (uw_Basis_htmlifyString_w(ctx, __uwr_r_0.__uwf_Nam), ((uw_write(ctx, " <form method=\"post\"><input type=\"submit\""), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, " value=\"Delete\" /></form>\n<form method=\"post\">\nAdd child: <div"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></div> <input type=\"submit\""), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), (uw_write(ctx, " />\n</form>\n"), 0)))))))))))))));
}

static uw_Basis_string __uwn_row_1832(uw_context, struct __uws_1);
static uw_unit __uwn_row_1842(uw_context, struct __uws_1);

static uw_Basis_string __uwn_row_1832(uw_context ctx, struct __uws_1 __uwr_x_0) {
restart:
return(__uwn_lam_1845_1845(ctx, __uwr_x_0));
}
static uw_unit __uwn_row_1842(uw_context ctx, struct __uws_1 __uwr_x_0) {
restart:
return(__uwn_lam_1846_1846(ctx, __uwr_x_0));
}


static uw_unit __uwn_wrap_main_1836(uw_context ctx, uw_unit __uwr_x0_0, uw_unit __uwr___1) {
return(({
uw_Basis_string __uwr_r_2 = (({
uw_Basis_string acc = "";
int dummy = (uw_begin_region(ctx), 0);
uw_ensure_transaction(ctx);
char *query = uw_Basis_strcat(ctx, "SELECT T_Tab.uw_id, T_Tab.uw_nam, T_Tab.uw_parent FROM uw_Tree_t AS T_Tab WHERE (T_Tab.uw_parent IS NULL) HAVING TRUE", ({
uw_Basis_string disc = "";

(!strcmp(disc, "")) ? "" : 1 ? ({
uw_Basis_string __uwr_orderby_2 = disc;
uw_Basis_strcat(ctx, " ORDER BY ", __uwr_orderby_2);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}));
uw_conn *conn = uw_get_db(ctx);
sqlite3_stmt *stmt;
if (sqlite3_prepare_v2(conn->conn, query, -1, &stmt, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "Error preparing statement: %s<br />%s", query, sqlite3_errmsg(conn->conn));
uw_push_cleanup(ctx, (void (*)(void *))sqlite3_finalize, stmt);
int r;
sqlite3_reset(stmt);
uw_end_region(ctx);
while ((r = sqlite3_step(stmt)) == SQLITE_ROW) {
struct __uws_2 __uwr_r_2;
uw_Basis_string __uwr_acc_3 = acc;

__uwr_r_2.__uwf_Tab.__uwf_Id = (sqlite3_column_type(stmt, 0) == SQLITE_NULL ? ({ uw_Basis_int tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #0"); tmp; }) : sqlite3_column_int64(stmt, 0));
__uwr_r_2.__uwf_Tab.__uwf_Nam = (sqlite3_column_type(stmt, 1) == SQLITE_NULL ? ({ uw_Basis_string tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #1"); tmp; }) : uw_strdup(ctx, (uw_Basis_string)sqlite3_column_text(stmt, 1)));
__uwr_r_2.__uwf_Tab.__uwf_Parent = (sqlite3_column_type(stmt, 2) == SQLITE_NULL ? NULL : ({
uw_Basis_int *tmp = uw_malloc(ctx, sizeof(uw_Basis_int));
*tmp = sqlite3_column_int64(stmt, 2);
tmp;
}));

acc = ({
uw_Basis_string __uwr_r_4 = ({
uw_Basis_int* arg0 = ({
uw_Basis_int *tmp = uw_malloc(ctx, sizeof(uw_Basis_int));
*tmp = __uwr_r_2.__uwf_Tab.__uwf_Id;
tmp;
});
uw_unit arg1 = 0;
__uwn__recurse_1839(ctx, arg0, arg1);
});
uw_Basis_mstrcat(ctx, __uwr_acc_3, "\n<li", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "> #", uw_Basis_htmlifyInt(ctx, __uwr_r_2.__uwf_Tab.__uwf_Id), ": ", uw_Basis_htmlifyString(ctx, __uwr_r_2.__uwf_Tab.__uwf_Nam), " <form method=\"post\"><input type=\"submit\"", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), " value=\"Delete\" /></form>\n<form method=\"post\">\nAdd child: <div", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "></div> <input type=\"submit\"", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), " />\n</form>\n</li>\n<ul", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">\n", __uwr_r_4, "\n</ul>\n", NULL);
});
}
if (r == SQLITE_BUSY) {
sleep(1);
uw_error(ctx, UNLIMITED_RETRY, "Database is busy");
}
if (r != SQLITE_DONE) uw_error(ctx, FATAL, "query: query step failed: %s<br />%s", query, sqlite3_errmsg(conn->conn));
uw_pop_cleanup(ctx);
acc;
}));
(uw_write(ctx, uw_Basis_mstrcat(ctx, "<body", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">\n", __uwr_r_2, "\n<form method=\"post\">\nAdd a top-level node: <div", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "></div> <input type=\"submit\"", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), " />\n</form>\n</body>", NULL)), 0);
}));
}

static void uw_setup_limits(void) {
}

void uw_global_custom(void) {
uw_setup_limits();
}

static void uw_initializer(uw_context ctx) {
uw_begin_initializing(ctx);
__uwn_t_1793 = "uw_Tree_t";
uw_end_initializing(ctx);
__uwn_initializer_1841(ctx, 0);
}

static void uw_expunger(uw_context ctx, uw_Basis_client cli) {
__uwn_expunger_1840(ctx, cli);
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
if (!strncmp(request, "/Tree/main", 10) && (request[10] == 0 || request[10] == '/')) {
request += 10;
if (*request == '/') ++request;
uw_write_header(ctx, "Content-type: text/html; charset=utf-8\r\n");
uw_write(ctx, uw_begin_html5);
uw_mayReturnIndirectly(ctx);
uw_set_could_write_db(ctx, 1);
uw_set_at_most_one_query(ctx, 1);
uw_set_needs_push(ctx, 0);
uw_set_needs_sig(ctx, 0);
uw_login(ctx);
{
uw_unit arg0 = uw_Basis_unurlifyUnit(ctx, &request);
__uwn_wrap_main_1836(ctx, arg0, 0);
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
