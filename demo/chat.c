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
do { _prepare_rc = sqlite3_prepare_v2(conn->conn, "SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Chat_Room_t'", -1, &stmt, NULL); if (_prepare_rc == SQLITE_BUSY) sleep(1); } while (_prepare_rc == SQLITE_BUSY);
if (_prepare_rc != SQLITE_OK) {
char _sqlerrmsg[1024];
strncpy(_sqlerrmsg, sqlite3_errmsg(conn->conn), sizeof(_sqlerrmsg)-1);
_sqlerrmsg[sizeof(_sqlerrmsg)-1] = 0;
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Query preparation failed (%s):<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Chat_Room_t'", _sqlerrmsg); }
}
while ((res = sqlite3_step(stmt)) == SQLITE_BUSY)
sleep(1);
if (res == SQLITE_DONE) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "No row returned:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Chat_Room_t'");
}
if (res != SQLITE_ROW) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Error getting row:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Chat_Room_t'");
}
if (sqlite3_column_count(stmt) != 1) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Bad column count:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Chat_Room_t'");
}
if (sqlite3_column_int(stmt, 0) != 1) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Table 'uw_Chat_Room_t' does not exist.");
}
sqlite3_finalize(stmt);
{ int _prepare_rc;
do { _prepare_rc = sqlite3_prepare_v2(conn->conn, "SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Chat_t'", -1, &stmt, NULL); if (_prepare_rc == SQLITE_BUSY) sleep(1); } while (_prepare_rc == SQLITE_BUSY);
if (_prepare_rc != SQLITE_OK) {
char _sqlerrmsg[1024];
strncpy(_sqlerrmsg, sqlite3_errmsg(conn->conn), sizeof(_sqlerrmsg)-1);
_sqlerrmsg[sizeof(_sqlerrmsg)-1] = 0;
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Query preparation failed (%s):<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Chat_t'", _sqlerrmsg); }
}
while ((res = sqlite3_step(stmt)) == SQLITE_BUSY)
sleep(1);
if (res == SQLITE_DONE) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "No row returned:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Chat_t'");
}
if (res != SQLITE_ROW) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Error getting row:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Chat_t'");
}
if (sqlite3_column_count(stmt) != 1) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Bad column count:<br />SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = 'uw_Chat_t'");
}
if (sqlite3_column_int(stmt, 0) != 1) {
sqlite3_finalize(stmt);
sqlite3_close(conn->conn);
uw_error(ctx, FATAL, "Table 'uw_Chat_t' does not exist.");
}
sqlite3_finalize(stmt);
}

static void uw_db_prepare(uw_context ctx) { }

static void uw_db_init(uw_context ctx) {
sqlite3 *sqlite;
sqlite3_stmt *stmt;
uw_conn *conn;

if (sqlite3_open("/tmp/urweb-chat-boot.db", &sqlite) != SQLITE_OK) uw_error(ctx, FATAL, "Can't open SQLite database.");

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

struct __uws_2 {
struct __uws_1 __uwf_T;
};

struct __uws_3 {
uw_unit __uwf_T;
};

struct __uws_4 {
uw_Basis_int __uwf_Id;
uw_Basis_string __uwf_Title;
uw_Basis_int __uwf_Room;
};

struct __uws_5 {
struct __uws_4 __uwf_T;
};

static uw_unit __uwn_expunger_1852(uw_context ctx, uw_Basis_client __uwr_cli_0) {
return(0);
}

/* Function prototypes */
static uw_unit __uwn_expunger_1852(uw_context, uw_Basis_client);
static uw_unit __uwn_initializer_1853(uw_context, uw_unit);
static uw_unit __uwn__speak_1844(uw_context, uw_Basis_int, uw_Basis_string, uw_unit);
static uw_unit __uwn_wrap_main_1851(uw_context, uw_unit, uw_unit);

struct __uws_1 {
uw_Basis_channel __uwf_Channel;
};

static uw_unit __uwn_initializer_1853(uw_context ctx, uw_unit __uwr___0) {
return(0);
}

#line 2 "/Users/jacksmith/prog/urweb/demo/broadcast.ur"
/* SQL sequence uw_Chat_Room_s */

#line 3 "/Users/jacksmith/prog/urweb/demo/broadcast.ur"
/* SQL table uw_Chat_Room_t uw_Id, uw_Client constraints  */

#line 5 "/Users/jacksmith/prog/urweb/demo/chat.ur"
/* SQL sequence uw_Chat_s */

#line 6 "/Users/jacksmith/prog/urweb/demo/chat.ur"
/* SQL table uw_Chat_t uw_Id constraints  */

#line 9 "/Users/jacksmith/prog/urweb/demo/chat.ur"
static uw_unit __uwn__speak_1844(uw_context ctx, uw_Basis_int __uwr_id_0, uw_Basis_string __uwr_line_1, uw_unit __uwr___2) {
return(({
uw_unit* __uwr_r_3 = (({
uw_unit* acc = NULL;
int dummy = (uw_begin_region(ctx), 0);
uw_ensure_transaction(ctx);
char *query = 0LL;
uw_conn *conn = uw_get_db(ctx);
sqlite3_stmt *stmt;
if (sqlite3_prepare_v2(conn->conn, query, -1, &stmt, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "Error preparing statement: %s<br />%s", query, sqlite3_errmsg(conn->conn));
uw_push_cleanup(ctx, (void (*)(void *))sqlite3_finalize, stmt);
int r;
sqlite3_reset(stmt);
uw_end_region(ctx);
while ((r = sqlite3_step(stmt)) == SQLITE_ROW) {
struct __uws_0 __uwr_r_3;
uw_unit* __uwr_acc_4 = acc;


acc = ({
uw_unit *tmp = uw_malloc(ctx, sizeof(uw_unit));
*tmp = __uwr_r_3;
tmp;
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
(({
uw_unit acc = 0;
int dummy = (uw_begin_region(ctx), 0);
uw_ensure_transaction(ctx);
char *query = ({
struct __uws_3* disc = __uwr_r_3;
struct __uws_3
(disc == NULL) ? ({
struct __uws_3 tmp;
uw_error(ctx, FATAL, "%s", "Query returned no rows");
tmp;
}) : (disc != NULL) && 1 ? ({
struct __uws_3 __uwr_r_4 = (*disc);
__uwr_r_4;
}) : ({
struct __uws_3 tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
})(ctx, 0).__uwf_T.__uwf_Room;
uw_conn *conn = uw_get_db(ctx);
sqlite3_stmt *stmt;
if (sqlite3_prepare_v2(conn->conn, query, -1, &stmt, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "Error preparing statement: %s<br />%s", query, sqlite3_errmsg(conn->conn));
uw_push_cleanup(ctx, (void (*)(void *))sqlite3_finalize, stmt);
int r;
sqlite3_reset(stmt);
uw_end_region(ctx);
while ((r = sqlite3_step(stmt)) == SQLITE_ROW) {
struct __uws_2 __uwr_r_4;
uw_unit __uwr_acc_5 = acc;

__uwr_r_4.__uwf_T.__uwf_Channel = (sqlite3_column_type(stmt, 0) == SQLITE_NULL ? ({ uw_Basis_channel tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #0"); tmp; }) : ({
sqlite3_int64 n = sqlite3_column_int64(stmt, 0);
uw_Basis_channel ch = {n >> 32, n & 0xFFFFFFFF};
ch;
}));

acc = uw_Basis_mstrcat(ctx, "SELECT * FROM uw_Chat_Room_t AS T_T WHERE (T_T.uw_id = ", __uwr_id_0, ")", ({
uw_Basis_string disc = uw_Basis_bool_True;
uw_Basis_string
(!strcmp(disc, "1")) ? "" : 1 ? ({
uw_Basis_string __uwr_h_6 = disc;
uw_Basis_strcat(ctx, " HAVING ", __uwr_h_6);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}), ({
uw_Basis_string disc = "";
uw_Basis_string
(!strcmp(disc, "")) ? "" : 1 ? ({
uw_Basis_string __uwr_orderby_6 = disc;
uw_Basis_strcat(ctx, " ORDER BY ", __uwr_orderby_6);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}), NULL)(ctx, __uwr_r_4, 0);
}
if (r == SQLITE_BUSY) {
sleep(1);
uw_error(ctx, UNLIMITED_RETRY, "Database is busy");
}
if (r != SQLITE_DONE) uw_error(ctx, FATAL, "query: query step failed: %s<br />%s", query, sqlite3_errmsg(conn->conn));
uw_pop_cleanup(ctx);
acc;
}))(ctx, 0);
}));
}

static uw_unit __uwn_wrap_main_1851(uw_context ctx, uw_unit __uwr_x0_0, uw_unit __uwr___1) {
return(({
uw_Basis_string __uwr_r_2 = (({
uw_Basis_string acc = "";
int dummy = (uw_begin_region(ctx), 0);
uw_ensure_transaction(ctx);
char *query = 0;
uw_conn *conn = uw_get_db(ctx);
sqlite3_stmt *stmt;
if (sqlite3_prepare_v2(conn->conn, query, -1, &stmt, NULL) != SQLITE_OK) uw_error(ctx, FATAL, "Error preparing statement: %s<br />%s", query, sqlite3_errmsg(conn->conn));
uw_push_cleanup(ctx, (void (*)(void *))sqlite3_finalize, stmt);
int r;
sqlite3_reset(stmt);
uw_end_region(ctx);
while ((r = sqlite3_step(stmt)) == SQLITE_ROW) {
struct __uws_5 __uwr_r_2;
uw_Basis_string __uwr_acc_3 = acc;

__uwr_r_2.__uwf_T.__uwf_Id = (sqlite3_column_type(stmt, 0) == SQLITE_NULL ? ({ uw_Basis_int tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #0"); tmp; }) : sqlite3_column_int64(stmt, 0));
__uwr_r_2.__uwf_T.__uwf_Room = (sqlite3_column_type(stmt, 1) == SQLITE_NULL ? ({ uw_Basis_int tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #1"); tmp; }) : sqlite3_column_int64(stmt, 1));
__uwr_r_2.__uwf_T.__uwf_Title = (sqlite3_column_type(stmt, 2) == SQLITE_NULL ? ({ uw_Basis_string tmp; uw_error(ctx, FATAL, "query: Unexpectedly NULL field #2"); tmp; }) : uw_strdup(ctx, (uw_Basis_string)sqlite3_column_text(stmt, 2)));

acc = uw_Basis_strcat(ctx, __uwr_acc_3, uw_Basis_mstrcat(ctx, "SELECT * FROM uw_Chat_t AS T_T", ({
uw_Basis_string disc = uw_Basis_bool_True;
uw_Basis_string
(!strcmp(disc, "1")) ? "" : 1 ? ({
uw_Basis_string __uwr_w_4 = disc;
uw_Basis_strcat(ctx, " WHERE ", __uwr_w_4);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}), ({
uw_Basis_string disc = uw_Basis_bool_True;
uw_Basis_string
(!strcmp(disc, "1")) ? "" : 1 ? ({
uw_Basis_string __uwr_h_4 = disc;
uw_Basis_strcat(ctx, " HAVING ", __uwr_h_4);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}), ({
uw_Basis_string disc = "";
uw_Basis_string
(!strcmp(disc, "")) ? "" : 1 ? ({
uw_Basis_string __uwr_orderby_4 = disc;
uw_Basis_strcat(ctx, " ORDER BY ", __uwr_orderby_4);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}), NULL)(ctx, __uwr_r_2, 0));
}
if (r == SQLITE_BUSY) {
sleep(1);
uw_error(ctx, UNLIMITED_RETRY, "Database is busy");
}
if (r != SQLITE_DONE) uw_error(ctx, FATAL, "query: query step failed: %s<br />%s", query, sqlite3_errmsg(conn->conn));
uw_pop_cleanup(ctx);
acc;
}))(ctx, 0);
((uw_write(ctx, "<body"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">\n<h1"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">Current Channels</h1>\n<tabl"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">\n<tr"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "> <th"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">ID</th> <th"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">Title</th> <th"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">#Subscribers</th> </tr>\n"), 0), ((uw_write(ctx, __uwr_r_2), 0), ((uw_write(ctx, "\n</tabl>\n<h1"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">New Channel</h1>\n"), 0), ((uw_write(ctx, uw_Basis_form(ctx, 0LL, 0LL, 0LL, uw_Basis_mstrcat(ctx, "\nTitle: <div", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "></div><br", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "></br>\n<submit", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "></submit>\n", NULL))), 0), (uw_write(ctx, "\n</body>"), 0)))))))))))))))))))))))))))));
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
__uwn_initializer_1853(ctx, 0);
}

static void uw_expunger(uw_context ctx, uw_Basis_client cli) {
__uwn_expunger_1852(ctx, cli);
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
if (!strncmp(request, "/Chat/speak", 11) && (request[11] == 0 || request[11] == '/')) {
request += 11;
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
uw_Basis_int arg0 = uw_Basis_unurlifyInt(ctx, &request);
uw_Basis_string arg1 = uw_Basis_unurlifyString(ctx, &request);
uw_unit it0 = __uwn__speak_1844(ctx, arg0, arg1, 0);
uw_write(ctx, uw_get_real_script(ctx));
uw_write(ctx, "\n");
uw_Basis_urlifyString_w(ctx, "");
return;
}
}
if (!strncmp(request, "/Chat/main", 10) && (request[10] == 0 || request[10] == '/')) {
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
__uwn_wrap_main_1851(ctx, arg0, 0);
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
