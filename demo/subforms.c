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
}

static void uw_db_prepare(uw_context ctx) { }

static void uw_db_init(uw_context ctx) {
sqlite3 *sqlite;
sqlite3_stmt *stmt;
uw_conn *conn;

if (sqlite3_open("/tmp/urweb-subforms.db", &sqlite) != SQLITE_OK) uw_error(ctx, FATAL, "Can't open SQLite database.");

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
uw_Basis_string __uwf_Num;
uw_Basis_string __uwf_Text;
};

struct __uws_2 {
struct __uws_1 __uwf_1;
struct __uws_2* __uwf_2;
};

struct __uws_3 {
struct __uws_2* __uwf_Lines;
};

/* Function prototypes */
static uw_Basis_string __uwn_lam_1713_1713(uw_context, struct __uws_2*);
static uw_unit __uwn_lam_1714_1714(uw_context, struct __uws_2*);
static uw_Basis_string __uwn__subPRIME_1704(uw_context, struct __uws_2*);
static uw_unit __uwn__subPRIME_1711(uw_context, struct __uws_2*);
static uw_Basis_string __uwn_lam_1715_1715(uw_context, uw_Basis_int);
static uw_unit __uwn_lam_1716_1716(uw_context, uw_Basis_int);
static uw_Basis_string __uwn_subfrms_1706(uw_context, uw_Basis_int);
static uw_unit __uwn_subfrms_1712(uw_context, uw_Basis_int);
static uw_Basis_string __uwn_lam_1717_1717(uw_context, uw_Basis_int, uw_unit, uw_unit);
static uw_unit __uwn_lam_1718_1718(uw_context, struct __uws_3, uw_unit);
static uw_Basis_string __uwn_form_1707(uw_context, uw_Basis_int, uw_unit);
static uw_unit __uwn_wrap_sub_1710(uw_context, struct __uws_3, uw_unit);
static uw_unit __uwn_wrap_main_1709(uw_context, uw_unit, uw_unit);

/* URL handler prototypes */
static struct __uws_2 *unurlify_list_2(uw_context, char **);

static char jslib[] = "";

#line 4 "/Users/jacksmith/prog/urweb/demo/subforms.ur"
static uw_Basis_string __uwn_lam_1713_1713(uw_context ctx, struct __uws_2* __uwr_ls_0) {
return(({
struct __uws_2* disc = __uwr_ls_0;

(disc == NULL) ? "" : (disc != NULL) && 1 && 1 ? ({
struct __uws_1 __uwr_r_1 = (*disc).__uwf_1;
struct __uws_2* __uwr_ls_2 = (*disc).__uwf_2;
uw_Basis_mstrcat(ctx, "\n<li", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">", uw_Basis_htmlifyString(ctx, __uwr_r_1.__uwf_Num), " = ", uw_Basis_htmlifyString(ctx, __uwr_r_1.__uwf_Text), "</li>\n", __uwn__subPRIME_1704(ctx, __uwr_ls_2), "\n", NULL);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}));
}

#line 1 "/Users/jacksmith/prog/urweb/demo/subforms.ur"
static uw_unit __uwn_lam_1714_1714(uw_context ctx, struct __uws_2* __uwr_ls_0) {
return((uw_write(ctx, ({
struct __uws_2* disc = __uwr_ls_0;

(disc == NULL) ? "" : (disc != NULL) && 1 && 1 ? ({
struct __uws_1 __uwr_r_1 = (*disc).__uwf_1;
struct __uws_2* __uwr_ls_2 = (*disc).__uwf_2;
uw_Basis_mstrcat(ctx, "\n<li", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">", uw_Basis_htmlifyString(ctx, __uwr_r_1.__uwf_Num), " = ", uw_Basis_htmlifyString(ctx, __uwr_r_1.__uwf_Text), "</li>\n", __uwn__subPRIME_1704(ctx, __uwr_ls_2), "\n", NULL);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
})), 0));
}

#line 1 "/Users/jacksmith/prog/urweb/demo/subforms.ur"
static uw_Basis_string __uwn__subPRIME_1704(uw_context, struct __uws_2*);
static uw_unit __uwn__subPRIME_1711(uw_context, struct __uws_2*);

static uw_Basis_string __uwn__subPRIME_1704(uw_context ctx, struct __uws_2* __uwr_x_0) {
restart:
return(__uwn_lam_1713_1713(ctx, __uwr_x_0));
}
static uw_unit __uwn__subPRIME_1711(uw_context ctx, struct __uws_2* __uwr_x_0) {
restart:
return(__uwn_lam_1714_1714(ctx, __uwr_x_0));
}


#line 17 "/Users/jacksmith/prog/urweb/demo/subforms.ur"
static uw_Basis_string __uwn_lam_1715_1715(uw_context ctx, uw_Basis_int __uwr_n_0) {
return(({
uw_Basis_bool disc = (__uwr_n_0 <= 0LL);

(disc == uw_Basis_True) ? "" : (disc == uw_Basis_False) ? uw_Basis_mstrcat(ctx, "\n<input type=\"hidden\" name=\".i\" value=\"1\" />\n<div", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), " value=\"", uw_Basis_attrifyString(ctx, uw_Basis_intToString(ctx, __uwr_n_0)), "\"></div>\n<li", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">", uw_Basis_htmlifyInt(ctx, __uwr_n_0), ": <div", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "></div></li>\n<input type=\"hidden\" name=\".e\" value=\"1\" />\n", __uwn_subfrms_1706(ctx, (__uwr_n_0 - 1LL)), "\n", NULL) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}));
}

#line 16 "/Users/jacksmith/prog/urweb/demo/subforms.ur"
static uw_unit __uwn_lam_1716_1716(uw_context ctx, uw_Basis_int __uwr_n_0) {
return((uw_write(ctx, ({
uw_Basis_bool disc = (__uwr_n_0 <= 0LL);

(disc == uw_Basis_True) ? "" : (disc == uw_Basis_False) ? uw_Basis_mstrcat(ctx, "\n<input type=\"hidden\" name=\".i\" value=\"1\" />\n<div", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), " value=\"", uw_Basis_attrifyString(ctx, uw_Basis_intToString(ctx, __uwr_n_0)), "\"></div>\n<li", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">", uw_Basis_htmlifyInt(ctx, __uwr_n_0), ": <div", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "></div></li>\n<input type=\"hidden\" name=\".e\" value=\"1\" />\n", __uwn_subfrms_1706(ctx, (__uwr_n_0 - 1LL)), "\n", NULL) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
})), 0));
}

#line 16 "/Users/jacksmith/prog/urweb/demo/subforms.ur"
static uw_Basis_string __uwn_subfrms_1706(uw_context, uw_Basis_int);
static uw_unit __uwn_subfrms_1712(uw_context, uw_Basis_int);

static uw_Basis_string __uwn_subfrms_1706(uw_context ctx, uw_Basis_int __uwr_x_0) {
restart:
return(__uwn_lam_1715_1715(ctx, __uwr_x_0));
}
static uw_unit __uwn_subfrms_1712(uw_context ctx, uw_Basis_int __uwr_x_0) {
restart:
return(__uwn_lam_1716_1716(ctx, __uwr_x_0));
}


#line 28 "/Users/jacksmith/prog/urweb/demo/subforms.ur"
static uw_Basis_string __uwn_lam_1717_1717(uw_context ctx, uw_Basis_int __uwr_n_0, uw_unit __uwr___1, uw_unit __uwr___2) {
return(uw_Basis_mstrcat(ctx, "<body", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">\n<form method=\"post\"", " action=\"/Subforms/sub\">\n", uw_Basis_subforms(ctx, 0, 0, uw_Basis_mstrcat(ctx, "\n", __uwn_subfrms_1706(ctx, __uwr_n_0), "\n", NULL)), "\n<input type=\"submit\"", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), " action=\"/Subforms/sub\" />\n</form>\n<a", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">One more blank</a><br", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), "></br>\n", ({
uw_Basis_bool disc = (! (__uwr_n_0 <= 0LL));

(disc == uw_Basis_True) ? uw_Basis_mstrcat(ctx, "<a", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">One fewer blank</a>", NULL) : (disc == uw_Basis_False) ? "" : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
}), "\n</body>", NULL));
}

#line 28 "/Users/jacksmith/prog/urweb/demo/subforms.ur"
static uw_unit __uwn_lam_1718_1718(uw_context ctx, struct __uws_3 __uwr_x0_0, uw_unit __uwr___1) {
return(((uw_write(ctx, "<body"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">\n"), 0), ((uw_write(ctx, ({
struct __uws_2* disc = __uwr_x0_0.__uwf_Lines;

(disc == NULL) ? "" : (disc != NULL) && 1 && 1 ? ({
struct __uws_1 __uwr_r_2 = (*disc).__uwf_1;
struct __uws_2* __uwr_ls_3 = (*disc).__uwf_2;
uw_Basis_mstrcat(ctx, "\n<li", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">", uw_Basis_htmlifyString(ctx, __uwr_r_2.__uwf_Num), " = ", uw_Basis_htmlifyString(ctx, __uwr_r_2.__uwf_Text), "</li>\n", __uwn__subPRIME_1704(ctx, __uwr_ls_3), "\n", NULL);
}) : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
})), 0), (uw_write(ctx, "\n</body>"), 0)))))));
}

#line 28 "/Users/jacksmith/prog/urweb/demo/subforms.ur"
static uw_Basis_string __uwn_form_1707(uw_context, uw_Basis_int, uw_unit);
static uw_unit __uwn_wrap_sub_1710(uw_context, struct __uws_3, uw_unit);

static uw_Basis_string __uwn_form_1707(uw_context ctx, uw_Basis_int __uwr_x_0, uw_unit __uwr___1) {
restart:
return(({
uw_Basis_int arg0 = __uwr_x_0;
uw_unit arg1 = __uwr___1;
uw_unit arg2 = 0;
__uwn_lam_1717_1717(ctx, arg0, arg1, arg2);
}));
}
static uw_unit __uwn_wrap_sub_1710(uw_context ctx, struct __uws_3 __uwr_x_0, uw_unit __uwr_x_1) {
restart:
return(({
struct __uws_3 arg0 = __uwr_x_0;
uw_unit arg1 = __uwr_x_1;
__uwn_lam_1718_1718(ctx, arg0, arg1);
}));
}


static uw_unit __uwn_wrap_main_1709(uw_context ctx, uw_unit __uwr_x0_0, uw_unit __uwr___1) {
return(((uw_write(ctx, "<body"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">\n<form method=\"post\" action=\"/Subforms/sub\">\n"), 0), ((uw_write(ctx, uw_Basis_subforms(ctx, 0, 0, uw_Basis_mstrcat(ctx, "\n", __uwn_subfrms_1706(ctx, 1LL), "\n", NULL))), 0), ((uw_write(ctx, "\n<input type=\"submit\""), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, " action=\"/Subforms/sub\" />\n</form>\n<a"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">One more blank</a><br"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></br>\n"), 0), ((uw_write(ctx, ({
uw_Basis_bool disc = (! (1LL <= 0LL));

(disc == uw_Basis_True) ? uw_Basis_mstrcat(ctx, "<a", uw_Basis_attrOptional(ctx, "class", ""), uw_Basis_attrOptional(ctx, "style", ""), ">One fewer blank</a>", NULL) : (disc == uw_Basis_False) ? "" : ({
uw_Basis_string tmp;
uw_error(ctx, FATAL, "Ur/Web runtime: case/of exhausted — none of the patterns matched this value.");
tmp;
});
})), 0), (uw_write(ctx, "\n</body>"), 0))))))))))))))))));
}

/* URL handler helpers */
static struct __uws_2 *unurlify_list_2(uw_context ctx, char **request) {
return ((*request)[0] == '/' ? ++*request : *request,
((!strncmp(*request, "Nil", 3) && ((*request)[3] == 0 || (*request)[3] == '/')) ? (*request += 3, ((*request)[0] == '/' ? ((*request)[0] = 0, ++*request) : NULL), NULL) : ((!strncmp(*request, "Cons", 4) && ((*request)[4] == 0 || (*request)[4] == '/')) ? (*request += 4, ((*request)[0] == '/' ? ++*request : NULL),
({
struct __uws_2 *tmp = uw_malloc(ctx, sizeof(struct __uws_2));
*tmp = ({
struct __uws_1 uwr_1 = ({
uw_Basis_string uwr_Num = uw_Basis_unurlifyString(ctx, request);
uw_Basis_string uwr_Text = uw_Basis_unurlifyString(ctx, request);
struct __uws_1 tmp = { uwr_Num, uwr_Text };
tmp;
});
struct __uws_2* uwr_2 = unurlify_list_2(ctx, request);
struct __uws_2 tmp = { uwr_1, uwr_2 };
tmp;
});
tmp;
})) : (uw_error(ctx, FATAL, "Ur/Web: could not decode a list from the URL at this point in the path: %s", *request), NULL))));
}

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
if (!strncmp(request, "/Subforms/sub", 13) && (request[13] == 0 || request[13] == '/')) {
request += 13;
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
struct __uws_3 arg0 = ({
struct __uws_2* uwr_Lines = unurlify_list_2(ctx, &request);
struct __uws_3 tmp = { uwr_Lines };
tmp;
});
__uwn_wrap_sub_1710(ctx, arg0, 0);
uw_write(ctx, "</html>");
return;
}
}
if (!strncmp(request, "/Subforms/main", 14) && (request[14] == 0 || request[14] == '/')) {
request += 14;
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
__uwn_wrap_main_1709(ctx, arg0, 0);
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
