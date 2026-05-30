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

if (sqlite3_open("/private/tmp/listedit.db", &sqlite) != SQLITE_OK) uw_error(ctx, FATAL, "Can't open SQLite database.");

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

/* Function prototypes */
static uw_unit __uwn_wrap_main_1715(uw_context, uw_unit, uw_unit);

static char jslib[] = "urlRules = null;\n\nurfuncs[1712] = {c:\"t\",f:'{c:\"l\",b:{c:\"l\",b:{c:\"l\",b:{c:\"=\",e1:{c:\"f\",f:sg,a:cons({c:\"v\",n:2},null)},e2:{c:\"=\",e1:{c:\"f\",f:sc,a:cons({c:\"v\",n:0},null)},e2:{c:\"=\",e1:{c:\"f\",f:sc,a:cons({c:\"c\",v:\"\"},null)},e2:{c:\"=\",e1:{c:\"f\",f:sg,a:cons({c:\"v\",n:4},null)},e2:{c:\"=\",e1:{c:\"f\",f:sc,a:cons({c:\"c\",v:null},null)},e2:{c:\"=\",e1:{c:\"f\",f:sv,a:cons({c:\"v\",n:1},cons({c:\"r\",l:cons({n:\"Data\",v:{c:\"v\",n:3}},cons({n:\"NewData\",v:{c:\"v\",n:2}},cons({n:\"Tail\",v:{c:\"v\",n:0}},null)))},null))},e2:{c:\"f\",f:sv,a:cons({c:\"v\",n:7},cons({c:\"v\",n:1},null))}}}}}}}}}}'};\nurfuncs[1708] = {c:\"t\",f:'{c:\"l\",b:{c:\"f\",f:sb,a:cons({c:\"f\",f:ss,a:cons({c:\"v\",n:0},null)},cons({c:\"l\",b:{c:\"a\",f:{c:\"n\",n:1709},x:{c:\"v\",n:0}}},null)}}'};\nurfuncs[1709] = {c:\"t\",f:'{c:\"l\",b:{c:\"m\",e:{c:\"v\",n:0},p:cons({p:{c:\"c\",v:null},b:{c:\"f\",f:sr,a:cons({c:\"c\",v:\"\"},null)}},cons({p:{c:\"s\",n:false,p:{c:\"r\",l:cons({n:\"Data\",p:{/*hoho*/c:\"v\"}},cons({n:\"NewData\",p:{/*hoho*/c:\"v\"}},cons({n:\"Tail\",p:{/*hoho*/c:\"v\"}},null)))}},b:{c:\"f\",f:sr,a:cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\"\\\\\\\\n\\\\\\\\074script type=\\\\\\\\\"text/javascript\\\\\\\\\">dyn(\\\\\\\\\"span\\\\\\\\\", execD(\"},cons({c:\"f\",f:cat,a:cons({c:\"e\",e:{c:\"a\",f:{c:\"a\",f:{c:\"n\",n:1710},x:{c:\"v\",n:2}},x:{c:\"c\",v:null}}},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\"))\\\\\\\\074/script>\\\\\\\\n\\\\\\\\074button\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"class\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"style\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\" value=\\\\\\\\\"Change to:\\\\\\\\\" onclick=\\\\\\\\\\\\\\'uw_event=event;exec(\"},cons({c:\"f\",f:cat,a:cons({c:\"e\",e:{c:\"a\",f:{c:\"a\",f:{c:\"a\",f:{c:\"n\",n:1711},x:{c:\"v\",n:2}},x:{c:\"v\",n:1}},x:{c:\"c\",v:null}}},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\")\\\\\\\\\\\\\\'>\\\\\\\\074/button>\\\\\\\\n\\\\\\\\074script type=\\\\\\\\\"text/javascript\\\\\\\\\">inp(exec(\"},cons({c:\"f\",f:cat,a:cons({c:\"e\",e:{c:\"v\",n:1}},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\"))\\\\\\\\074/script>\\\\\\\\074br\"},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"class\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"f\",f:ERROR,a:cons({c:\"c\",v:\"style\"},cons({c:\"c\",v:\"\"},null))},cons({c:\"f\",f:cat,a:cons({c:\"c\",v:\">\\\\\\\\074/br>\\\\\\\\n\\\\\\\\074script type=\\\\\\\\\"text/javascript\\\\\\\\\">dyn(\\\\\\\\\"span\\\\\\\\\", execD(\"},cons({c:\"f\",f:cat,a:cons({c:\"e\",e:{c:\"a\",f:{c:\"n\",n:1708},x:{c:\"v\",n:0}}},cons({c:\"c\",v:\"))\\\\\\\\074/script>\\\\\\\\n\"},null)},null)},null)},null)},null)},null)},null)},null)},null)},null)},null)},null)},null)},null)},null)}},null))}}'};\nurfuncs[1711] = {c:\"t\",f:'{c:\"l\",b:{c:\"l\",b:{c:\"l\",b:{c:\"=\",e1:{c:\"f\",f:sg,a:cons({c:\"v\",n:1},null)},e2:{c:\"f\",f:sv,a:cons({c:\"v\",n:3},cons({c:\"v\",n:0},null))}}}}}'};\nurfuncs[1710] = {c:\"t\",f:'{c:\"l\",b:{c:\"l\",b:{c:\"f\",f:sb,a:cons({c:\"f\",f:ss,a:cons({c:\"v\",n:1},null)},cons({c:\"l\",b:{c:\"f\",f:sr,a:cons({c:\"f\",f:eh,a:cons({c:\"v\",n:0},null)},null)}},null)}}}'};\n\ntime_format = \"%c\";\n";

static uw_unit __uwn_wrap_main_1715(uw_context ctx, uw_unit __uwr_x0_0, uw_unit __uwr___1) {
return(({
uw_Basis_source __uwr_r_2 = uw_Basis_new_client_source(ctx, "{c:\"c\",v:null}");
({
uw_Basis_source __uwr_r_3 = uw_Basis_new_client_source(ctx, uw_Basis_mstrcat(ctx, "{c:\"c\",v:", uw_Basis_htmlifySource(ctx, __uwr_r_2), "}", NULL));
({
uw_Basis_source __uwr_r_4 = uw_Basis_new_client_source(ctx, uw_Basis_mstrcat(ctx, "{c:\"c\",v:", uw_Basis_jsifyString(ctx, ""), "}", NULL));
((uw_write(ctx, "<body"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, ">\n<script type=\"text/javascript\">inp(exec("), 0), (((uw_write(ctx, "{c:\"c\",v:"), 0), (uw_Basis_htmlifySource_w(ctx, __uwr_r_4), (uw_write(ctx, "}"), 0))), ((uw_write(ctx, "))</script> <button"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, " value=\"Add\" onclick=\'uw_event=event;exec("), 0), (((uw_write(ctx, "{c:\"a\",f:{c:\"a\",f:{c:\"a\",f:{c:\"n\",n:1712},x:{c:\"c\",v:"), 0), (uw_Basis_htmlifySource_w(ctx, __uwr_r_3), ((uw_write(ctx, "}},x:{c:\"c\",v:"), 0), (uw_Basis_htmlifySource_w(ctx, __uwr_r_4), (uw_write(ctx, "}},x:{c:\"c\",v:null}}"), 0))))), ((uw_write(ctx, ")\'></button><br"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></br>\n<br"), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "class", "")), 0), ((uw_write(ctx, uw_Basis_attrOptional(ctx, "style", "")), 0), ((uw_write(ctx, "></br>\n<script type=\"text/javascript\">dyn(\"span\", execD("), 0), (((uw_write(ctx, "{c:\"a\",f:{c:\"n\",n:1708},x:{c:\"c\",v:"), 0), (uw_Basis_htmlifySource_w(ctx, __uwr_r_2), (uw_write(ctx, "}}"), 0))), (uw_write(ctx, "))</script>\n</body>"), 0)))))))))))))))))));
});
});
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
if (!strncmp(request, "/ListEdit/main", 14) && (request[14] == 0 || request[14] == '/')) {
request += 14;
if (*request == '/') ++request;
uw_write_header(ctx, "Content-type: text/html; charset=utf-8\r\n");
uw_write_header(ctx, "Content-script-type: text/javascript\r\n");
uw_write(ctx, uw_begin_html5);
uw_mayReturnIndirectly(ctx);
uw_set_could_write_db(ctx, 0);
uw_set_at_most_one_query(ctx, 0);
uw_set_needs_push(ctx, 0);
uw_set_needs_sig(ctx, 0);
uw_login(ctx);
{
uw_unit arg0 = uw_Basis_unurlifyUnit(ctx, &request);
__uwn_wrap_main_1715(ctx, arg0, 0);
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
