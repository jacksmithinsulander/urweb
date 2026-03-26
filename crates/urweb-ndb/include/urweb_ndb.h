/* Ur/Web — ndb-style line KV store (Rust staticlib; no plan9port headers). */
#ifndef URWEB_NDB_H
#define URWEB_NDB_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Open (create) a line-oriented database file. Pass ":memory:" for a private temp file.
 * Returns NULL on failure.
 */
void *urweb_ndb_open(const char *path);

void urweb_ndb_close(void *handle);

/*
 * Append one record: UrK=<key> UrV=<val>\\n (UTF-8). Key and value must not contain '=', CR, or LF.
 * Returns 0 on success, -1 on error.
 */
int32_t urweb_ndb_put(void *handle, const uint8_t *key, size_t key_len,
                      const uint8_t *val, size_t val_len);

/*
 * On success sets *out to a malloc'd buffer of *out_len bytes (not NUL-terminated).
 * Caller must free(*out). Returns 0 if found, 1 if missing, -1 on error (last matching UrK wins).
 */
int32_t urweb_ndb_get(void *handle, const uint8_t *key, size_t key_len,
                      uint8_t **out, size_t *out_len);

#ifdef __cplusplus
}
#endif

#endif /* URWEB_NDB_H */
