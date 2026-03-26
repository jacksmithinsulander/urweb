/* Ur/Web — Persy bridge (built from crates/urweb-persy). */
#ifndef URWEB_PERSY_H
#define URWEB_PERSY_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Opaque Persy database handle from urweb_persy_open. */
void *urweb_persy_open(const char *path);

void urweb_persy_close(void *handle);

/* Insert / lookup in Persy index "urweb_kv" (opaque byte keys/values). */
int32_t urweb_persy_put(void *handle, const uint8_t *key, size_t key_len,
                        const uint8_t *val, size_t val_len);

/*
 * On success sets *out to a malloc'd buffer of *out_len bytes (not NUL-terminated).
 * Caller must free(*out). Returns 0 if found, 1 if missing, -1 on error.
 */
int32_t urweb_persy_get(void *handle, const uint8_t *key, size_t key_len,
                        uint8_t **out, size_t *out_len);

#ifdef __cplusplus
}
#endif

#endif /* URWEB_PERSY_H */
