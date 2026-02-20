/* Compatibility layer: ICU U8_* macros implemented with libunistring */

#ifndef UNICODE_COMPAT_H
#define UNICODE_COMPAT_H

#include <string.h>
#include <unistr.h>
#include <unictype.h>
#include <unicase.h>

#define U8_IS_SINGLE(c) ((unsigned char)(c) < 0x80)

#define U8_NEXT(s, i, length, c) do { \
  const uint8_t *__s = (const uint8_t*)(s); \
  size_t __len = ((length) < 0) ? strlen((const char*)__s + (i)) : (size_t)((length) - (i)); \
  int __n = u8_mbtouc((ucs4_t*)&(c), __s + (i), __len); \
  (i) += (__n > 0) ? __n : 1; \
  if (__n <= 0) (c) = 0xFFFD; \
} while(0)

#define U8_APPEND_UNSAFE(buf, i, c) do { \
  int __n = u8_uctomb((uint8_t*)(buf) + (i), (ucs4_t)(c), 6); \
  if (__n > 0) (i) += __n; \
} while(0)

static inline int u8_length_u(ucs4_t c) {
  if (c < 0x80) return 1;
  if (c < 0x800) return 2;
  if (c < 0x10000) return 3;
  return 4;
}

#define U8_LENGTH(c) u8_length_u((ucs4_t)(c))

#define U8_FWD_1(s, i, length) do { \
  size_t __len = ((length) < 0) ? strlen((const char*)(s) + (i)) : (size_t)((length) - (i)); \
  int __m = u8_mblen((const uint8_t*)(s) + (i), __len); \
  (i) += (__m > 0) ? __m : 1; \
} while(0)

#define U8_FWD_N(s, i, length, n) do { \
  int __nn = (n); \
  while (__nn-- > 0) { U8_FWD_1(s, i, length); } \
} while(0)

#endif
