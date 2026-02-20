#include "config.h"

#include <stdlib.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <pthread.h>

#include <bearssl_hash.h>
#include <bearssl_rand.h>

#define PASSSIZE 4

int uw_hash_blocksize = 32;

static int password[PASSSIZE];

char *uw_sig_file = NULL;

static br_hmac_drbg_context prng_ctx;
static pthread_mutex_t prng_mutex = PTHREAD_MUTEX_INITIALIZER;
static int prng_seeded = 0;

static void seed_prng(void) {
  unsigned char seed[32];
  int fd = open("/dev/urandom", O_RDONLY);
  if (fd < 0) {
    fprintf(stderr, "Error opening /dev/urandom\n");
    perror("open");
    exit(1);
  }
  if (read(fd, seed, sizeof seed) != (ssize_t)sizeof seed) {
    fprintf(stderr, "Error reading from /dev/urandom\n");
    close(fd);
    exit(1);
  }
  close(fd);
  br_hmac_drbg_init(&prng_ctx, &br_sha256_vtable, seed, sizeof seed);
  prng_seeded = 1;
}

/* Generate len cryptographically secure random bytes into buf. Returns 1 on success, 0 on failure. */
int uw_rand_bytes(unsigned char *buf, size_t len) {
  pthread_mutex_lock(&prng_mutex);
  if (!prng_seeded)
    seed_prng();
  br_hmac_drbg_generate(&prng_ctx, buf, len);
  pthread_mutex_unlock(&prng_mutex);
  return 1;
}

static void random_password(void) {
  if (!uw_rand_bytes((unsigned char *)password, sizeof password)) {
    fprintf(stderr, "Error generating random password\n");
    exit(1);
  }
}

void uw_init_crypto(void) {
  /* Prepare signatures. */
  if (uw_sig_file) {
    int fd;

    if (access(uw_sig_file, F_OK)) {
      random_password();

      if ((fd = open(uw_sig_file, O_WRONLY | O_CREAT, 0700)) < 0) {
        fprintf(stderr, "Can't open signature file %s\n", uw_sig_file);
        perror("open");
        exit(1);
      }

      if (write(fd, &password, sizeof password) != (ssize_t)sizeof password) {
        fprintf(stderr, "Error writing signature file\n");
        exit(1);
      }

      close(fd);
    } else {
      if ((fd = open(uw_sig_file, O_RDONLY)) < 0) {
        fprintf(stderr, "Can't open signature file %s\n", uw_sig_file);
        perror("open");
        exit(1);
      }

      if (read(fd, &password, sizeof password) != (ssize_t)sizeof password) {
        fprintf(stderr, "Error reading signature file\n");
        exit(1);
      }

      close(fd);
    }
  } else
    random_password();
}

void uw_sign(const char *in, unsigned char *out) {
  br_sha256_context ctx;

  br_sha256_init(&ctx);
  br_sha256_update(&ctx, password, sizeof password);
  br_sha256_update(&ctx, in, strlen(in));
  br_sha256_out(&ctx, out);
}
