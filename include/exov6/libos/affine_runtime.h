#pragma once
#include "unified_chan.h"
#include "caplib.h"

/* Legacy compatibility layer */
typedef unified_chan_t affine_chan_t;

/* Legacy compatibility functions */
static inline affine_chan_t *affine_chan_create(const struct msg_type_desc *desc) {
    return unified_chan_create(desc, CHAN_FIXED | CHAN_AFFINE);
}

static inline void affine_chan_destroy(affine_chan_t *c) {
    unified_chan_destroy(c);
}

static inline int affine_chan_send(affine_chan_t *c, exo_cap dest, const void *msg, size_t len) {
    return unified_chan_send(c, dest, msg, len);
}

static inline int affine_chan_recv(affine_chan_t *c, exo_cap src, void *msg, size_t len) {
    return unified_chan_recv(c, src, msg, len);
}

/* Legacy macro - now redirects to unified system */
#define AFFINE_CHAN_DECLARE(name, type) \
    UNIFIED_CHAN_DECLARE(name, type, CHAN_FIXED | CHAN_AFFINE)

/* Lambda capabilities remain unchanged */
typedef int (*lambda_fn)(void *env);

typedef struct lambda_term {
  lambda_fn fn; // one evaluation step
  void *env;    // closure environment
  int steps;    // total steps executed
} lambda_term_t;

int lambda_run(lambda_term_t *t, int fuel);

typedef struct lambda_cap {
  lambda_term_t term; // lambda to execute
  exo_cap cap;        // associated capability token
  int consumed;       // non-zero once used
} lambda_cap_t;

EXO_NODISCARD lambda_cap_t *lambda_cap_create(lambda_fn fn, void *env, exo_cap cap);
void lambda_cap_destroy(lambda_cap_t *lc);
int lambda_cap_use(lambda_cap_t *lc, int fuel);
int lambda_cap_delegate(lambda_cap_t *lc, uint16_t new_owner);
int lambda_cap_revoke(lambda_cap_t *lc);
