#pragma once
#include "chan.h"
#include "caplib.h"

// Affine channel wrapper allowing at most one send and one receive
typedef struct affine_chan {
  chan_t base;
  int used_send;
  int used_recv;
} affine_chan_t;

[[nodiscard]] affine_chan_t *
affine_chan_create(const struct msg_type_desc *desc);
void affine_chan_destroy(affine_chan_t *c);
[[nodiscard]] int affine_chan_send(affine_chan_t *c, exo_cap dest,
                                   const void *msg, size_t len);
[[nodiscard]] int affine_chan_recv(affine_chan_t *c, exo_cap src, void *msg,
                                   size_t len);

// Simple lambda term representation
typedef int (*lambda_fn)(void *env);

typedef struct lambda_term {
  lambda_fn fn; // one evaluation step
  void *env;    // closure environment
  int steps;    // total steps executed
} lambda_term_t;

// Run the lambda term for up to `fuel` steps. The function returns
// the value returned by the underlying lambda function on the last
// step (0 for continue, non-zero to stop).
int lambda_run(lambda_term_t *t, int fuel);

// Lambda capability that can be consumed exactly once
typedef struct lambda_cap {
  lambda_term_t term; // lambda to execute
  exo_cap cap;        // associated capability token
  int consumed;       // non-zero once used
} lambda_cap_t;

[[nodiscard]] lambda_cap_t *lambda_cap_create(lambda_fn fn, void *env,
                                             exo_cap cap);
void lambda_cap_destroy(lambda_cap_t *lc);
// Execute the lambda once and mark the capability consumed
int lambda_cap_use(lambda_cap_t *lc, int fuel);

// Security hooks for microkernels
// Delegate duplicates the capability for a new owner
int lambda_cap_delegate(lambda_cap_t *lc, uint16_t new_owner);
// Revoke invalidates the capability via the kernel
int lambda_cap_revoke(lambda_cap_t *lc);

// Macro to declare an affine typed channel using Cap'n Proto helpers
#define AFFINE_CHAN_DECLARE(name, type)                                        \
  static const struct msg_type_desc name##_typedesc = {                        \
      type##_MESSAGE_SIZE, 0, (msg_encode_fn)type##_encode,                    \
      (msg_decode_fn)type##_decode};                                           \
  typedef struct {                                                             \
    affine_chan_t base;                                                        \
  } name##_t;                                                                  \
  static inline name##_t *name##_create(void) {                                \
    return (name##_t *)affine_chan_create(&name##_typedesc);                   \
  }                                                                            \
  static inline void name##_destroy(name##_t *c) {                             \
    affine_chan_destroy(&c->base);                                             \
  }                                                                            \
  static inline int name##_send(name##_t *c, exo_cap dest, const type *m) {    \
    unsigned char buf[type##_MESSAGE_SIZE];                                    \
    size_t len = type##_encode(m, buf);                                        \
    return affine_chan_send(&c->base, dest, buf, len);                         \
  }                                                                            \
  static inline int name##_recv(name##_t *c, exo_cap src, type *m) {           \
    unsigned char buf[type##_MESSAGE_SIZE];                                    \
    int r = affine_chan_recv(&c->base, src, buf, type##_MESSAGE_SIZE);         \
    if (r >= 0)                                                                \
      type##_decode(m, buf);                                                   \
    return r;                                                                  \
  }
