#pragma once
#include "chan.h"
#include "caplib.h"

// Define nodiscard attribute for functions whose return values must be checked
#ifndef EXO_NODISCARD
  #if defined(__has_attribute)
    #if __has_attribute(nodiscard)
      #define EXO_NODISCARD [[nodiscard]]
    #elif __has_attribute(warn_unused_result)
      #define EXO_NODISCARD __attribute__((warn_unused_result))
    #else
      #define EXO_NODISCARD
    #endif
  #else
    #define EXO_NODISCARD
  #endif
#endif

// Affine channel wrapper allowing at most one send and one receive
typedef struct affine_chan {
  chan_t base;
  int used_send;
  int used_recv;
} affine_chan_t;

EXO_NODISCARD affine_chan_t *
affine_chan_create(const struct msg_type_desc *desc);
void affine_chan_destroy(affine_chan_t *c);
EXO_NODISCARD int affine_chan_send(affine_chan_t *c, exo_cap dest,
                                   const void *msg, size_t len);
EXO_NODISCARD int affine_chan_recv(affine_chan_t *c, exo_cap src, void *msg,
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

EXO_NODISCARD lambda_cap_t *lambda_cap_create(lambda_fn fn, void *env,
                                              exo_cap cap);
void lambda_cap_destroy(lambda_cap_t *lc);
// Execute the lambda once and mark the capability consumed
int lambda_cap_use(lambda_cap_t *lc, int fuel);

// Security hooks for microkernels
// Delegate duplicates the capability for a new owner
int lambda_cap_delegate(lambda_cap_t *lc, uint16_t new_owner);
// Revoke invalidates the capability via the kernel
int lambda_cap_revoke(lambda_cap_t *lc);

// Note: AFFINE_CHAN_DECLARE macro is now provided by unified_chan.h 
// to avoid redefinition conflicts with the unified channel system.
