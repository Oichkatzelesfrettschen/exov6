#pragma once

/**
 * @file chan.h
 * @brief Type-safe channel interface for exokernel IPC
 * 
 * Pure C17 implementation with modern patterns.
 */

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include "types.h"
#include "exo.h"
#include "ipc.h"  // For msg_type_desc

// Generic channel descriptor storing expected message size and type
typedef struct chan {
    size_t msg_size;
    const struct msg_type_desc *desc;
} chan_t;

// Allocate a channel expecting messages of specified descriptor
chan_t *chan_create(const struct msg_type_desc *desc);

// Free a channel allocated with chan_create
void chan_destroy(chan_t *c);

// Send and receive through an exo capability endpoint
int chan_endpoint_send(chan_t *c, exo_cap dest, const void *msg, size_t len);
int chan_endpoint_recv(chan_t *c, exo_cap src, void *msg, size_t len);

// Helper macro to declare a typed channel wrapper
// Usage: CHAN_DECLARE(mychan, struct mymsg);
// Provides mychan_t type with create/send/recv functions
#define CHAN_DECLARE(name, type)                                               \
  static const struct msg_type_desc name##_typedesc = {                        \
      .msg_size = sizeof(type)                                                 \
  };                                                                           \
  typedef struct {                                                             \
    chan_t base;                                                               \
  } name##_t;                                                                  \
  static inline name##_t *name##_create(void) {                                \
    return (name##_t *)chan_create(&name##_typedesc);                          \
  }                                                                            \
  static inline void name##_destroy(name##_t *c) {                            \
    chan_destroy(&c->base);                                                    \
  }                                                                            \
  static inline int name##_send(name##_t *c, exo_cap dest, const type *m) {    \
    return chan_endpoint_send(&c->base, dest, m, sizeof(type));                \
  }                                                                            \
  static inline int name##_recv(name##_t *c, exo_cap src, type *m) {           \
    return chan_endpoint_recv(&c->base, src, m, sizeof(type));                 \
  }

// Compile-time assertions
_Static_assert(sizeof(chan_t) <= 32, "Channel descriptor too large");
_Static_assert(_Alignof(chan_t) >= 8, "Channel must be properly aligned");