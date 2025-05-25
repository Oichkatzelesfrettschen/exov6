#pragma once
#include "types.h"
#include "caplib.h"
#include "exo_ipc.h"

// Generic channel descriptor storing expected message size and type
typedef struct chan {
  size_t msg_size;
  const struct msg_type_desc *desc;
} chan_t;

// Allocate a channel expecting messages of size msg_size bytes
[[nodiscard]] chan_t *chan_create(const struct msg_type_desc *desc);

// Free a channel allocated with chan_create
void chan_destroy(chan_t *c);

// Send and receive through an exo capability endpoint
[[nodiscard]] exo_ipc_status chan_endpoint_send(chan_t *c, exo_cap dest,
                                                const void *msg, size_t len);
[[nodiscard]] exo_ipc_status chan_endpoint_recv(chan_t *c, exo_cap src, void *msg,
                                                size_t len);

// Helper macro to declare a typed channel wrapper
// Usage: CHAN_DECLARE(mychan, struct mymsg);
// Provides mychan_t type with create/send/recv functions
#define CHAN_DECLARE(name, type)                                               \
  static const struct msg_type_desc name##_typedesc = {type##_MESSAGE_SIZE};   \
  typedef struct {                                                             \
    chan_t base;                                                               \
  } name##_t;                                                                  \
  static inline name##_t *name##_create(void) {                                \
    return (name##_t *)chan_create(&name##_typedesc);                          \
  }                                                                            \
  static inline void name##_destroy(name##_t *c) { chan_destroy(&c->base); }   \
  static inline exo_ipc_status name##_send(name##_t *c, exo_cap dest,            \
                                          const type *m) {                      \
    unsigned char buf[type##_MESSAGE_SIZE];                                    \
    type##_encode(m, buf);                                                     \
    return chan_endpoint_send(&c->base, dest, buf, type##_MESSAGE_SIZE);       \
  }                                                                            \
  static inline exo_ipc_status name##_recv(name##_t *c, exo_cap src, type *m) { \
    unsigned char buf[type##_MESSAGE_SIZE];                                    \
    exo_ipc_status r =                                                      \
        chan_endpoint_recv(&c->base, src, buf, type##_MESSAGE_SIZE);          \
    if (r == 0)                                                                \
      type##_decode(m, buf);                                                   \
    return r;                                                                  \
  }
