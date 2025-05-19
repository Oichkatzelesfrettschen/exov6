#pragma once
#include "types.h"
#include "caplib.h"

// Generic channel descriptor storing expected message size
typedef struct chan {
    size_t msg_size;
} chan_t;

// Allocate a channel expecting messages of size msg_size bytes
chan_t *chan_create(size_t msg_size);

// Free a channel allocated with chan_create
void chan_destroy(chan_t *c);

// Send and receive through an exo capability endpoint
int endpoint_send(chan_t *c, exo_cap dest, const void *msg);
int endpoint_recv(chan_t *c, exo_cap src, void *msg);

// Helper macro to declare a typed channel wrapper
// Usage: CHAN_DECLARE(mychan, struct mymsg);
// Provides mychan_t type with create/send/recv functions
#define CHAN_DECLARE(name, type)                                    \
    typedef struct {                                                \
        chan_t base;                                                \
    } name##_t;                                                     \
    static inline name##_t *name##_create(void) {                   \
        return (name##_t *)chan_create(sizeof(type));               \
    }                                                               \
    static inline void name##_destroy(name##_t *c) {                 \
        chan_destroy(&c->base);                                     \
    }                                                               \
    static inline int name##_send(name##_t *c, exo_cap dest, const type *m){ \
        if(c->base.msg_size != sizeof(type)) return -1;             \
        return endpoint_send(&c->base, dest, m);                    \
    }                                                               \
    static inline int name##_recv(name##_t *c, exo_cap src, type *m){ \
        if(c->base.msg_size != sizeof(type)) return -1;             \
        return endpoint_recv(&c->base, src, m);                     \
    }

