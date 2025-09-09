#pragma once

/**
 * @file chan.h
 * @brief Type-safe channel interface for exokernel IPC
 * 
 * Legacy compatibility layer over unified channel system.
 * New code should use unified_chan.h directly.
 */

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include "types.h"
#include "exo.h"
#include "unified_chan.h"

/* Legacy compatibility types */
typedef unified_chan_t chan_t;
typedef msg_type_desc_t msg_type_desc;

/* Legacy compatibility functions */
static inline chan_t *chan_create(const struct msg_type_desc *desc) {
    return unified_chan_create(desc, CHAN_FIXED);
}

static inline void chan_destroy(chan_t *c) {
    unified_chan_destroy(c);
}

static inline int chan_endpoint_send(chan_t *c, exo_cap dest, const void *msg, size_t len) {
    return unified_chan_send(c, dest, msg, len);
}

static inline int chan_endpoint_recv(chan_t *c, exo_cap src, void *msg, size_t len) {
    return unified_chan_recv(c, src, msg, len);
}

/* Legacy macro - now redirects to unified system */
#define CHAN_DECLARE(name, type) \
    UNIFIED_CHAN_DECLARE(name, type, CHAN_FIXED)

/* Compile-time assertions - adjusted for current implementation */
_Static_assert(sizeof(chan_t) <= 128, "Channel descriptor too large");
_Static_assert(_Alignof(chan_t) >= 8, "Channel must be properly aligned");