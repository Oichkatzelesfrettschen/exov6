#pragma once
#include <stdatomic.h>
#include <stdint.h>
#include <stddef.h>

typedef uint32_t label_t;

typedef struct {
    uint64_t hi;
    uint64_t lo;
    label_t  label;
    uint32_t rights;
} cap_t;

typedef struct chan chan_t;

enum {
    CAP_RIGHT_RECV = 1u << 0,
    CAP_RIGHT_SEND = 1u << 1,
};

chan_t *k_chan_create(cap_t *out_cap, uint32_t rights, uint32_t flags);
int     k_chan_destroy(cap_t chan);

int     k_chan_send(cap_t chan, const void *buf, size_t len,
                    const cap_t *caps, size_t n_caps);

ssize_t k_chan_recv(cap_t chan, void *buf, size_t *inout_len,
                    cap_t *caps, size_t *inout_n_caps,
                    uint32_t flags);
