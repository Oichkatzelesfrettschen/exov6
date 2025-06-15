#include "lattice_ipc.h"
#include "caplib.h"
#include "libos/crypto.h"
#include "quaternion_spinlock.h"  /* for WITH_QLOCK */
#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <stdatomic.h>

/*==============================================================================
 * Pseudo-random generator (not crypto-secure; for stub only)
 *============================================================================*/
static uint32_t lcg_rand(void) {
    static uint32_t seed = 123456789u;
    seed = seed * 1103515245u + 12345u;
    return seed;
}

/*==============================================================================
 * XOR-based symmetric cipher helper
 *============================================================================*/
static void xor_crypt(uint8_t *dst,
                      const uint8_t *src,
                      size_t len,
                      const lattice_sig_t *key)
{
    for (size_t i = 0; i < len; ++i) {
        dst[i] = src[i] ^ key->sig_data[i % LATTICE_SIG_BYTES];
    }
}

/*==============================================================================
 * Simplified Kyber-style key exchange stub
 *============================================================================*/
static int kyber_stub_exchange(lattice_channel_t *chan) {
    uint8_t local_nonce[32];
    for (size_t i = 0; i < sizeof local_nonce; ++i) {
        local_nonce[i] = (uint8_t)lcg_rand();
    }

    if (exo_send(chan->cap, local_nonce, sizeof local_nonce) !=
        (int)sizeof local_nonce) {
        return -1;
    }

    uint8_t remote_nonce[32];
    if (exo_recv(chan->cap, remote_nonce, sizeof remote_nonce) !=
        (int)sizeof remote_nonce) {
        return -1;
    }

    return libos_kdf_derive(
        local_nonce,   sizeof local_nonce,
        remote_nonce,  sizeof remote_nonce,
        "kyber-stub",
        chan->key.sig_data,
        sizeof chan->key.sig_data
    );
}

/*==============================================================================
 * Public API: connect, send, recv, close, yield
 *============================================================================*/

/**
 * @brief Establish a channel and perform post-quantum stub exchange.
 * @param chan  Pointer to channel descriptor (must be non-NULL).
 * @param dest  Destination capability.
 * @return 0 on success, –1 on error.
 */
int lattice_connect(lattice_channel_t *chan, exo_cap dest) {
    if (!chan) {
        return -1;
    }

    WITH_QLOCK(&chan->lock) {
        chan->cap = dest;
        atomic_store(&chan->seq, 0);
        memset(&chan->key, 0, sizeof chan->key);
    }

    return kyber_stub_exchange(chan);
}

/**
 * @brief Send a message over the channel (XOR-encrypted + sequence bump).
 */
int lattice_send(lattice_channel_t *chan, const void *buf, size_t len) {
    if (!chan) {
        return -1;
    }

    uint8_t enc[len];
    xor_crypt(enc, buf, len, &chan->key);

    int ret;
    WITH_QLOCK(&chan->lock) {
        ret = exo_send(chan->cap, enc, (uint64_t)len);
        if (ret > 0) {
            atomic_fetch_add(&chan->seq, 1);
        }
    }
    return ret;
}

/**
 * @brief Receive a message from the channel (XOR-decrypted + sequence bump).
 */
int lattice_recv(lattice_channel_t *chan, void *buf, size_t len) {
    if (!chan) {
        return -1;
    }

    uint8_t enc[len];
    int ret;
    WITH_QLOCK(&chan->lock) {
        ret = exo_recv(chan->cap, enc, (uint64_t)len);
        if (ret >= 0) {
            xor_crypt((uint8_t *)buf, enc, (size_t)ret, &chan->key);
            atomic_fetch_add(&chan->seq, 1);
        }
    }
    return ret;
}

/**
 * @brief Close a previously opened channel, zeroing state.
 */
void lattice_close(lattice_channel_t *chan) {
    if (!chan) {
        return;
    }

    WITH_QLOCK(&chan->lock) {
        chan->cap = 0;
        atomic_store(&chan->seq, 0);
        memset(&chan->key, 0, sizeof chan->key);
    }
}

/**
 * @brief Yield the CPU to the channel’s remote endpoint.
 * @return 0 on success, negative on failure.
 */
int lattice_yield_to(const lattice_channel_t *chan) {
    if (!chan) {
        return -1;
    }

    exo_cap dest;
    /* cast away const for locking */
    WITH_QLOCK((quaternion_spinlock_t *)&chan->lock) {
        dest = chan->cap;
    }
    return cap_yield_to_cap(dest);
}
