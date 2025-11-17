/**
 * @file lattice_ipc.c
 * @brief Capability-based, post-quantum authenticated IPC layer for XINIM.
 */

#include "lattice_ipc.h"
#include "caplib.h"
#include "libos/crypto.h"
#include "octonion.h"
#include "quaternion_spinlock.h"  /* Fixed path - include/ already in search path */
#include "dag.h"

#include <stdatomic.h>
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

#ifndef EXO_KERNEL
int cap_yield_to_cap(exo_cap dest) { (void)dest; return 0; }
int libos_kdf_derive(const uint8_t *salt, size_t salt_len, const uint8_t *ikm,
                     size_t ikm_len, const char *info, uint8_t *okm,
                     size_t okm_len) {
    (void)salt; (void)salt_len; (void)info;
    if (!okm || !ikm || okm_len == 0 || ikm_len == 0) return -1;
    /* trivial xor stub for host build */
    for (size_t i = 0; i < okm_len; ++i) okm[i] = ikm[i % ikm_len] ^ (uint8_t)i;
    return 0;
}
int pqcrypto_kem_keypair(uint8_t *pk, uint8_t *sk) {
    for (size_t i = 0; i < 32; ++i) { pk[i] = (uint8_t)(i+1); sk[i] = (uint8_t)(i+2);} return 0; }
int pqcrypto_kem_enc(uint8_t *cipher, uint8_t *key, const uint8_t *pk) {
    (void)pk; for (size_t i = 0; i < 32; ++i) { key[i] = (uint8_t)(i+3); cipher[i]= (uint8_t)(key[i]^0xAA);} return 0; }
int pqcrypto_kem_dec(uint8_t *key, const uint8_t *cipher, const uint8_t *sk) {
    (void)sk; for (size_t i = 0; i < 32; ++i) key[i] = (uint8_t)(cipher[i]^0xAA); return 0; }
#endif

/*------------------------------------------------------------------------------
 * Symmetric XOR stream cipher
 *----------------------------------------------------------------------------*/
static void xor_crypt(uint8_t *dst, const uint8_t *src, size_t len,
                      const lattice_sig_t *key) {
    for (size_t i = 0; i < len; ++i) {
        dst[i] = src[i] ^ key->sig_data[i % LATTICE_SIG_BYTES];
    }
}

/*------------------------------------------------------------------------------
 * Post-quantum Kyber-based key exchange via pqcrypto
 *----------------------------------------------------------------------------*/
static int kyber_pqcrypto_exchange(lattice_channel_t *chan) {
    uint8_t pk[32], sk[32];
    // TODO: Replace pqcrypto_kem_keypair with a robust, audited post-quantum crypto library implementation.
    if (pqcrypto_kem_keypair(pk, sk) != 0)
        return -1;

    // TODO: Add robust error handling for exo_send/exo_recv, including timeouts and retry mechanisms.
    if (exo_send(chan->cap, pk, sizeof pk) != (int)sizeof pk)
        return -1;

    uint8_t peer_pk[32];
    if (exo_recv(chan->cap, peer_pk, sizeof peer_pk) != (int)sizeof peer_pk)
        return -1;

    uint8_t cipher[32], key1[32];
    // TODO: Replace pqcrypto_kem_enc with a robust, audited post-quantum crypto library implementation.
    if (pqcrypto_kem_enc(cipher, key1, peer_pk) != 0)
        return -1;

    if (exo_send(chan->cap, cipher, sizeof cipher) != (int)sizeof cipher)
        return -1;

    uint8_t peer_cipher[32], key2[32];
    if (exo_recv(chan->cap, peer_cipher, sizeof peer_cipher) != (int)sizeof peer_cipher)
        return -1;

    // TODO: Replace pqcrypto_kem_dec with a robust, audited post-quantum crypto library implementation.
    if (pqcrypto_kem_dec(key2, peer_cipher, sk) != 0)
        return -1;

    uint8_t combo[64];
    memcpy(combo, key1, sizeof key1);
    memcpy(combo + sizeof key1, key2, sizeof key2);

    // TODO: Replace libos_kdf_derive with a robust, audited KDF implementation.
    return libos_kdf_derive(NULL, 0, combo, sizeof combo, "kyber",
                            chan->key.sig_data, sizeof chan->key.sig_data);
}

/*------------------------------------------------------------------------------
 * Public API
 *----------------------------------------------------------------------------*/

/**
 * @brief Establish a channel and perform Kyber-based key exchange.
 */
int lattice_connect(lattice_channel_t *chan, exo_cap dest) {
    if (!chan)
        return -1;

    WITH_QLOCK(&chan->lock) {
        chan->cap = dest;
        atomic_store_explicit(&chan->seq, 0, memory_order_relaxed);
        memset(&chan->key, 0, sizeof chan->key);
        memset(&chan->token, 0, sizeof chan->token);
        dag_node_init(&chan->dag, dest);
    }

    int rc = kyber_pqcrypto_exchange(chan);
    if (rc == 0) {
        double coeffs[8];
        for (size_t i = 0; i < 8; ++i)
            coeffs[i] = (double)chan->key.sig_data[i] / 255.0;
        chan->token = octonion_create(coeffs[0], coeffs[1], coeffs[2], coeffs[3],
                                      coeffs[4], coeffs[5], coeffs[6], coeffs[7]);
    }
    return rc;
}

/**
 * @brief Send a message through an encrypted channel.
 */
int lattice_send(lattice_channel_t *chan, const void *buf, size_t len) {
    if (!chan || !buf || len == 0)
        return -1;

    uint8_t *enc = malloc(len);
    if (!enc)
        return -1; // TODO: Handle memory allocation failure more robustly.

    xor_crypt(enc, buf, len, &chan->key);

    int ret = -1;
    WITH_QLOCK(&chan->lock) {
        // TODO: Add robust error handling for exo_send, including timeouts and retry mechanisms.
        ret = exo_send(chan->cap, enc, len);
        if (ret == (int)len)
            atomic_fetch_add_explicit(&chan->seq, 1, memory_order_relaxed);
    }

    free(enc);
    return ret;
}

/**
 * @brief Receive a message and decrypt it.
 */
int lattice_recv(lattice_channel_t *chan, void *buf, size_t len) {
    if (!chan || !buf || len == 0)
        return -1;

    uint8_t *enc = malloc(len);
    if (!enc)
        return -1; // TODO: Handle memory allocation failure more robustly.

    int ret = -1;
    WITH_QLOCK(&chan->lock) {
        // TODO: Add robust error handling for exo_recv, including timeouts and retry mechanisms.
        ret = exo_recv(chan->cap, enc, len);
        if (ret == (int)len) {
            xor_crypt(buf, enc, ret, &chan->key);
            atomic_fetch_add_explicit(&chan->seq, 1, memory_order_relaxed);
        }
    }

    free(enc);
    return ret;
}

/**
 * @brief Close the channel and erase its state.
 */
void lattice_close(lattice_channel_t *chan) {
    if (!chan)
        return;

    WITH_QLOCK(&chan->lock) {
        chan->cap = (exo_cap){0};
        atomic_store_explicit(&chan->seq, 0, memory_order_relaxed);
        memset(&chan->key, 0, sizeof chan->key);
        memset(&chan->token, 0, sizeof chan->token);
        memset(&chan->dag, 0, sizeof chan->dag);
    }
}

/**
 * @brief Yield control to the peer endpoint associated with the channel.
 */
int lattice_yield_to(const lattice_channel_t *chan) {
    if (!chan)
        return -1;

    exo_cap dest;
    WITH_QLOCK((quaternion_spinlock_t *)&chan->lock) {
        dest = chan->cap;
    }
    return cap_yield_to_cap(dest);
}

/**
 * @brief Declare a dependency edge between two lattice channels.
 */
int lattice_channel_add_dep(lattice_channel_t *parent,
                            lattice_channel_t *child) {
    if (!parent || !child)
        return -1;
    return dag_add_edge(&parent->dag, &child->dag);
}

/**
 * @brief Submit a lattice channel’s DAG node for scheduling.
 */
int lattice_channel_submit(lattice_channel_t *chan) {
    if (!chan)
        return -1;
    return dag_sched_submit(&chan->dag);
}
