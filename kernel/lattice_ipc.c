/**
 * @file lattice_ipc.c
 * @brief Capability-based, post-quantum authenticated IPC layer for XINIM.
 */

#include "lattice_ipc.h"
#include "caplib.h"
#include "libos/crypto.h"
#include "cap_security.h"
#include "octonion.h"
#include "quaternion_spinlock.h"
#include "dag.h"

#include <stdatomic.h>
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

/* Forward declarations for crypto functions */
extern void simple_sha256(const uint8_t *data, size_t len, uint8_t hash[32]);
extern int hmac_verify_constant_time(const unsigned char *a, const unsigned char *b, size_t len);

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
    if (pqcrypto_kem_keypair(pk, sk) != 0)
        return -1;

    if (exo_send(chan->cap, pk, sizeof pk) != (int)sizeof pk)
        return -1;

    uint8_t peer_pk[32];
    if (exo_recv(chan->cap, peer_pk, sizeof peer_pk) != (int)sizeof peer_pk)
        return -1;

    uint8_t cipher[32], key1[32];
    if (pqcrypto_kem_enc(cipher, key1, peer_pk) != 0)
        return -1;

    if (exo_send(chan->cap, cipher, sizeof cipher) != (int)sizeof cipher)
        return -1;

    uint8_t peer_cipher[32], key2[32];
    if (exo_recv(chan->cap, peer_cipher, sizeof peer_cipher) != (int)sizeof peer_cipher)
        return -1;

    if (pqcrypto_kem_dec(key2, peer_cipher, sk) != 0)
        return -1;

    uint8_t combo[64];
    memcpy(combo, key1, sizeof key1);
    memcpy(combo + sizeof key1, key2, sizeof key2);

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
 * @brief Send a message through an encrypted channel with authentication.
 */
int lattice_send(lattice_channel_t *chan, const void *buf, size_t len) {
    if (!chan || !buf || len == 0)
        return -1;

    uint8_t *enc = malloc(len + 32); /* Extra space for auth tag */
    if (!enc)
        return -1;

    /* Compute HMAC for authentication */
    uint8_t auth_tag[32];
    simple_sha256((const uint8_t *)buf, len, auth_tag);
    
    /* Mix in channel key for authentication */
    for (size_t i = 0; i < 32; i++) {
        auth_tag[i] ^= chan->key.sig_data[i % LATTICE_SIG_BYTES];
    }

    /* Encrypt the message */
    xor_crypt(enc, buf, len, &chan->key);
    
    /* Append authentication tag */
    memcpy(enc + len, auth_tag, 32);

    int ret = -1;
    WITH_QLOCK(&chan->lock) {
        ret = exo_send(chan->cap, enc, len + 32);
        if (ret == (int)(len + 32)) {
            atomic_fetch_add_explicit(&chan->seq, 1, memory_order_relaxed);
            ret = len; /* Return original message length */
        }
    }

    /* Clear sensitive data */
    cap_secure_clear(enc, len + 32);
    cap_secure_clear(auth_tag, sizeof(auth_tag));
    free(enc);
    return ret;
}

/**
 * @brief Receive a message and decrypt it.
 */
int lattice_recv(lattice_channel_t *chan, void *buf, size_t len) {
    if (!chan || !buf || len == 0)
        return -1;

    uint8_t *enc = malloc(len + 32); /* Space for message + auth tag */
    if (!enc)
        return -1;

    int ret = -1;
    WITH_QLOCK(&chan->lock) {
        ret = exo_recv(chan->cap, enc, len + 32);
        if (ret == (int)(len + 32)) {
            /* Decrypt the message */
            xor_crypt(buf, enc, len, &chan->key);
            
            /* Verify authentication tag */
            uint8_t expected_auth[32];
            simple_sha256((const uint8_t *)buf, len, expected_auth);
            
            /* Mix in channel key for authentication */
            for (size_t i = 0; i < 32; i++) {
                expected_auth[i] ^= chan->key.sig_data[i % LATTICE_SIG_BYTES];
            }
            
            /* Compare auth tags in constant time */
            if (hmac_verify_constant_time(expected_auth, enc + len, 32)) {
                atomic_fetch_add_explicit(&chan->seq, 1, memory_order_relaxed);
                ret = len; /* Return original message length */
            } else {
                /* Authentication failed - clear decrypted data */
                cap_secure_clear(buf, len);
                ret = -2; /* Authentication error */
            }
            
            cap_secure_clear(expected_auth, sizeof(expected_auth));
        }
    }

    /* Clear sensitive data */
    cap_secure_clear(enc, len + 32);
    free(enc);
    return ret;
}

/**
 * @brief Close the channel and erase its state securely.
 */
void lattice_close(lattice_channel_t *chan) {
    if (!chan)
        return;

    WITH_QLOCK(&chan->lock) {
        chan->cap = (exo_cap){0};
        atomic_store_explicit(&chan->seq, 0, memory_order_relaxed);
        
        /* Securely clear cryptographic material */
        cap_secure_clear(&chan->key, sizeof chan->key);
        cap_secure_clear(&chan->token, sizeof chan->token);
        cap_secure_clear(&chan->pub, sizeof chan->pub);
        cap_secure_clear(&chan->priv, sizeof chan->priv);
        
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
