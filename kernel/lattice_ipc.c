#include "lattice_ipc.h"
#include "caplib.h"
#include "libos/crypto.h"
#include <string.h>
#include <stdint.h>

/**
 * @brief Pseudo random generator reused from qspinlock.c.
 *
 * This is not cryptographically secure but suffices for key
 * exchange stubbing.  A real implementation would use a true
 * random source.
 */
static uint32_t lcg_rand(void) {
    static uint32_t seed = 123456789u;
    seed = seed * 1103515245u + 12345u;
    return seed;
}

/**
 * @brief XOR-based symmetric encryption/decryption helper.
 */
static void xor_crypt(uint8_t *dst, const uint8_t *src, size_t len,
                      const lattice_sig_t *key) {
    for (size_t i = 0; i < len; ++i) {
        dst[i] = src[i] ^ key->sig_data[i % LATTICE_SIG_BYTES];
    }
}

/**
 * @brief Perform a simplified Kyber-like key exchange.
 *
 * The function exchanges two 32 byte nonces with the peer and
 * derives a shared secret using the stub KDF.  The resulting
 * secret is stored directly in ``chan->key``.
 *
 * @param chan Initialized channel descriptor.
 * @return 0 on success, negative value on failure.
 */
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

    return libos_kdf_derive(local_nonce, sizeof local_nonce,
                            remote_nonce, sizeof remote_nonce,
                            "kyber-stub",
                            chan->key.sig_data,
                            sizeof chan->key.sig_data);
}

/**
 * @brief Establish a connection to a remote capability.
 */
int lattice_connect(lattice_channel_t *chan, exo_cap dest) {
    if (!chan) {
        return -1;
    }

    chan->cap = dest;
    chan->seq = 0;
    memset(&chan->key, 0, sizeof(chan->key));

    return kyber_stub_exchange(chan);
}

/**
 * @brief Send a message over the channel.
 */
int lattice_send(lattice_channel_t *chan, const void *buf, size_t len) {
    if (!chan) {
        return -1;
    }

    uint8_t enc[len];
    xor_crypt(enc, buf, len, &chan->key);

    int ret = exo_send(chan->cap, enc, (uint64_t)len);
    if (ret == 0) {
        chan->seq++;
    }
    return ret;
}

/**
 * @brief Receive a message from the channel.
 */
int lattice_recv(lattice_channel_t *chan, void *buf, size_t len) {
    if (!chan) {
        return -1;
    }

    uint8_t enc[len];
    int ret = exo_recv(chan->cap, enc, (uint64_t)len);
    if (ret >= 0) {
        xor_crypt(buf, enc, (size_t)ret, &chan->key);
        chan->seq++;
    }
    return ret;
}

/**
 * @brief Close a previously opened channel.
 */
void lattice_close(lattice_channel_t *chan) {
    if (!chan) {
        return;
    }
    chan->cap = 0;
    chan->seq = 0;
    memset(&chan->key, 0, sizeof(chan->key));
}

/**
 * @brief Yield the CPU to the remote endpoint if possible.
 */
int lattice_yield_to(const lattice_channel_t *chan) {
    if (!chan) {
        return -1;
    }
    return cap_yield_to_cap(chan->cap);
}


