/*
 * @file lattice_ipc.c
 * @brief Capability-based, post-quantum stubbed IPC in C23.
 */

#include "lattice_ipc.h"
#include "caplib.h"
#include "libos/crypto.h"
#include "octonion.h"
#include "quaternion_spinlock.h" /* for WITH_QLOCK */
#include "dag.h"

#include <stdatomic.h>
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

/*------------------------------------------------------------------------------
 * Pseudo-random generator (non-crypto stub)
 *----------------------------------------------------------------------------*/

/*------------------------------------------------------------------------------
 * XOR-based symmetric cipher helper
 *----------------------------------------------------------------------------*/
static void xor_crypt(uint8_t *dst, const uint8_t *src, size_t len,
                      const lattice_sig_t *key) {
  for (size_t i = 0; i < len; ++i) {
    dst[i] = src[i] ^ key->sig_data[i % LATTICE_SIG_BYTES];
  }
}

/**
 * @brief Perform a Kyber key exchange via pqcrypto helpers.
 *
 * Each endpoint generates a key pair, exchanges public keys,
 * encapsulates a secret for the peer, and decapsulates the
 * received ciphertext. Both halves are concatenated and fed
 * through the libOS KDF to populate ``chan->key``.
 *
 * @param chan Channel with capability for transport.
 * @return 0 on success, -1 on failure.
 */
static int kyber_pqcrypto_exchange(lattice_channel_t *chan) {
  uint8_t pk[32];
  uint8_t sk[32];
  if (pqcrypto_kem_keypair(pk, sk) != 0) {
    return -1;
  }

  if (exo_send(chan->cap, pk, sizeof pk) != (int)sizeof pk) {
    return -1;
  }

  uint8_t peer_pk[32];
  if (exo_recv(chan->cap, peer_pk, sizeof peer_pk) != (int)sizeof peer_pk) {
    return -1;
  }

  uint8_t cipher[32];
  uint8_t key1[32];
  if (pqcrypto_kem_enc(cipher, key1, peer_pk) != 0) {
    return -1;
  }
  if (exo_send(chan->cap, cipher, sizeof cipher) != (int)sizeof cipher) {
    return -1;
  }

  uint8_t peer_cipher[32];
  if (exo_recv(chan->cap, peer_cipher, sizeof peer_cipher) !=
      (int)sizeof peer_cipher) {
    return -1;
  }
  uint8_t key2[32];
  if (pqcrypto_kem_dec(key2, peer_cipher, sk) != 0) {
    return -1;
  }

  uint8_t combo[64];
  memcpy(combo, key1, sizeof key1);
  memcpy(combo + sizeof key1, key2, sizeof key2);
  return libos_kdf_derive(NULL, 0, combo, sizeof combo, "kyber",
                          chan->key.sig_data, sizeof chan->key.sig_data);
}

/*==============================================================================
 * Public API: connect, send, recv, close, yield, DAG integration
 *============================================================================*/

/**
 * @brief Establish a channel and perform post-quantum stub exchange.
 */
int lattice_connect(lattice_channel_t *chan, exo_cap dest) {
  if (chan == NULL) {
    return -1;
  }

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
    for (size_t i = 0; i < 8; ++i) {
      coeffs[i] = (double)chan->key.sig_data[i] / 255.0;
    }
    chan->token = octonion_create(coeffs[0], coeffs[1], coeffs[2], coeffs[3],
                                  coeffs[4], coeffs[5], coeffs[6], coeffs[7]);
  }
  return rc;
}

/**
 * @brief Send a message (XOR-encrypted + sequence bump).
 */
int lattice_send(lattice_channel_t *chan, const void *buf, size_t len) {
  if (chan == NULL || buf == NULL) {
    return -1;
  }

  uint8_t *enc = malloc(len);
  if (enc == NULL) {
    return -1;
  }

  xor_crypt(enc, buf, len, &chan->key);

  int ret;
  WITH_QLOCK(&chan->lock) {
    ret = exo_send(chan->cap, enc, (uint64_t)len);
    if (ret == (int)len) {
      atomic_fetch_add_explicit(&chan->seq, 1, memory_order_relaxed);
    }
  }

  free(enc);
  return ret;
}

/**
 * @brief Receive a message (XOR-decrypted + sequence bump).
 */
int lattice_recv(lattice_channel_t *chan, void *buf, size_t len) {
  if (chan == NULL || buf == NULL) {
    return -1;
  }

  uint8_t *enc = malloc(len);
  if (enc == NULL) {
    return -1;
  }

  int ret;
  WITH_QLOCK(&chan->lock) {
    ret = exo_recv(chan->cap, enc, (uint64_t)len);
    if (ret == (int)len) {
      xor_crypt((uint8_t *)buf, enc, (size_t)ret, &chan->key);
      atomic_fetch_add_explicit(&chan->seq, 1, memory_order_relaxed);
    }
  }

  free(enc);
  return ret;
}

/**
 * @brief Close a channel, zeroing its state.
 */
void lattice_close(lattice_channel_t *chan) {
  if (chan == NULL) {
    return;
  }

  WITH_QLOCK(&chan->lock) {
    chan->cap = (exo_cap){0};
    atomic_store_explicit(&chan->seq, 0, memory_order_relaxed);
    memset(&chan->key, 0, sizeof chan->key);
    memset(&chan->token, 0, sizeof chan->token);
    memset(&chan->dag, 0, sizeof chan->dag);
  }
}

/**
 * @brief Yield the CPU to the channel’s remote endpoint.
 */
int lattice_yield_to(const lattice_channel_t *chan) {
  if (chan == NULL) {
    return -1;
  }

  exo_cap dest;
  WITH_QLOCK(&chan->lock) { dest = chan->cap; }
  return cap_yield_to_cap(dest);
}

/**
 * @brief Add a dependency edge between two channels.
 */
int lattice_channel_add_dep(lattice_channel_t *parent,
                            lattice_channel_t *child) {
  if (parent == NULL || child == NULL) {
    return -1;
  }
  return dag_add_edge(&parent->dag, &child->dag);
}

/**
 * @brief Submit a channel’s DAG node to the scheduler.
 */
int lattice_channel_submit(lattice_channel_t *chan) {
  if (chan == NULL) {
    return -1;
  }
  return dag_sched_submit(&chan->dag);
}
