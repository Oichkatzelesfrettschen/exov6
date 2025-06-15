/*
 * @file lattice_ipc.c
 * @brief Capability‐based, post‐quantum stubbed IPC in C23.
 */

#include "lattice_ipc.h"
#include "caplib.h"
#include "libos/crypto.h"
#include "quaternion_spinlock.h" /* for WITH_QLOCK */
#include "octonion.h"
#include "dag.h"
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <stdatomic.h>

/*==============================================================================
 * Pseudo‐random generator (non‐crypto; stub only)
 *============================================================================*/
static uint32_t lcg_rand(void) {
  static uint32_t seed = 123456789u;
  seed = seed * 1103515245u + 12345u;
  return seed;
}

/*==============================================================================
 * XOR‐based symmetric cipher helper
 *============================================================================*/
static void xor_crypt(uint8_t *dst, const uint8_t *src, size_t len,
                      const lattice_sig_t *key) {
  for (size_t i = 0; i < len; ++i) {
    dst[i] = src[i] ^ key->sig_data[i % LATTICE_SIG_BYTES];
  }
}

/*==============================================================================
 * Simplified Kyber‐style key exchange stub
 *============================================================================*/
/**
 * @brief Exchange nonces and derive a shared secret via KDF.
 *
 * Sends a 32‐byte local nonce, receives peer nonce, then uses
 * libos_kdf_derive() to fill chan->key.sig_data.
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

  return libos_kdf_derive(local_nonce, sizeof local_nonce, remote_nonce,
                          sizeof remote_nonce, "kyber-stub", chan->key.sig_data,
                          sizeof chan->key.sig_data);
}

/*==============================================================================
 * Public API: connect, send, recv, close, yield
 *============================================================================*/
/**
 * @brief Establish a channel and perform post‐quantum stub exchange.
 */
int lattice_connect(lattice_channel_t *chan, exo_cap dest) {
  if (chan == NULL) {
    return -1;
  }

  WITH_QLOCK(&chan->lock) {
    chan->cap = dest;
    /* relaxed ordering is sufficient under the spinlock */
    atomic_store_explicit(&chan->seq, 0, memory_order_relaxed);
    memset(&chan->key, 0, sizeof chan->key);
    memset(&chan->token, 0, sizeof chan->token);
    dag_node_init(&chan->dag, dest);
  }

  int rc = kyber_stub_exchange(chan);
  if (rc == 0) {
    /* derive a simple octonion token from the key */
    double coeffs[8];
    for (size_t i = 0; i < 8; ++i)
      coeffs[i] = (double)chan->key.sig_data[i] / 255.0;
    chan->token = octonion_create(coeffs[0], coeffs[1], coeffs[2], coeffs[3],
                                  coeffs[4], coeffs[5], coeffs[6], coeffs[7]);
  }

  return rc;
}

/**
 * @brief Send a message (XOR‐encrypted + sequence bump).
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
      /* relaxed increment safe under spinlock */
      atomic_fetch_add_explicit(&chan->seq, 1, memory_order_relaxed);
    }
  }

  free(enc);
  return ret;
}

/**
 * @brief Receive a message (XOR‐decrypted + sequence bump).
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
      /* relaxed increment safe under spinlock */
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
  /* spinlock guards access to chan->cap */
  WITH_QLOCK((quaternion_spinlock_t *)&chan->lock) { dest = chan->cap; }
  return cap_yield_to_cap(dest);
}

int lattice_channel_add_dep(lattice_channel_t *parent,
                            lattice_channel_t *child) {
  if (parent == NULL || child == NULL) {
    return -1;
  }
  return dag_add_edge(&parent->dag, &child->dag);
}

int lattice_channel_submit(lattice_channel_t *chan) {
  if (chan == NULL) {
    return -1;
  }
  return dag_sched_submit(&chan->dag);
}
