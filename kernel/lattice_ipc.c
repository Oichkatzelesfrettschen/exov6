#include "lattice_ipc.h"
#include "caplib.h"
#include <string.h>
#include <stdatomic.h>

/**
 * @brief Establish a connection to a remote capability.
 */
int lattice_connect(lattice_channel_t *chan, exo_cap dest) {
  if (!chan) {
    return -1;
  }
  WITH_QLOCK(&chan->lock) {
    chan->cap = dest;
    atomic_store(&chan->seq, 0);
    memset(&chan->key, 0, sizeof(chan->key));
  }
  return 0;
}

/**
 * @brief Send a message over the channel.
 */
int lattice_send(lattice_channel_t *chan, const void *buf, size_t len) {
  if (!chan) {
    return -1;
  }
  int ret;
  WITH_QLOCK(&chan->lock) {
    ret = exo_send(chan->cap, buf, (uint64_t)len);
    if (ret == 0) {
      atomic_fetch_add(&chan->seq, 1);
    }
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
  int ret;
  WITH_QLOCK(&chan->lock) {
    ret = exo_recv(chan->cap, buf, (uint64_t)len);
    if (ret >= 0) {
      atomic_fetch_add(&chan->seq, 1);
    }
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
  WITH_QLOCK(&chan->lock) {
    chan->cap = 0;
    atomic_store(&chan->seq, 0);
    memset(&chan->key, 0, sizeof(chan->key));
  }
}

/**
 * @brief Yield the CPU to the remote endpoint if possible.
 */
int lattice_yield_to(const lattice_channel_t *chan) {
  if (!chan) {
    return -1;
  }
  exo_cap dest;
  WITH_QLOCK((quaternion_spinlock_t *)&chan->lock) { // cast away const for lock
    dest = chan->cap;
  }
  return cap_yield_to_cap(dest);
}
