#include "door.h"
#include "exo_ipc.h"
#include <stddef.h>

/**
 * @file door.c
 * @brief Implementation of the door IPC abstraction.
 */

/**
 * @brief Zero a capability structure.
 *
 * This helper clears @p c to prevent leaking uninitialized bits.
 */
static void clear_cap(exo_cap *c) {
  unsigned char *p = (unsigned char *)c;
  for (size_t i = 0; i < sizeof(*c); i++)
    p[i] = 0;
}

/**
 * @brief Construct a door that directly invokes @p handler.
 */
door_t door_create_local(void (*handler)(zipc_msg_t *msg)) {
  door_t d;
  clear_cap(&d.dest);
  d.handler = handler;
  d.is_local = 1;
  return d;
}

/**
 * @brief Construct a door that forwards requests to @p dest.
 */
door_t door_create_remote(exo_cap dest) {
  door_t d;
  d.dest = dest;
  d.handler = 0;
  d.is_local = 0;
  return d;
}

/**
 * @brief Call a door using the provided message.
 */
EXO_NODISCARD int door_call(door_t *d, zipc_msg_t *msg) {
  if (!d)
    return -1;
  if (d->is_local) {
    if (d->handler)
      d->handler(msg);
    return 0;
  }
  if (cap_send(d->dest, msg, sizeof(*msg)) != IPC_STATUS_SUCCESS)
    return -1;
  if (cap_recv(d->dest, msg, sizeof(*msg)) != IPC_STATUS_SUCCESS)
    return -1;
  return 0;
}

/**
 * @brief Run a blocking service loop for a door.
 */
void door_server_loop(door_t *d) {
  if (!d || !d->handler)
    return;
  while (1) {
    zipc_msg_t msg;
    if (cap_recv(d->dest, &msg, sizeof(msg)) < 0)
      continue;
    d->handler(&msg);
    (void)cap_send(d->dest, &msg, sizeof(msg));
  }
}

/**
 * @brief Send a message without waiting for the reply.
 */
EXO_NODISCARD int door_call_async(door_t *d, const zipc_msg_t *msg) {
  if (!d || d->is_local)
    return -1;
  return cap_send(d->dest, msg, sizeof(*msg)) == IPC_STATUS_SUCCESS ? 0 : -1;
}

/**
 * @brief Receive a pending message on a door.
 */
EXO_NODISCARD int door_recv(door_t *d, zipc_msg_t *msg) {
  if (!d)
    return -1;
  return cap_recv(d->dest, msg, sizeof(*msg)) == IPC_STATUS_SUCCESS ? 0 : -1;
}

/**
 * @brief Send a reply for a previously received message.
 */
EXO_NODISCARD int door_reply(door_t *d, const zipc_msg_t *msg) {
  if (!d)
    return -1;
  return cap_send(d->dest, msg, sizeof(*msg)) == IPC_STATUS_SUCCESS ? 0 : -1;
}
