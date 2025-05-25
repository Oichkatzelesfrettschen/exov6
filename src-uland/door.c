#include "door.h"
#include "exo_ipc.h"
#include <string.h>

static void clear_cap(exo_cap *c) { memset(c, 0, sizeof(*c)); }

door_t door_create_local(void (*handler)(zipc_msg_t *msg)) {
  door_t d;
  clear_cap(&d.dest);
  d.handler = handler;
  d.is_local = 1;
  return d;
}

door_t door_create_remote(exo_cap dest) {
  door_t d;
  d.dest = dest;
  d.handler = 0;
  d.is_local = 0;
  return d;
}

[[nodiscard]] exo_ipc_status door_call(door_t *d, zipc_msg_t *msg) {
  if (!d)
    return IPC_STATUS_ERROR;
  if (d->is_local) {
    if (d->handler)
      d->handler(msg);
    return IPC_STATUS_SUCCESS;
  }
  if (cap_send(d->dest, msg, sizeof(*msg)) != IPC_STATUS_SUCCESS)
    return IPC_STATUS_ERROR;
  return cap_recv(d->dest, msg, sizeof(*msg));
}

void door_server_loop(door_t *d) {
  if (!d || !d->handler)
    return;
  while (1) {
    zipc_msg_t msg;
    if (cap_recv(d->dest, &msg, sizeof(msg)) < 0)
      continue;
    d->handler(&msg);
    cap_send(d->dest, &msg, sizeof(msg));
  }
}
