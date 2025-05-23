#include "types.h"
#include "defs.h"
#include "exo_ipc.h"

static struct exo_ipc_ops ipc_ops;

void exo_ipc_register(struct exo_ipc_ops *ops) { ipc_ops = *ops; }

int exo_send(exo_cap dest, const void *buf, uint64_t len) {
  if (ipc_ops.send)
    return ipc_ops.send(dest, buf, len);
  return -1;
}

int exo_recv(exo_cap src, void *buf, uint64_t len) {
  if (ipc_ops.recv)
    return ipc_ops.recv(src, buf, len);
  return -1;
}
