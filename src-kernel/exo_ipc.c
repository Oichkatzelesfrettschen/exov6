#include "types.h"
#include "defs.h"
#include "exo_ipc.h"

static struct exo_ipc_ops ipc_ops;

void exo_ipc_register(struct exo_ipc_ops *ops) { ipc_ops = *ops; }

[[nodiscard]] int exo_send(exo_cap dest, const void *buf, uint64_t len) {
  if (ipc_ops.send)
    return ipc_ops.send(dest, buf, len);
  return -1;
}

[[nodiscard]] int exo_recv(exo_cap src, void *buf, uint64_t len) {
  if (ipc_ops.recv)
    return ipc_ops.recv(src, buf, len);
  return -1;
}

[[nodiscard]] int exo_recv_timed(exo_cap src, void *buf, uint64_t len,
                                 uint32_t timeout_ms) {
  if (ipc_ops.recv_timed)
    return ipc_ops.recv_timed(src, buf, len, timeout_ms);
  if (ipc_ops.recv)
    return ipc_ops.recv(src, buf, len);
  return -1;
}
