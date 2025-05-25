#pragma once
#include <stdint.h>
#include "exo_mem.h"
#include "../exo.h"

enum exo_ipc_status {
  IPC_STATUS_SUCCESS = 0,
  IPC_STATUS_TIMEOUT,
  IPC_STATUS_AGAIN,
  IPC_STATUS_BADDEST,
};

struct exo_ipc_ops {
  enum exo_ipc_status (*send)(exo_cap dest, const void *buf, uint64_t len);
  enum exo_ipc_status (*recv)(exo_cap src, void *buf, uint64_t len);
};

void exo_ipc_register(struct exo_ipc_ops *ops);
[[nodiscard]] enum exo_ipc_status exo_send(exo_cap dest, const void *buf,
                                           uint64_t len);
[[nodiscard]] enum exo_ipc_status exo_recv(exo_cap src, void *buf, uint64_t len);
