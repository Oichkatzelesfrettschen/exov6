#pragma once
#include <stdint.h>
#include "exo_mem.h"
#include "../exo.h"

typedef enum {
  IPC_STATUS_SUCCESS = 0,
  IPC_STATUS_TIMEOUT,
  IPC_STATUS_AGAIN,
  IPC_STATUS_BADDEST,
  IPC_STATUS_ERROR = -1
} exo_ipc_status;

struct exo_ipc_ops {
  exo_ipc_status (*send)(exo_cap dest, const void *buf, uint64_t len);
  exo_ipc_status (*recv)(exo_cap src, void *buf, uint64_t len);
};

void exo_ipc_register(struct exo_ipc_ops *ops);
[[nodiscard]] exo_ipc_status exo_send(exo_cap dest, const void *buf, uint64_t len);
[[nodiscard]] exo_ipc_status exo_recv(exo_cap src, void *buf, uint64_t len);
