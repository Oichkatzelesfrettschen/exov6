#pragma once
#include <stdint.h>
#include "exo_mem.h"
#include "compiler_attrs.h"
#include "exo.h"

typedef enum {
  IPC_STATUS_SUCCESS = 0,
  IPC_STATUS_TIMEOUT,
  IPC_STATUS_AGAIN,
  IPC_STATUS_BADDEST,
} exo_ipc_status;

struct exo_ipc_ops {
  int (*send)(exo_cap dest, const void *buf, uint64_t len);
  int (*recv)(exo_cap src, void *buf, uint64_t len);
};

void exo_ipc_register(struct exo_ipc_ops *ops);
#if defined(EXO_KERNEL) || defined(EXO_USER_EXO_IPC_DECLS)
EXO_NODISCARD int exo_send(exo_cap dest, const void *buf, uint64_t len);
EXO_NODISCARD int exo_recv(exo_cap src, void *buf, uint64_t len);
EXO_NODISCARD int exo_recv_timed(exo_cap src, void *buf, uint64_t len,
                                 unsigned timeout);
#endif
