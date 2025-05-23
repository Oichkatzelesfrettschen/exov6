#pragma once
#include "exo.h"

int exo_send(exo_cap dest, const void *buf, uint64_t len);
int exo_recv(exo_cap src, void *buf, uint64_t len);

struct exo_ipc_ops {
  int (*send)(exo_cap dest, const void *buf, uint64_t len);
  int (*recv)(exo_cap src, void *buf, uint64_t len);
};

extern struct exo_ipc_ops exo_ipc_queue_ops;

void exo_ipc_register(struct exo_ipc_ops *ops);
