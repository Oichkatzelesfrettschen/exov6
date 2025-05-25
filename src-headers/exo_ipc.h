#pragma once
#include <stdint.h>
#include "exo_mem.h"
#include "../exo.h"

struct exo_ipc_ops {
  int (*send)(exo_cap dest, const void *buf, uint64_t len);
  int (*recv)(exo_cap src, void *buf, uint64_t len);
};


void exo_ipc_register(struct exo_ipc_ops *ops);
int exo_send(exo_cap dest, const void *buf, uint64_t len);
int exo_recv(exo_cap src, void *buf, uint64_t len);
