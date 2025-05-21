#pragma once
#include "exo_mem.h"
#include "../exo.h"

struct proc;

struct ipc_endpoint {
  uint badge;
  struct proc *waiting;
};

extern char *exo_ipc_frame;
int exo_send(exo_cap dest, const void *buf, uint64_t len);
int exo_recv(exo_cap src, void *buf, uint64_t len);
