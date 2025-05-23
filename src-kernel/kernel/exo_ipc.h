#pragma once
#include "types.h"
#include <exo_ipc.h>

void exo_ipc_register(struct exo_ipc_ops *ops);
int exo_send(exo_cap dest, const void *buf, uint64 len);
int exo_recv(exo_cap src, void *buf, uint64 len);

int exo_ipc_queue_send(exo_cap dest, const void *buf, uint64 len);
int exo_ipc_queue_recv(exo_cap src, void *buf, uint64 len);
extern struct exo_ipc_ops exo_ipc_queue_ops;
