#pragma once
#include "exo_ipc.h"

int ipc_queue_send(exo_cap dest, const void *buf, uint64_t len);
int ipc_queue_recv(exo_cap src, void *buf, uint64_t len);
