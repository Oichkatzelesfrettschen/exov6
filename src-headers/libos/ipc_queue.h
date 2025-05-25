#pragma once
#ifdef __cplusplus
extern "C" {
#endif
#include "exo_ipc.h"

int ipc_queue_send(exo_cap dest, const void *buf, uint64_t len);
int ipc_queue_recv(exo_cap src, void *buf, uint64_t len);
#ifdef __cplusplus
}
#endif
