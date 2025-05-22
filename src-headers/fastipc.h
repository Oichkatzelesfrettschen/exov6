#pragma once
#include "ipc.h"

// simple kernel-to-user message queue used by ipc_fast

#ifdef __cplusplus
extern "C" {
#endif

void fastipc_send(zipc_msg_t *m);
int sys_ipc_fast(void);

#ifdef __cplusplus
}
#endif
