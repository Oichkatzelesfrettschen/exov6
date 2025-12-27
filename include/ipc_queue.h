#pragma once

#include "exo_ipc.h"

struct mailbox;
extern struct mailbox ipcs;
void ipc_timed_init(void);

/* Queue-based IPC operations for exo_send/exo_recv.
 * Register with: exo_ipc_register(&exo_ipc_queue_ops); */
extern struct exo_ipc_ops exo_ipc_queue_ops;
