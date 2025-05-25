#pragma once
#include "exo_ipc.h"

enum exo_ipc_status ipc_queue_send(exo_cap dest, const void *buf, uint64_t len);
enum exo_ipc_status ipc_queue_recv(exo_cap src, void *buf, uint64_t len);
