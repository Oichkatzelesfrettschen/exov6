#pragma once
#include <stddef.h>
#include "caplib.h"

exo_cap capwrap_alloc_page(void);
enum exo_ipc_status capwrap_send(exo_cap dest, const void *buf, size_t len);
enum exo_ipc_status capwrap_recv(exo_cap src, void *buf, size_t len);
