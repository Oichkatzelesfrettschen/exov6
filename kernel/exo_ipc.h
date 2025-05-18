#pragma once
#include "exo_mem.h"
#include <stdint.h>

int exo_send(exo_cap dest, const void *buf, uint64_t len);
int exo_recv(exo_cap src, void *buf, uint64_t len);
