#pragma once
#include "exo_mem.h"
#include <stdint.h>

int exo_send(cap_t dest, const void *buf, uint64_t len);
int exo_recv(cap_t src, void *buf, uint64_t len);
