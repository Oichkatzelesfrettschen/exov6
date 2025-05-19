#pragma once
#include "exo_mem.h"
#include "../stdint.h"
#include "../exo.h"

int exo_read_disk(exo_cap cap, void *dst, uint64_t off, uint64_t n);
int exo_write_disk(exo_cap cap, const void *src, uint64_t off, uint64_t n);
