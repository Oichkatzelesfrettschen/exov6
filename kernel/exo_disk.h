#pragma once
#include "exo_mem.h"
#include <stdint.h>

int exo_read_disk(cap_t cap, void *dst, uint64_t off, uint64_t n);
int exo_write_disk(cap_t cap, const void *src, uint64_t off, uint64_t n);
