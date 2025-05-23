#pragma once
#include "types.h"
#include "exo.h"

int exo_read_disk(struct exo_blockcap cap, void *dst, uint64 off, uint64 n);
int exo_write_disk(struct exo_blockcap cap, const void *src, uint64 off,
                   uint64 n);
