#pragma once
#ifdef __cplusplus
extern "C" {
#endif
#include <stdint.h>
#include "exo_mem.h"
#include "../exo.h"
#include <stdint.h>

int exo_read_disk(struct exo_blockcap cap, void *dst, uint64_t off, uint64_t n);
int exo_write_disk(struct exo_blockcap cap, const void *src, uint64_t off,
                   uint64_t n);
#ifdef __cplusplus
}
#endif
