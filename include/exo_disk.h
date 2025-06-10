#pragma once
#include <stdint.h>
#include "exo_mem.h"
#include "exo.h"
#include <stdint.h>

EXO_NODISCARD int exo_read_disk(struct exo_blockcap cap, void *dst,
                                uint64_t off, uint64_t n);
EXO_NODISCARD int exo_write_disk(struct exo_blockcap cap, const void *src,
                                 uint64_t off, uint64_t n);
