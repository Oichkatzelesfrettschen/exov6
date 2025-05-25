#pragma once
#include "types.h"
#include "file.h"
#include "fs.h"
#include "defs.h"
#include "exokernel.h"

int fs_read_block(struct exo_blockcap cap, void *dst);
int fs_write_block(struct exo_blockcap cap, const void *src);
int fs_alloc_block(uint dev, uint rights, struct exo_blockcap *cap);
int fs_bind_block(struct exo_blockcap *cap, void *data, int write);
