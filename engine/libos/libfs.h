#pragma once
#include "fs.h"
#include "file.h"

int fs_read_block(struct exo_blockcap cap, void *dst);
int fs_write_block(struct exo_blockcap cap, const void *src);
