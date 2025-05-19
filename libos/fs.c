#include "types.h"
#include "user.h"
#include "fs.h"
#include "sleeplock.h"
#include "spinlock.h"
#include "file.h"

// Simplified user-space filesystem stubs using exokernel disk primitives.

int
fs_read_block(struct exo_blockcap cap, void *dst)
{
    return exo_read_disk(cap, dst, 0, BSIZE);
}

int
fs_write_block(struct exo_blockcap cap, const void *src)
{
    return exo_write_disk(cap, src, 0, BSIZE);
}
