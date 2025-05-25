#include "fs.h"
#include "file.h"
#include "exokernel.h"
#include "sleeplock.h"
#include "spinlock.h"
#include "types.h"
#include "user.h"

// Simplified user-space filesystem stubs using exokernel disk primitives.

int fs_read_block(struct exo_blockcap cap, void *dst) {
  return exo_read_disk(cap, dst, 0, BSIZE);
}

int fs_write_block(struct exo_blockcap cap, const void *src) {
  return exo_write_disk(cap, src, 0, BSIZE);
}

int fs_alloc_block(uint dev, uint rights, struct exo_blockcap *cap) {
  return exo_alloc_block(dev, rights, cap);
}

int fs_bind_block(struct exo_blockcap *cap, void *data, int write) {
  return exo_bind_block(cap, data, write);
}
