#include "kernel/exo_disk.h"
#include "defs.h"

int __attribute__((weak))
exo_read_disk(struct exo_blockcap cap, void *dst, uint64_t off, uint64_t n) {
    // TODO: implement disk read via capability
    (void)cap;
    (void)dst;
    (void)off;
    (void)n;
    return -1;
}

int __attribute__((weak))
exo_write_disk(struct exo_blockcap cap, const void *src, uint64_t off,
               uint64_t n) {
    // TODO: implement disk write via capability
    (void)cap;
    (void)src;
    (void)off;
    (void)n;
    return -1;
}
