#include <stdint.h>
#include <string.h>
#include "exo.h"

#define STUB_BLOCKS 128
#define BSIZE 512

static unsigned char disk[STUB_BLOCKS * BSIZE];
static uint32_t next_block;

int exo_alloc_page(exo_cap *cap) {
    static uint32_t next_page = 1;
    if (!cap) return -1;
    cap->pa = next_page * 0x1000;
    cap->id = next_page++;
    cap->rights = 0;
    cap->owner = 1;
    return 0;
}

int exo_unbind_page(exo_cap c) {
    (void)c;
    return 0;
}

int exo_alloc_block(uint32_t dev, uint32_t rights, exo_blockcap *cap) {
    (void)dev;
    if (!cap) return -1;
    cap->dev = 1;
    cap->blockno = next_block++;
    cap->rights = rights;
    cap->owner = 1;
    return 0;
}

int exo_bind_block(exo_blockcap *cap, void *data, int write) {
    if (!cap || cap->blockno >= STUB_BLOCKS || !data) return -1;
    unsigned char *slot = disk + cap->blockno * BSIZE;
    if (write)
        memcpy(slot, data, BSIZE);
    else
        memcpy(data, slot, BSIZE);
    return 0;
}

int exo_read_disk(exo_blockcap cap, void *dst, uint64_t off, uint64_t n) {
    if (cap.blockno >= STUB_BLOCKS || !dst) return -1;
    if (off + n > BSIZE) return -1;
    memcpy(dst, disk + cap.blockno * BSIZE + off, n);
    return (int)n;
}

int exo_write_disk(exo_blockcap cap, const void *src, uint64_t off, uint64_t n) {
    if (cap.blockno >= STUB_BLOCKS || !src) return -1;
    if (off + n > BSIZE) return -1;
    memcpy(disk + cap.blockno * BSIZE + off, src, n);
    return (int)n;
}

