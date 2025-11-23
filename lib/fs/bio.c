/**
 * @file bio.c
 * @brief Block I/O Layer (Phase 8)
 *
 * Simple synchronous block cache for the user-space file system.
 * Version 1: No caching, just alloc/read/free.
 * Future versions can add LRU caching.
 */

#include "include/fs.h"
#include "../virtio/virtio.h"

// Forward declarations
extern void print(const char *s);
extern void print_hex(uint64_t n);

// Simple memory pool for buffers (avoid malloc for now)
#define NBUF 16
static struct buf buf_pool[NBUF];
static int buf_used[NBUF];

/**
 * Allocate a buffer from the pool
 */
static struct buf* buf_alloc(void) {
    for (int i = 0; i < NBUF; i++) {
        if (!buf_used[i]) {
            buf_used[i] = 1;
            buf_pool[i].valid = 0;
            buf_pool[i].dirty = 0;
            return &buf_pool[i];
        }
    }
    print("[BIO] ERROR: No free buffers!\n");
    return 0;
}

/**
 * Free a buffer back to the pool
 */
static void buf_free(struct buf *b) {
    for (int i = 0; i < NBUF; i++) {
        if (&buf_pool[i] == b) {
            buf_used[i] = 0;
            return;
        }
    }
}

/**
 * Read a block from disk
 * @param dev Device number (ignored for now, single disk)
 * @param blockno Block number
 * @return Buffer containing block data, or NULL on error
 */
struct buf* bread(uint32_t dev, uint32_t blockno) {
    (void)dev;  // Single device for now

    struct buf *b = buf_alloc();
    if (!b) return 0;

    b->dev = dev;
    b->blockno = blockno;

    // Use VirtIO driver to read the block
    if (virtio_read_block(blockno, b->data) < 0) {
        print("[BIO] ERROR: Read failed for block ");
        print_hex(blockno);
        print("\n");
        buf_free(b);
        return 0;
    }

    b->valid = 1;
    return b;
}

/**
 * Write a buffer back to disk
 * @param b Buffer to write
 */
void bwrite(struct buf *b) {
    if (!b || !b->valid) return;

    if (virtio_write_block(b->blockno, b->data) < 0) {
        print("[BIO] ERROR: Write failed for block ");
        print_hex(b->blockno);
        print("\n");
    }

    b->dirty = 0;
}

/**
 * Release a buffer
 * @param b Buffer to release
 */
void brelse(struct buf *b) {
    if (!b) return;

    // Write back if dirty
    if (b->dirty) {
        bwrite(b);
    }

    buf_free(b);
}

/**
 * Initialize block I/O layer
 */
void bio_init(void) {
    for (int i = 0; i < NBUF; i++) {
        buf_used[i] = 0;
    }
    print("[BIO] Block I/O initialized (");
    print_hex(NBUF);
    print(" buffers)\n");
}
