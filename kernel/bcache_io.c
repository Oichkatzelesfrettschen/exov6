/**
 * @file bcache_io.c
 * @brief Buffer Cache Device I/O Layer
 *
 * Bridges the novel PDAC-aware buffer cache to the IDE driver.
 * Converts between bcache_entry_t and struct buf for disk operations.
 */

#include "buffer_cache.h"
#include "buf.h"
#include "fs.h"
#include "sleeplock.h"
#include <string.h>
#include <stdio.h>

/* Forward declarations - these come from bio.c/ide.c */
extern void iderw(struct buf *b);
extern void initsleeplock(struct sleeplock *lk, char *name, int level);
extern void acquiresleep(struct sleeplock *lk);
extern void releasesleep(struct sleeplock *lk);

/*******************************************************************************
 * DEVICE I/O OPERATIONS
 ******************************************************************************/

/**
 * @brief Read a block from disk into buffer cache entry
 *
 * @param cache Buffer cache instance
 * @param entry Cache entry to read into
 * @return 0 on success, -1 on error
 */
int bcache_io_read(buffer_cache_t *cache, bcache_entry_t *entry)
{
    if (!cache || !entry || !entry->data) {
        return -1;
    }

    /* Create temporary buf structure for IDE driver */
    struct buf b;
    memset(&b, 0, sizeof(b));

    /* Initialize sleeplock for synchronization */
    initsleeplock(&b.lock, "bcache_io", 100);
    acquiresleep(&b.lock);

    /* Setup buffer for read */
    b.dev = entry->dev;
    b.blockno = entry->blockno;
    b.flags = 0;  /* Not DIRTY, so IDE will read */
    b.refcnt = 1;
    b.rcref = 0;

    /* Perform IDE read */
    iderw(&b);

    /* Copy data from temporary buffer to cache entry */
    if (b.flags & B_VALID) {
        memcpy(entry->data, b.data, BSIZE);
        releasesleep(&b.lock);
        return 0;
    }

    releasesleep(&b.lock);
    return -1;  /* Read failed */
}

/**
 * @brief Write a block from buffer cache entry to disk
 *
 * @param cache Buffer cache instance
 * @param entry Cache entry to write from
 * @return 0 on success, -1 on error
 */
int bcache_io_write(buffer_cache_t *cache, bcache_entry_t *entry)
{
    if (!cache || !entry || !entry->data) {
        return -1;
    }

    /* Check if entry is dirty */
    if (!(atomic_load(&entry->flags) & BCACHE_DIRTY)) {
        return 0;  /* Not dirty, nothing to write */
    }

    /* Create temporary buf structure for IDE driver */
    struct buf b;
    memset(&b, 0, sizeof(b));

    /* Initialize sleeplock for synchronization */
    initsleeplock(&b.lock, "bcache_io", 100);
    acquiresleep(&b.lock);

    /* Setup buffer for write */
    b.dev = entry->dev;
    b.blockno = entry->blockno;
    b.flags = B_DIRTY | B_VALID;  /* Mark dirty so IDE will write */
    b.refcnt = 1;
    b.rcref = 0;

    /* Copy data from cache entry to temporary buffer */
    memcpy(b.data, entry->data, BSIZE);

    /* Perform IDE write */
    iderw(&b);

    /* Check if write succeeded */
    if ((b.flags & B_VALID) && !(b.flags & B_DIRTY)) {
        /* Write succeeded - clear dirty flag in cache entry */
        atomic_fetch_and(&entry->flags, ~BCACHE_DIRTY);
        releasesleep(&b.lock);
        return 0;
    }

    releasesleep(&b.lock);
    return -1;  /* Write failed */
}

/**
 * @brief Async read-ahead (queues read for later)
 *
 * For now, this performs synchronous read. In Phase 5.4,
 * we'll implement a proper async I/O queue.
 *
 * @param cache Buffer cache instance
 * @param entry Cache entry to read into
 * @return 0 on success, -1 on error
 */
int bcache_io_read_async(buffer_cache_t *cache, bcache_entry_t *entry)
{
    /* TODO Phase 5.4: Implement async I/O queue */
    /* For now, just perform synchronous read */
    return bcache_io_read(cache, entry);
}

/**
 * @brief Check if device is available
 *
 * @param dev Device number
 * @return true if device exists, false otherwise
 */
bool bcache_io_device_exists(uint32_t dev)
{
    /* Device 0 always exists (primary IDE disk) */
    /* Device 1 exists if havedisk1 is set in ide.c */
    /* For simplicity, accept devices 0-1 */
    return (dev <= 1);
}

/**
 * @brief Flush all dirty blocks for a device
 *
 * @param cache Buffer cache instance
 * @param dev Device number
 * @return Number of blocks flushed, or -1 on error
 */
int bcache_io_flush_device(buffer_cache_t *cache, uint32_t dev)
{
    if (!cache) {
        return -1;
    }

    int flushed = 0;
    int errors = 0;

    /* Walk all hash buckets */
    for (uint32_t i = 0; i < BCACHE_BUCKETS; i++) {
        bcache_entry_t *entry = cache->buckets[i];

        while (entry) {
            if (entry->dev == dev && (atomic_load(&entry->flags) & BCACHE_DIRTY)) {
                if (bcache_io_write(cache, entry) == 0) {
                    flushed++;
                } else {
                    errors++;
                }
            }
            entry = entry->next;
        }
    }

    if (errors > 0) {
        fprintf(stderr, "bcache_io: %d errors while flushing device %u\n", errors, dev);
        return -1;
    }

    return flushed;
}
