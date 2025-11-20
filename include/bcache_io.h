/**
 * @file bcache_io.h
 * @brief Buffer Cache Device I/O Layer Interface
 *
 * Provides device I/O operations for the PDAC-aware buffer cache.
 * Bridges between bcache_entry_t and the IDE driver.
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Forward declarations */
typedef struct buffer_cache buffer_cache_t;
typedef struct bcache_entry bcache_entry_t;

/*******************************************************************************
 * DEVICE I/O OPERATIONS
 ******************************************************************************/

/**
 * @brief Read a block from disk into buffer cache entry
 *
 * Synchronously reads the block identified by entry->dev and entry->blockno
 * from the IDE driver into entry->data.
 *
 * @param cache Buffer cache instance
 * @param entry Cache entry to read into (must have dev, blockno set)
 * @return 0 on success, -1 on error
 */
int bcache_io_read(buffer_cache_t *cache, bcache_entry_t *entry);

/**
 * @brief Write a block from buffer cache entry to disk
 *
 * Synchronously writes the block from entry->data to disk at the location
 * identified by entry->dev and entry->blockno. Only writes if the entry
 * is marked dirty.
 *
 * @param cache Buffer cache instance
 * @param entry Cache entry to write from
 * @return 0 on success, -1 on error
 */
int bcache_io_write(buffer_cache_t *cache, bcache_entry_t *entry);

/**
 * @brief Async read-ahead (queues read for later)
 *
 * Initiates an asynchronous read of the block. The read may complete
 * in the background. Currently implemented as synchronous read.
 *
 * @param cache Buffer cache instance
 * @param entry Cache entry to read into
 * @return 0 on success, -1 on error
 */
int bcache_io_read_async(buffer_cache_t *cache, bcache_entry_t *entry);

/**
 * @brief Check if device is available
 *
 * @param dev Device number (0 = primary disk, 1 = secondary disk)
 * @return true if device exists, false otherwise
 */
bool bcache_io_device_exists(uint32_t dev);

/**
 * @brief Flush all dirty blocks for a device
 *
 * Writes all dirty cache entries for the specified device to disk.
 * Used during unmount or sync operations.
 *
 * @param cache Buffer cache instance
 * @param dev Device number
 * @return Number of blocks flushed, or -1 on error
 */
int bcache_io_flush_device(buffer_cache_t *cache, uint32_t dev);

#ifdef __cplusplus
}
#endif
