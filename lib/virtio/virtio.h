/**
 * @file virtio.h
 * @brief User-Space VirtIO Block Driver API (Phase 8)
 *
 * This header exposes the VirtIO block driver as a library for use
 * by higher-level components like the file system.
 */

#ifndef LIBOS_VIRTIO_H
#define LIBOS_VIRTIO_H

#include <stdint.h>

// Block sizes
#define VIRTIO_SECTOR_SIZE  512     // VirtIO uses 512-byte sectors
#define FS_BLOCK_SIZE       1024    // xv6 file system uses 1024-byte blocks

/**
 * Initialize the VirtIO block driver
 * Maps MMIO region, initializes device, sets up virtqueues
 * @return 0 on success, negative on error
 */
int virtio_init(void);

/**
 * Read a single 512-byte sector from disk
 * @param sector Sector number (512-byte units)
 * @param buf Buffer to read into (must be at least 512 bytes)
 * @return 0 on success, negative on error
 */
int virtio_read_sector(uint64_t sector, void *buf);

/**
 * Write a single 512-byte sector to disk
 * @param sector Sector number (512-byte units)
 * @param buf Buffer to write from (must be at least 512 bytes)
 * @return 0 on success, negative on error
 */
int virtio_write_sector(uint64_t sector, const void *buf);

/**
 * Read a file system block (1024 bytes = 2 sectors)
 * @param blockno Block number (1024-byte units)
 * @param buf Buffer to read into (must be at least 1024 bytes)
 * @return 0 on success, negative on error
 */
int virtio_read_block(uint32_t blockno, void *buf);

/**
 * Write a file system block (1024 bytes = 2 sectors)
 * @param blockno Block number (1024-byte units)
 * @param buf Buffer to write from (must be at least 1024 bytes)
 * @return 0 on success, negative on error
 */
int virtio_write_block(uint32_t blockno, const void *buf);

/**
 * Check if VirtIO driver is initialized
 * @return 1 if initialized, 0 otherwise
 */
int virtio_is_ready(void);

#endif // LIBOS_VIRTIO_H
