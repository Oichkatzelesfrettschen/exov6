#pragma once

#include <stddef.h>
#include <stdint.h>

#include "file.h"
#include "fs.h"
#include "exokernel.h"

/**
 * @brief Read a block from the backing store.
 *
 * @param cap Capability identifying the block.
 * @param dst Destination buffer.
 * @return 0 on success, negative error code otherwise.
 */
int fs_read_block(struct exo_blockcap cap, void *dst);

/**
 * @brief Write a block to the backing store.
 *
 * @param cap Capability identifying the block.
 * @param src Source buffer.
 * @return 0 on success, negative error code otherwise.
 */
int fs_write_block(struct exo_blockcap cap, const void *src);

/**
 * @brief Allocate a new block capability.
 *
 * @param dev Device identifier.
 * @param rights Capability rights mask.
 * @param cap Destination for the new capability.
 * @return 0 on success, negative error code otherwise.
 */
int fs_alloc_block(uint32_t dev, uint32_t rights, struct exo_blockcap *cap);

/**
 * @brief Bind a block capability to a memory region.
 *
 * @param cap   Capability to bind.
 * @param data  Memory region.
 * @param write Non-zero to request write access.
 * @return 0 on success, negative error code otherwise.
 */
int fs_bind_block(struct exo_blockcap *cap, void *data, int write);

/** Initialize the file-system support layer. */
void libfs_init(void);

/**
 * @brief Open a file by path.
 *
 * @param path File path.
 * @param flags Open flags.
 * @return Pointer to file structure or NULL on failure.
 */
struct file *libfs_open(const char *path, int flags);

/**
 * @brief Read from an open file.
 *
 * @param f   File handle.
 * @param buf Destination buffer.
 * @param n   Number of bytes to read.
 * @return Number of bytes read or negative error code.
 */
int libfs_read(struct file *f, void *buf, size_t n);

/**
 * @brief Write to an open file.
 *
 * @param f   File handle.
 * @param buf Source buffer.
 * @param n   Number of bytes to write.
 * @return Number of bytes written or negative error code.
 */
int libfs_write(struct file *f, const void *buf, size_t n);

/**
 * @brief Close an open file.
 *
 * @param f File handle.
 */
void libfs_close(struct file *f);

/**
 * @brief Delete a file by path.
 *
 * @param path File path.
 * @return 0 on success, negative error code otherwise.
 */
int libfs_unlink(const char *path);

/**
 * @brief Rename a file.
 *
 * @param oldpath Original path.
 * @param newpath New path.
 * @return 0 on success, negative error code otherwise.
 */
int libfs_rename(const char *oldpath, const char *newpath);

/**
 * @brief Truncate a file to the given length.
 *
 * @param f      File handle.
 * @param length Desired length.
 * @return 0 on success, negative error code otherwise.
 */
int libfs_truncate(struct file *f, size_t length);
