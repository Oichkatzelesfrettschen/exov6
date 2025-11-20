/**
 * @file minix3_fs.h
 * @brief MINIX v3 Filesystem Implementation
 *
 * MINIX v3 is a simple, educational filesystem with:
 * - Bitmap-based free space management
 * - Traditional Unix-style inodes
 * - Direct and indirect block addressing
 * - Simple directory structure
 *
 * Integrated with VFS and PDAC.
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include "vfs.h"
#include "fs.h"

#ifdef __cplusplus
extern "C" {
#endif

/*******************************************************************************
 * ON-DISK STRUCTURES (from fs.h)
 ******************************************************************************/

/* Already defined in fs.h:
 * - struct superblock
 * - struct dinode
 * - struct dirent
 * - BSIZE (512)
 * - NDIRECT (12)
 * - NINDIRECT
 */

/*******************************************************************************
 * IN-MEMORY STRUCTURES
 ******************************************************************************/

/**
 * @brief MINIX v3 superblock (in-memory)
 */
typedef struct {
    struct superblock sb;              /**< On-disk superblock */
    uint32_t dev;                      /**< Device number */

    /* Cached bitmaps */
    uint8_t *inode_bitmap;             /**< Inode allocation bitmap */
    uint8_t *zone_bitmap;              /**< Zone allocation bitmap */
    uint32_t inode_bitmap_blocks;      /**< Number of inode bitmap blocks */
    uint32_t zone_bitmap_blocks;       /**< Number of zone bitmap blocks */

    /* Statistics */
    _Atomic uint32_t free_inodes;      /**< Free inodes */
    _Atomic uint32_t free_zones;       /**< Free zones (blocks) */

    /* Reference counting */
    _Atomic uint32_t refcount;
} minix3_sb_t;

/**
 * @brief MINIX v3 inode (in-memory)
 */
typedef struct {
    struct dinode di;                  /**< On-disk inode */
    uint32_t dev;                      /**< Device number */
    uint32_t inum;                     /**< Inode number */

    /* VFS integration */
    struct vfs_inode *vfs_inode;       /**< Associated VFS inode */

    /* State */
    _Atomic uint32_t dirty;            /**< Dirty flag */
} minix3_inode_t;

/**
 * @brief MINIX v3 directory entry (in-memory)
 */
typedef struct {
    struct dirent de;                  /**< On-disk directory entry */
    char name_str[DIRSIZ + 1];         /**< Null-terminated name */
} minix3_dirent_t;

/*******************************************************************************
 * MINIX V3 FILESYSTEM OPERATIONS
 ******************************************************************************/

/**
 * @brief Initialize MINIX v3 filesystem
 *
 * Registers MINIX v3 with VFS layer.
 *
 * @return 0 on success, negative on error
 */
int minix3_init(void);

/**
 * @brief Mount MINIX v3 filesystem
 *
 * @param dev          Device number
 * @param mountpoint   Mount point path
 * @param flags        Mount flags
 * @return 0 on success, negative on error
 */
int minix3_mount(uint32_t dev, const char *mountpoint, uint32_t flags);

/**
 * @brief Unmount MINIX v3 filesystem
 *
 * @param dev  Device number
 * @return 0 on success, negative on error
 */
int minix3_umount(uint32_t dev);

/*******************************************************************************
 * SUPERBLOCK OPERATIONS
 ******************************************************************************/

/**
 * @brief Read MINIX v3 superblock from device
 *
 * @param dev  Device number
 * @return Superblock or NULL on error
 */
minix3_sb_t* minix3_read_super(uint32_t dev);

/**
 * @brief Write MINIX v3 superblock to device
 *
 * @param sb  MINIX v3 superblock
 * @return 0 on success, negative on error
 */
int minix3_write_super(minix3_sb_t *sb);

/**
 * @brief Sync MINIX v3 filesystem
 *
 * @param sb  MINIX v3 superblock
 * @return 0 on success, negative on error
 */
int minix3_sync(minix3_sb_t *sb);

/*******************************************************************************
 * INODE OPERATIONS
 ******************************************************************************/

/**
 * @brief Read MINIX v3 inode from disk
 *
 * @param sb    MINIX v3 superblock
 * @param inum  Inode number
 * @return Inode or NULL on error
 */
minix3_inode_t* minix3_read_inode(minix3_sb_t *sb, uint32_t inum);

/**
 * @brief Write MINIX v3 inode to disk
 *
 * @param sb     MINIX v3 superblock
 * @param inode  Inode to write
 * @return 0 on success, negative on error
 */
int minix3_write_inode(minix3_sb_t *sb, minix3_inode_t *inode);

/**
 * @brief Allocate a new inode
 *
 * @param sb    MINIX v3 superblock
 * @param type  Inode type (T_FILE, T_DIR, etc.)
 * @return Inode number or 0 on error
 */
uint32_t minix3_alloc_inode(minix3_sb_t *sb, short type);

/**
 * @brief Free an inode
 *
 * @param sb    MINIX v3 superblock
 * @param inum  Inode number
 * @return 0 on success, negative on error
 */
int minix3_free_inode(minix3_sb_t *sb, uint32_t inum);

/*******************************************************************************
 * BLOCK OPERATIONS
 ******************************************************************************/

/**
 * @brief Allocate a data block
 *
 * @param sb  MINIX v3 superblock
 * @return Block number or 0 on error
 */
uint32_t minix3_alloc_block(minix3_sb_t *sb);

/**
 * @brief Free a data block
 *
 * @param sb    MINIX v3 superblock
 * @param block Block number
 * @return 0 on success, negative on error
 */
int minix3_free_block(minix3_sb_t *sb, uint32_t block);

/**
 * @brief Get block number for file offset
 *
 * Maps logical block number to physical block number.
 * Handles direct, indirect, and double indirect blocks.
 *
 * @param sb         MINIX v3 superblock
 * @param inode      Inode
 * @param block_num  Logical block number
 * @param alloc      If true, allocate blocks if needed
 * @return Physical block number or 0 on error
 */
uint32_t minix3_bmap(minix3_sb_t *sb, minix3_inode_t *inode,
                     uint32_t block_num, bool alloc);

/*******************************************************************************
 * DIRECTORY OPERATIONS
 ******************************************************************************/

/**
 * @brief Look up directory entry
 *
 * @param sb    MINIX v3 superblock
 * @param dir   Directory inode
 * @param name  Entry name
 * @param len   Name length
 * @return Inode number or 0 if not found
 */
uint32_t minix3_dir_lookup(minix3_sb_t *sb, minix3_inode_t *dir,
                           const char *name, uint32_t len);

/**
 * @brief Add directory entry
 *
 * @param sb    MINIX v3 superblock
 * @param dir   Directory inode
 * @param name  Entry name
 * @param len   Name length
 * @param inum  Inode number
 * @return 0 on success, negative on error
 */
int minix3_dir_add(minix3_sb_t *sb, minix3_inode_t *dir,
                   const char *name, uint32_t len, uint32_t inum);

/**
 * @brief Remove directory entry
 *
 * @param sb    MINIX v3 superblock
 * @param dir   Directory inode
 * @param name  Entry name
 * @param len   Name length
 * @return 0 on success, negative on error
 */
int minix3_dir_remove(minix3_sb_t *sb, minix3_inode_t *dir,
                      const char *name, uint32_t len);

/**
 * @brief Check if directory is empty
 *
 * @param sb   MINIX v3 superblock
 * @param dir  Directory inode
 * @return true if empty (only . and ..)
 */
bool minix3_dir_is_empty(minix3_sb_t *sb, minix3_inode_t *dir);

/*******************************************************************************
 * FILE I/O OPERATIONS
 ******************************************************************************/

/**
 * @brief Read from file
 *
 * @param sb      MINIX v3 superblock
 * @param inode   File inode
 * @param buf     Output buffer
 * @param count   Bytes to read
 * @param offset  File offset
 * @return Bytes read or negative on error
 */
ssize_t minix3_file_read(minix3_sb_t *sb, minix3_inode_t *inode,
                         void *buf, size_t count, uint64_t offset);

/**
 * @brief Write to file
 *
 * @param sb      MINIX v3 superblock
 * @param inode   File inode
 * @param buf     Input buffer
 * @param count   Bytes to write
 * @param offset  File offset
 * @return Bytes written or negative on error
 */
ssize_t minix3_file_write(minix3_sb_t *sb, minix3_inode_t *inode,
                          const void *buf, size_t count, uint64_t offset);

/**
 * @brief Truncate file
 *
 * @param sb      MINIX v3 superblock
 * @param inode   File inode
 * @param length  New length
 * @return 0 on success, negative on error
 */
int minix3_file_truncate(minix3_sb_t *sb, minix3_inode_t *inode, uint64_t length);

/*******************************************************************************
 * BITMAP OPERATIONS
 ******************************************************************************/

/**
 * @brief Find first zero bit in bitmap
 *
 * @param bitmap  Bitmap
 * @param size    Size in bytes
 * @return Bit position or -1 if not found
 */
int minix3_bitmap_find_zero(const uint8_t *bitmap, uint32_t size);

/**
 * @brief Set bit in bitmap
 *
 * @param bitmap  Bitmap
 * @param bit     Bit position
 */
static inline void minix3_bitmap_set(uint8_t *bitmap, uint32_t bit)
{
    bitmap[bit / 8] |= (1 << (bit % 8));
}

/**
 * @brief Clear bit in bitmap
 *
 * @param bitmap  Bitmap
 * @param bit     Bit position
 */
static inline void minix3_bitmap_clear(uint8_t *bitmap, uint32_t bit)
{
    bitmap[bit / 8] &= ~(1 << (bit % 8));
}

/**
 * @brief Test bit in bitmap
 *
 * @param bitmap  Bitmap
 * @param bit     Bit position
 * @return true if bit is set
 */
static inline bool minix3_bitmap_test(const uint8_t *bitmap, uint32_t bit)
{
    return (bitmap[bit / 8] & (1 << (bit % 8))) != 0;
}

/*******************************************************************************
 * STATISTICS
 ******************************************************************************/

/**
 * @brief MINIX v3 filesystem statistics
 */
typedef struct {
    uint32_t total_inodes;
    uint32_t free_inodes;
    uint32_t total_blocks;
    uint32_t free_blocks;
    uint32_t block_size;
} minix3_stats_t;

/**
 * @brief Get MINIX v3 filesystem statistics
 *
 * @param sb     MINIX v3 superblock
 * @param stats  Output statistics
 * @return 0 on success, negative on error
 */
int minix3_get_stats(const minix3_sb_t *sb, minix3_stats_t *stats);

/**
 * @brief Print MINIX v3 filesystem statistics
 *
 * @param sb  MINIX v3 superblock
 */
void minix3_print_stats(const minix3_sb_t *sb);

#ifdef __cplusplus
}
#endif
