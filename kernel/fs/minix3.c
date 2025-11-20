/**
 * @file minix3.c
 * @brief MINIX v3 Filesystem Implementation
 */

#include "minix3_fs.h"
#include "vfs_icache.h"
#include "vfs_dcache.h"
#include "buffer_cache.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

/*******************************************************************************
 * FORWARD DECLARATIONS
 ******************************************************************************/

static struct vfs_inode* minix3_vfs_alloc_inode(struct vfs_super_block *sb);
static void minix3_vfs_destroy_inode(struct vfs_inode *inode);
static int minix3_vfs_write_inode(struct vfs_inode *inode);
static struct vfs_inode* minix3_vfs_read_inode(struct vfs_super_block *sb, uint64_t inum);
static int minix3_vfs_write_super(struct vfs_super_block *sb);
static int minix3_vfs_sync_fs(struct vfs_super_block *sb);

static uint64_t minix3_vfs_lookup(struct vfs_inode *dir, const char *name, uint32_t len);
static struct vfs_inode* minix3_vfs_create(struct vfs_inode *dir, const char *name,
                                           uint32_t len, uint16_t mode);
static int minix3_vfs_mkdir(struct vfs_inode *dir, const char *name,
                            uint32_t len, uint16_t mode);
static int minix3_vfs_unlink(struct vfs_inode *dir, const char *name, uint32_t len);
static int minix3_vfs_rmdir(struct vfs_inode *dir, const char *name, uint32_t len);

static int minix3_vfs_open(struct vfs_inode *inode, struct vfs_file *file);
static int minix3_vfs_release(struct vfs_file *file);
static ssize_t minix3_vfs_read(struct vfs_file *file, void *buf,
                               size_t count, uint64_t offset);
static ssize_t minix3_vfs_write(struct vfs_file *file, const void *buf,
                                size_t count, uint64_t offset);
static int minix3_vfs_fsync(struct vfs_file *file);
static int minix3_vfs_readdir(struct vfs_file *file,
                              int (*callback)(void *, const char *, uint64_t),
                              void *ctx);

/*******************************************************************************
 * VFS OPERATIONS TABLES
 ******************************************************************************/

static const struct vfs_super_operations minix3_super_ops = {
    .alloc_inode = minix3_vfs_alloc_inode,
    .destroy_inode = minix3_vfs_destroy_inode,
    .write_inode = minix3_vfs_write_inode,
    .read_inode = minix3_vfs_read_inode,
    .write_super = minix3_vfs_write_super,
    .sync_fs = minix3_vfs_sync_fs,
};

static const struct vfs_inode_operations minix3_inode_ops = {
    .lookup = minix3_vfs_lookup,
    .create = minix3_vfs_create,
    .mkdir = minix3_vfs_mkdir,
    .unlink = minix3_vfs_unlink,
    .rmdir = minix3_vfs_rmdir,
};

static const struct vfs_file_operations minix3_file_ops = {
    .open = minix3_vfs_open,
    .release = minix3_vfs_release,
    .read = minix3_vfs_read,
    .write = minix3_vfs_write,
    .fsync = minix3_vfs_fsync,
    .readdir = minix3_vfs_readdir,
};

/*******************************************************************************
 * INITIALIZATION
 ******************************************************************************/

int minix3_init(void)
{
    /* Register with VFS */
    int ret = vfs_register_filesystem(FS_TYPE_MINIX3,
                                      &minix3_super_ops,
                                      &minix3_inode_ops,
                                      &minix3_file_ops);

    if (ret < 0) {
        printf("MINIX3: Failed to register filesystem\n");
        return ret;
    }

    printf("MINIX3: Filesystem driver initialized\n");
    return 0;
}

/*******************************************************************************
 * BITMAP OPERATIONS
 ******************************************************************************/

int minix3_bitmap_find_zero(const uint8_t *bitmap, uint32_t size)
{
    if (!bitmap) return -1;

    for (uint32_t byte = 0; byte < size; byte++) {
        if (bitmap[byte] != 0xFF) {
            /* Found byte with zero bit */
            for (int bit = 0; bit < 8; bit++) {
                if ((bitmap[byte] & (1 << bit)) == 0) {
                    return byte * 8 + bit;
                }
            }
        }
    }

    return -1;  /* Not found */
}

/*******************************************************************************
 * SUPERBLOCK OPERATIONS
 ******************************************************************************/

minix3_sb_t* minix3_read_super(uint32_t dev)
{
    /* TODO: Read superblock from device */
    /* For now, return NULL as device I/O not implemented */
    (void)dev;
    return NULL;
}

int minix3_write_super(minix3_sb_t *sb)
{
    if (!sb) return -1;

    /* TODO: Write superblock to device */
    return 0;
}

int minix3_sync(minix3_sb_t *sb)
{
    if (!sb) return -1;

    /* Write superblock */
    minix3_write_super(sb);

    /* TODO: Flush bitmaps */
    /* TODO: Flush buffer cache */

    return 0;
}

/*******************************************************************************
 * INODE OPERATIONS
 ******************************************************************************/

minix3_inode_t* minix3_read_inode(minix3_sb_t *sb, uint32_t inum)
{
    if (!sb || inum == 0) return NULL;

    /* Allocate inode structure */
    minix3_inode_t *inode = malloc(sizeof(minix3_inode_t));
    if (!inode) return NULL;

    memset(inode, 0, sizeof(*inode));

    inode->dev = sb->dev;
    inode->inum = inum;

    /* TODO: Read inode from disk */
    /* For now, initialize with defaults */
    inode->di.type = T_FILE;
    inode->di.nlink = 1;
    inode->di.size = 0;

    atomic_store(&inode->dirty, 0);

    return inode;
}

int minix3_write_inode(minix3_sb_t *sb, minix3_inode_t *inode)
{
    if (!sb || !inode) return -1;

    /* TODO: Write inode to disk */

    atomic_store(&inode->dirty, 0);
    return 0;
}

uint32_t minix3_alloc_inode(minix3_sb_t *sb, short type)
{
    if (!sb || !sb->inode_bitmap) return 0;

    /* Find free inode */
    int inum = minix3_bitmap_find_zero(sb->inode_bitmap,
                                       sb->inode_bitmap_blocks * BSIZE);

    if (inum < 0 || inum >= (int)sb->sb.ninodes) {
        return 0;  /* No free inodes */
    }

    /* Mark as allocated */
    minix3_bitmap_set(sb->inode_bitmap, inum);
    atomic_fetch_sub(&sb->free_inodes, 1);

    /* Initialize inode */
    minix3_inode_t *inode = minix3_read_inode(sb, inum);
    if (!inode) {
        minix3_bitmap_clear(sb->inode_bitmap, inum);
        atomic_fetch_add(&sb->free_inodes, 1);
        return 0;
    }

    inode->di.type = type;
    inode->di.nlink = 0;
    inode->di.size = 0;
    memset(inode->di.addrs, 0, sizeof(inode->di.addrs));

    minix3_write_inode(sb, inode);
    free(inode);

    return inum;
}

int minix3_free_inode(minix3_sb_t *sb, uint32_t inum)
{
    if (!sb || !sb->inode_bitmap || inum == 0 || inum >= sb->sb.ninodes) {
        return -1;
    }

    /* Mark as free */
    minix3_bitmap_clear(sb->inode_bitmap, inum);
    atomic_fetch_add(&sb->free_inodes, 1);

    return 0;
}

/*******************************************************************************
 * BLOCK OPERATIONS
 ******************************************************************************/

uint32_t minix3_alloc_block(minix3_sb_t *sb)
{
    if (!sb || !sb->zone_bitmap) return 0;

    /* Find free block */
    int blockno = minix3_bitmap_find_zero(sb->zone_bitmap,
                                          sb->zone_bitmap_blocks * BSIZE);

    if (blockno < 0 || blockno >= (int)sb->sb.nblocks) {
        return 0;  /* No free blocks */
    }

    /* Mark as allocated */
    minix3_bitmap_set(sb->zone_bitmap, blockno);
    atomic_fetch_sub(&sb->free_zones, 1);

    return blockno;
}

int minix3_free_block(minix3_sb_t *sb, uint32_t block)
{
    if (!sb || !sb->zone_bitmap || block == 0 || block >= sb->sb.nblocks) {
        return -1;
    }

    /* Mark as free */
    minix3_bitmap_clear(sb->zone_bitmap, block);
    atomic_fetch_add(&sb->free_zones, 1);

    return 0;
}

uint32_t minix3_bmap(minix3_sb_t *sb, minix3_inode_t *inode,
                     uint32_t block_num, bool alloc)
{
    if (!sb || !inode) return 0;

    /* Direct blocks */
    if (block_num < NDIRECT) {
        if (inode->di.addrs[block_num] == 0 && alloc) {
            inode->di.addrs[block_num] = minix3_alloc_block(sb);
            atomic_store(&inode->dirty, 1);
        }
        return inode->di.addrs[block_num];
    }

    block_num -= NDIRECT;

    /* Indirect block */
    if (block_num < NINDIRECT) {
        /* Get or allocate indirect block */
        uint32_t indirect = inode->di.addrs[NDIRECT];
        if (indirect == 0) {
            if (!alloc) return 0;
            indirect = minix3_alloc_block(sb);
            if (indirect == 0) return 0;
            inode->di.addrs[NDIRECT] = indirect;
            atomic_store(&inode->dirty, 1);
        }

        /* TODO: Read indirect block and get entry */
        /* For now, return 0 */
        return 0;
    }

    /* Beyond file size limit */
    return 0;
}

/*******************************************************************************
 * DIRECTORY OPERATIONS
 ******************************************************************************/

uint32_t minix3_dir_lookup(minix3_sb_t *sb, minix3_inode_t *dir,
                           const char *name, uint32_t len)
{
    if (!sb || !dir || !name || len == 0 || len > DIRSIZ) {
        return 0;
    }

    if (dir->di.type != T_DIR) {
        return 0;  /* Not a directory */
    }

    /* Read directory entries */
    uint32_t num_entries = dir->di.size / sizeof(struct dirent);

    for (uint32_t i = 0; i < num_entries; i++) {
        struct dirent de;

        /* TODO: Read directory entry from disk */
        /* For now, return 0 */
        (void)de;
    }

    return 0;  /* Not found */
}

int minix3_dir_add(minix3_sb_t *sb, minix3_inode_t *dir,
                   const char *name, uint32_t len, uint32_t inum)
{
    if (!sb || !dir || !name || len == 0 || len > DIRSIZ || inum == 0) {
        return -1;
    }

    if (dir->di.type != T_DIR) {
        return -1;  /* Not a directory */
    }

    /* TODO: Find free directory entry slot */
    /* TODO: Write directory entry */

    return -1;  /* Not implemented */
}

int minix3_dir_remove(minix3_sb_t *sb, minix3_inode_t *dir,
                      const char *name, uint32_t len)
{
    if (!sb || !dir || !name || len == 0 || len > DIRSIZ) {
        return -1;
    }

    if (dir->di.type != T_DIR) {
        return -1;  /* Not a directory */
    }

    /* TODO: Find directory entry */
    /* TODO: Mark as free (set inum to 0) */

    return -1;  /* Not implemented */
}

bool minix3_dir_is_empty(minix3_sb_t *sb, minix3_inode_t *dir)
{
    if (!sb || !dir || dir->di.type != T_DIR) {
        return false;
    }

    /* TODO: Check if directory has only . and .. */

    return true;  /* Stub */
}

/*******************************************************************************
 * FILE I/O OPERATIONS
 ******************************************************************************/

ssize_t minix3_file_read(minix3_sb_t *sb, minix3_inode_t *inode,
                         void *buf, size_t count, uint64_t offset)
{
    if (!sb || !inode || !buf || count == 0) {
        return -1;
    }

    /* Check bounds */
    if (offset >= inode->di.size) {
        return 0;  /* EOF */
    }

    /* Limit to file size */
    if (offset + count > inode->di.size) {
        count = inode->di.size - offset;
    }

    /* Get global buffer cache */
    buffer_cache_t *cache = bcache_get_global();
    if (!cache) {
        return -1;
    }

    size_t bytes_read = 0;
    uint8_t *dst = (uint8_t *)buf;

    while (bytes_read < count) {
        /* Calculate block number and offset within block */
        uint64_t file_block = (offset + bytes_read) / BSIZE;
        uint32_t block_offset = (offset + bytes_read) % BSIZE;
        uint32_t bytes_in_block = BSIZE - block_offset;

        if (bytes_in_block > count - bytes_read) {
            bytes_in_block = count - bytes_read;
        }

        /* Map file block to disk block */
        uint32_t disk_block = minix3_bmap(sb, inode, file_block, false);
        if (disk_block == 0) {
            /* Sparse file - return zeros */
            memset(dst + bytes_read, 0, bytes_in_block);
        } else {
            /* Read block through buffer cache with prefetch */
            bcache_entry_t *entry = bcache_read_with_prefetch(cache, sb->dev,
                                                               disk_block, NULL);
            if (!entry) {
                /* Read failed */
                break;
            }

            /* Copy data from cache to user buffer */
            memcpy(dst + bytes_read,
                   (uint8_t *)entry->data + block_offset,
                   bytes_in_block);

            /* Release cache entry */
            bcache_release(cache, entry);
        }

        bytes_read += bytes_in_block;
    }

    return bytes_read;
}

ssize_t minix3_file_write(minix3_sb_t *sb, minix3_inode_t *inode,
                          const void *buf, size_t count, uint64_t offset)
{
    if (!sb || !inode || !buf || count == 0) {
        return -1;
    }

    /* Get global buffer cache */
    buffer_cache_t *cache = bcache_get_global();
    if (!cache) {
        return -1;
    }

    size_t bytes_written = 0;
    const uint8_t *src = (const uint8_t *)buf;

    while (bytes_written < count) {
        /* Calculate block number and offset within block */
        uint64_t file_block = (offset + bytes_written) / BSIZE;
        uint32_t block_offset = (offset + bytes_written) % BSIZE;
        uint32_t bytes_in_block = BSIZE - block_offset;

        if (bytes_in_block > count - bytes_written) {
            bytes_in_block = count - bytes_written;
        }

        /* Map file block to disk block (allocate if needed) */
        uint32_t disk_block = minix3_bmap(sb, inode, file_block, true);
        if (disk_block == 0) {
            /* Allocation failed */
            break;
        }

        /* Get or read block through buffer cache */
        bcache_entry_t *entry = bcache_get_or_read(cache, sb->dev, disk_block, NULL);
        if (!entry) {
            /* Cache operation failed */
            break;
        }

        /* Copy data from user buffer to cache */
        memcpy((uint8_t *)entry->data + block_offset,
               src + bytes_written,
               bytes_in_block);

        /* Mark block dirty */
        atomic_fetch_or(&entry->flags, BCACHE_DIRTY);

        /* Release cache entry */
        bcache_release(cache, entry);

        bytes_written += bytes_in_block;
    }

    /* Update file size if we extended it */
    if (offset + bytes_written > inode->di.size) {
        inode->di.size = offset + bytes_written;
        atomic_store(&inode->dirty, 1);
    }

    /* Mark inode dirty if we wrote anything */
    if (bytes_written > 0) {
        atomic_store(&inode->dirty, 1);
    }

    return bytes_written;
}

int minix3_file_truncate(minix3_sb_t *sb, minix3_inode_t *inode, uint64_t length)
{
    if (!sb || !inode) {
        return -1;
    }

    /* TODO: Free blocks beyond new length */
    /* TODO: Update size */

    inode->di.size = length;
    atomic_store(&inode->dirty, 1);

    return 0;
}

/*******************************************************************************
 * VFS ADAPTER FUNCTIONS
 ******************************************************************************/

static struct vfs_inode* minix3_vfs_alloc_inode(struct vfs_super_block *sb)
{
    if (!sb || !sb->fs_private) return NULL;

    minix3_sb_t *m3sb = (minix3_sb_t *)sb->fs_private;

    /* Allocate VFS inode */
    struct vfs_inode *inode = malloc(sizeof(struct vfs_inode));
    if (!inode) return NULL;

    memset(inode, 0, sizeof(*inode));

    inode->sb = sb;
    atomic_store(&inode->refcount, 1);

    /* Allocate MINIX inode */
    minix3_inode_t *m3inode = malloc(sizeof(minix3_inode_t));
    if (!m3inode) {
        free(inode);
        return NULL;
    }

    memset(m3inode, 0, sizeof(*m3inode));
    m3inode->dev = m3sb->dev;
    m3inode->vfs_inode = inode;

    inode->fs_private = m3inode;

    return inode;
}

static void minix3_vfs_destroy_inode(struct vfs_inode *inode)
{
    if (!inode) return;

    if (inode->fs_private) {
        free(inode->fs_private);
    }

    free(inode);
}

static int minix3_vfs_write_inode(struct vfs_inode *inode)
{
    if (!inode || !inode->fs_private || !inode->sb || !inode->sb->fs_private) {
        return -1;
    }

    minix3_inode_t *m3inode = (minix3_inode_t *)inode->fs_private;
    minix3_sb_t *m3sb = (minix3_sb_t *)inode->sb->fs_private;

    return minix3_write_inode(m3sb, m3inode);
}

static struct vfs_inode* minix3_vfs_read_inode(struct vfs_super_block *sb, uint64_t inum)
{
    if (!sb || !sb->fs_private || inum == 0) {
        return NULL;
    }

    minix3_sb_t *m3sb = (minix3_sb_t *)sb->fs_private;

    /* Read MINIX inode */
    minix3_inode_t *m3inode = minix3_read_inode(m3sb, (uint32_t)inum);
    if (!m3inode) return NULL;

    /* Allocate VFS inode */
    struct vfs_inode *inode = malloc(sizeof(struct vfs_inode));
    if (!inode) {
        free(m3inode);
        return NULL;
    }

    memset(inode, 0, sizeof(*inode));

    /* Fill VFS inode */
    inode->inum = inum;
    inode->sb = sb;
    inode->mode = (m3inode->di.type == T_DIR) ? S_IFDIR : S_IFREG;
    inode->nlink = m3inode->di.nlink;
    inode->size = m3inode->di.size;
    atomic_store(&inode->refcount, 1);

    inode->fs_private = m3inode;
    m3inode->vfs_inode = inode;

    return inode;
}

static int minix3_vfs_write_super(struct vfs_super_block *sb)
{
    if (!sb || !sb->fs_private) return -1;

    minix3_sb_t *m3sb = (minix3_sb_t *)sb->fs_private;
    return minix3_write_super(m3sb);
}

static int minix3_vfs_sync_fs(struct vfs_super_block *sb)
{
    if (!sb || !sb->fs_private) return -1;

    minix3_sb_t *m3sb = (minix3_sb_t *)sb->fs_private;
    return minix3_sync(m3sb);
}

static uint64_t minix3_vfs_lookup(struct vfs_inode *dir, const char *name, uint32_t len)
{
    if (!dir || !dir->fs_private || !dir->sb || !dir->sb->fs_private || !name) {
        return 0;
    }

    minix3_inode_t *m3dir = (minix3_inode_t *)dir->fs_private;
    minix3_sb_t *m3sb = (minix3_sb_t *)dir->sb->fs_private;

    return minix3_dir_lookup(m3sb, m3dir, name, len);
}

static struct vfs_inode* minix3_vfs_create(struct vfs_inode *dir, const char *name,
                                           uint32_t len, uint16_t mode)
{
    if (!dir || !dir->fs_private || !dir->sb || !dir->sb->fs_private || !name) {
        return NULL;
    }

    minix3_inode_t *m3dir = (minix3_inode_t *)dir->fs_private;
    minix3_sb_t *m3sb = (minix3_sb_t *)dir->sb->fs_private;

    /* Allocate inode */
    uint32_t inum = minix3_alloc_inode(m3sb, T_FILE);
    if (inum == 0) return NULL;

    /* Add directory entry */
    if (minix3_dir_add(m3sb, m3dir, name, len, inum) < 0) {
        minix3_free_inode(m3sb, inum);
        return NULL;
    }

    /* Read and return inode */
    return minix3_vfs_read_inode(dir->sb, inum);
}

static int minix3_vfs_mkdir(struct vfs_inode *dir, const char *name,
                            uint32_t len, uint16_t mode)
{
    if (!dir || !dir->fs_private || !dir->sb || !dir->sb->fs_private || !name) {
        return -1;
    }

    minix3_inode_t *m3dir = (minix3_inode_t *)dir->fs_private;
    minix3_sb_t *m3sb = (minix3_sb_t *)dir->sb->fs_private;

    /* Allocate inode */
    uint32_t inum = minix3_alloc_inode(m3sb, T_DIR);
    if (inum == 0) return -1;

    /* Add directory entry */
    if (minix3_dir_add(m3sb, m3dir, name, len, inum) < 0) {
        minix3_free_inode(m3sb, inum);
        return -1;
    }

    /* TODO: Add . and .. entries */

    return 0;
}

static int minix3_vfs_unlink(struct vfs_inode *dir, const char *name, uint32_t len)
{
    if (!dir || !dir->fs_private || !dir->sb || !dir->sb->fs_private || !name) {
        return -1;
    }

    minix3_inode_t *m3dir = (minix3_inode_t *)dir->fs_private;
    minix3_sb_t *m3sb = (minix3_sb_t *)dir->sb->fs_private;

    /* TODO: Look up inode */
    /* TODO: Decrease link count */
    /* TODO: Free inode if link count reaches 0 */

    return minix3_dir_remove(m3sb, m3dir, name, len);
}

static int minix3_vfs_rmdir(struct vfs_inode *dir, const char *name, uint32_t len)
{
    /* Same as unlink but check directory is empty */
    return minix3_vfs_unlink(dir, name, len);
}

static int minix3_vfs_open(struct vfs_inode *inode, struct vfs_file *file)
{
    /* Nothing special needed */
    (void)inode;
    (void)file;
    return 0;
}

static int minix3_vfs_release(struct vfs_file *file)
{
    /* Nothing special needed */
    (void)file;
    return 0;
}

static ssize_t minix3_vfs_read(struct vfs_file *file, void *buf,
                               size_t count, uint64_t offset)
{
    if (!file || !file->inode || !file->inode->fs_private ||
        !file->inode->sb || !file->inode->sb->fs_private || !buf) {
        return -1;
    }

    minix3_inode_t *m3inode = (minix3_inode_t *)file->inode->fs_private;
    minix3_sb_t *m3sb = (minix3_sb_t *)file->inode->sb->fs_private;

    return minix3_file_read(m3sb, m3inode, buf, count, offset);
}

static ssize_t minix3_vfs_write(struct vfs_file *file, const void *buf,
                                size_t count, uint64_t offset)
{
    if (!file || !file->inode || !file->inode->fs_private ||
        !file->inode->sb || !file->inode->sb->fs_private || !buf) {
        return -1;
    }

    minix3_inode_t *m3inode = (minix3_inode_t *)file->inode->fs_private;
    minix3_sb_t *m3sb = (minix3_sb_t *)file->inode->sb->fs_private;

    return minix3_file_write(m3sb, m3inode, buf, count, offset);
}

static int minix3_vfs_fsync(struct vfs_file *file)
{
    if (!file || !file->inode) return -1;

    /* Write inode */
    return minix3_vfs_write_inode(file->inode);
}

static int minix3_vfs_readdir(struct vfs_file *file,
                              int (*callback)(void *, const char *, uint64_t),
                              void *ctx)
{
    if (!file || !callback) return -1;

    /* TODO: Read directory entries and call callback */

    return 0;
}

/*******************************************************************************
 * STATISTICS
 ******************************************************************************/

int minix3_get_stats(const minix3_sb_t *sb, minix3_stats_t *stats)
{
    if (!sb || !stats) return -1;

    memset(stats, 0, sizeof(*stats));

    stats->total_inodes = sb->sb.ninodes;
    stats->free_inodes = atomic_load(&sb->free_inodes);
    stats->total_blocks = sb->sb.nblocks;
    stats->free_blocks = atomic_load(&sb->free_zones);
    stats->block_size = BSIZE;

    return 0;
}

void minix3_print_stats(const minix3_sb_t *sb)
{
    if (!sb) return;

    printf("================================================================================\n");
    printf("MINIX v3 FILESYSTEM STATISTICS\n");
    printf("================================================================================\n\n");

    minix3_stats_t stats;
    minix3_get_stats(sb, &stats);

    printf("Inodes:\n");
    printf("  Total:             %u\n", stats.total_inodes);
    printf("  Free:              %u\n", stats.free_inodes);
    printf("  Used:              %u (%.1f%%)\n",
           stats.total_inodes - stats.free_inodes,
           100.0 * (stats.total_inodes - stats.free_inodes) / stats.total_inodes);
    printf("\n");

    printf("Blocks:\n");
    printf("  Total:             %u\n", stats.total_blocks);
    printf("  Free:              %u\n", stats.free_blocks);
    printf("  Used:              %u (%.1f%%)\n",
           stats.total_blocks - stats.free_blocks,
           100.0 * (stats.total_blocks - stats.free_blocks) / stats.total_blocks);
    printf("  Block Size:        %u bytes\n", stats.block_size);
    printf("\n");

    printf("Capacity:\n");
    printf("  Total:             %.2f MB\n",
           (double)(stats.total_blocks * stats.block_size) / (1024 * 1024));
    printf("  Free:              %.2f MB\n",
           (double)(stats.free_blocks * stats.block_size) / (1024 * 1024));
    printf("  Used:              %.2f MB\n",
           (double)((stats.total_blocks - stats.free_blocks) * stats.block_size) / (1024 * 1024));

    printf("================================================================================\n");
}
