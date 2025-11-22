/**
 * @file minix3.c
 * @brief MINIX v3 (xv6-fs layout) Filesystem Implementation
 */

#include "minix3_fs.h"
#include "vfs_icache.h"
#include "vfs_dcache.h"
#include "buffer_cache.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <sys/stat.h>

// Helper macros
#ifndef min
#define min(a, b) ((a) < (b) ? (a) : (b))
#endif

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

// Internal helpers
static uint32_t minix3_alloc_inode_internal(minix3_sb_t *sb, short type);
static int minix3_dir_link(minix3_sb_t *sb, minix3_inode_t *dir, const char *name, uint32_t len, uint32_t inum);
static ssize_t minix3_inode_read(minix3_sb_t *sb, minix3_inode_t *inode,
                                 void *buf, size_t count, uint64_t offset,
                                 const vfs_capability_t *cap);
static ssize_t minix3_inode_write(minix3_sb_t *sb, minix3_inode_t *inode,
                                  const void *buf, size_t count, uint64_t offset,
                                  const vfs_capability_t *cap);

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
 * SUPERBLOCK OPERATIONS
 ******************************************************************************/

minix3_sb_t* minix3_read_super(uint32_t dev)
{
    buffer_cache_t *cache = bcache_get_global();
    if (!cache) return NULL;

    // Read superblock (Block 1)
    bcache_entry_t *entry = bcache_get_or_read(cache, dev, 1, NULL);
    if (!entry) return NULL;

    minix3_sb_t *msb = malloc(sizeof(minix3_sb_t));
    if (!msb) {
        bcache_release(cache, entry);
        return NULL;
    }
    memset(msb, 0, sizeof(*msb));

    struct superblock *sb = (struct superblock *)entry->data;
    msb->sb = *sb;
    msb->dev = dev;

    // Validate superblock (basic check)
    if (msb->sb.size == 0 || msb->sb.nblocks == 0) {
        printf("MINIX3: Invalid superblock on dev %u\n", dev);
        free(msb);
        bcache_release(cache, entry);
        return NULL;
    }

    atomic_store(&msb->refcount, 1);
    bcache_release(cache, entry);

    return msb;
}

int minix3_write_super(minix3_sb_t *sb)
{
    if (!sb) return -1;
    // Superblock is typically read-only unless we resize fs
    return 0;
}

int minix3_sync(minix3_sb_t *sb)
{
    if (!sb) return -1;
    buffer_cache_t *cache = bcache_get_global();
    if (cache) {
        bcache_flush_dev(cache, sb->dev);
    }
    return 0;
}

/*******************************************************************************
 * INODE OPERATIONS
 ******************************************************************************/

minix3_inode_t* minix3_read_inode(minix3_sb_t *sb, uint32_t inum)
{
    if (!sb || inum == 0) return NULL;

    buffer_cache_t *cache = bcache_get_global();
    if (!cache) return NULL;

    minix3_inode_t *inode = malloc(sizeof(minix3_inode_t));
    if (!inode) return NULL;
    memset(inode, 0, sizeof(*inode));

    inode->dev = sb->dev;
    inode->inum = inum;

    // Calculate block number
    uint32_t blk = IBLOCK(inum, sb->sb);
    bcache_entry_t *entry = bcache_get_or_read(cache, sb->dev, blk, NULL);
    if (!entry) {
        free(inode);
        return NULL;
    }

    struct dinode *di = (struct dinode *)entry->data + (inum % IPB);
    inode->di = *di;

    bcache_release(cache, entry);
    atomic_store(&inode->dirty, 0);

    return inode;
}

int minix3_write_inode(minix3_sb_t *sb, minix3_inode_t *inode)
{
    if (!sb || !inode) return -1;

    buffer_cache_t *cache = bcache_get_global();
    if (!cache) return -1;

    uint32_t blk = IBLOCK(inode->inum, sb->sb);
    // Use NULL capability for inode metadata (system access)
    bcache_entry_t *entry = bcache_get_or_read(cache, sb->dev, blk, NULL);
    if (!entry) return -1;

    struct dinode *di = (struct dinode *)entry->data + (inode->inum % IPB);
    *di = inode->di;

    atomic_fetch_or(&entry->flags, BCACHE_DIRTY);
    bcache_release(cache, entry);

    atomic_store(&inode->dirty, 0);
    return 0;
}

/*******************************************************************************
 * BLOCK OPERATIONS
 ******************************************************************************/

uint32_t minix3_alloc_block(minix3_sb_t *sb)
{
    if (!sb) return 0;

    buffer_cache_t *cache = bcache_get_global();
    if (!cache) return 0;

    // Scan bitmap blocks
    uint32_t total_blocks = sb->sb.size; // Total fs blocks
    uint32_t bmap_block = sb->sb.bmapstart;

    // Loop through bitmap blocks
    for (uint32_t b = 0; b < total_blocks; b += BPB) {
        bcache_entry_t *entry = bcache_get_or_read(cache, sb->dev, bmap_block, NULL);
        if (!entry) return 0;

        uint8_t *bitmap = (uint8_t *)entry->data;
        for (int bi = 0; bi < BPB && b + bi < total_blocks; bi++) {
            int m = 1 << (bi % 8);
            if ((bitmap[bi/8] & m) == 0) {
                // Found free block
                bitmap[bi/8] |= m; // Mark used
                atomic_fetch_or(&entry->flags, BCACHE_DIRTY);
                bcache_release(cache, entry);
                return b + bi;
            }
        }
        bcache_release(cache, entry);
        bmap_block++;
    }

    return 0; // No free blocks
}

int minix3_free_block(minix3_sb_t *sb, uint32_t block)
{
    if (!sb || block == 0 || block >= sb->sb.size) return -1;

    buffer_cache_t *cache = bcache_get_global();
    if (!cache) return -1;

    uint32_t bmap_block = BBLOCK(block, sb->sb);
    bcache_entry_t *entry = bcache_get_or_read(cache, sb->dev, bmap_block, NULL);
    if (!entry) return -1;

    uint8_t *bitmap = (uint8_t *)entry->data;
    int bi = block % BPB;
    int m = 1 << (bi % 8);

    bitmap[bi/8] &= ~m; // Clear bit

    atomic_fetch_or(&entry->flags, BCACHE_DIRTY);
    bcache_release(cache, entry);
    return 0;
}

uint32_t minix3_bmap(minix3_sb_t *sb, minix3_inode_t *inode,
                     uint32_t block_num, bool alloc)
{
    if (!sb || !inode) return 0;

    // Direct blocks
    if (block_num < NDIRECT) {
        if (inode->di.addrs[block_num] == 0) {
            if (!alloc) return 0;
            uint32_t new_blk = minix3_alloc_block(sb);
            if (new_blk == 0) return 0;
            inode->di.addrs[block_num] = new_blk;
            atomic_store(&inode->dirty, 1);
        }
        return inode->di.addrs[block_num];
    }

    block_num -= NDIRECT;

    // Indirect block
    if (block_num < NINDIRECT) {
        uint32_t indirect_blk = inode->di.addrs[NDIRECT];
        if (indirect_blk == 0) {
            if (!alloc) return 0;
            indirect_blk = minix3_alloc_block(sb);
            if (indirect_blk == 0) return 0;
            inode->di.addrs[NDIRECT] = indirect_blk;

            // Zero the new indirect block
            buffer_cache_t *cache = bcache_get_global();
            bcache_entry_t *entry = bcache_get_or_read(cache, sb->dev, indirect_blk, NULL);
            if (entry) {
                memset(entry->data, 0, BSIZE);
                atomic_fetch_or(&entry->flags, BCACHE_DIRTY);
                bcache_release(cache, entry);
            }
            atomic_store(&inode->dirty, 1);
        }

        buffer_cache_t *cache = bcache_get_global();
        bcache_entry_t *entry = bcache_get_or_read(cache, sb->dev, indirect_blk, NULL);
        if (!entry) return 0;

        uint32_t *addrs = (uint32_t *)entry->data;
        uint32_t addr = addrs[block_num];

        if (addr == 0 && alloc) {
            addr = minix3_alloc_block(sb);
            if (addr) {
                addrs[block_num] = addr;
                atomic_fetch_or(&entry->flags, BCACHE_DIRTY);
            }
        }
        bcache_release(cache, entry);
        return addr;
    }

    return 0;
}

/*******************************************************************************
 * FILE I/O OPERATIONS (Internal)
 ******************************************************************************/

static ssize_t minix3_inode_read(minix3_sb_t *sb, minix3_inode_t *inode,
                                 void *buf, size_t count, uint64_t offset,
                                 const vfs_capability_t *cap)
{
    if (!sb || !inode || !buf) return -1;
    if (offset >= inode->di.size) return 0;
    if (offset + count > inode->di.size) count = inode->di.size - offset;

    buffer_cache_t *cache = bcache_get_global();
    if (!cache) return -1;

    size_t bytes_read = 0;
    uint8_t *dst = (uint8_t *)buf;

    while (bytes_read < count) {
        uint64_t fblk = (offset + bytes_read) / BSIZE;
        uint32_t boff = (offset + bytes_read) % BSIZE;
        uint32_t n = min(BSIZE - boff, count - bytes_read);

        uint32_t dblk = minix3_bmap(sb, inode, fblk, false);
        if (dblk == 0) {
            memset(dst + bytes_read, 0, n);
        } else {
            // Pass capability to buffer cache
            bcache_entry_t *entry = bcache_read_with_prefetch(cache, sb->dev, dblk, cap);
            if (!entry) return -1;
            memcpy(dst + bytes_read, (uint8_t*)entry->data + boff, n);
            bcache_release(cache, entry);
        }
        bytes_read += n;
    }
    return bytes_read;
}

static ssize_t minix3_inode_write(minix3_sb_t *sb, minix3_inode_t *inode,
                                  const void *buf, size_t count, uint64_t offset,
                                  const vfs_capability_t *cap)
{
    if (!sb || !inode || !buf) return -1;

    buffer_cache_t *cache = bcache_get_global();
    if (!cache) return -1;

    size_t bytes_written = 0;
    const uint8_t *src = (const uint8_t *)buf;

    while (bytes_written < count) {
        uint64_t fblk = (offset + bytes_written) / BSIZE;
        uint32_t boff = (offset + bytes_written) % BSIZE;
        uint32_t n = min(BSIZE - boff, count - bytes_written);

        uint32_t dblk = minix3_bmap(sb, inode, fblk, true);
        if (dblk == 0) break;

        // Pass capability to buffer cache
        bcache_entry_t *entry = bcache_get_or_read(cache, sb->dev, dblk, cap);
        if (!entry) break;

        memcpy((uint8_t*)entry->data + boff, src + bytes_written, n);
        atomic_fetch_or(&entry->flags, BCACHE_DIRTY);
        bcache_release(cache, entry);

        bytes_written += n;
    }

    if (bytes_written > 0) {
        if (offset + bytes_written > inode->di.size) {
            inode->di.size = offset + bytes_written;
            atomic_store(&inode->dirty, 1);
        }
        atomic_store(&inode->dirty, 1);
    }
    return bytes_written;
}

/*******************************************************************************
 * DIRECTORY OPERATIONS
 ******************************************************************************/

uint32_t minix3_dir_lookup(minix3_sb_t *sb, minix3_inode_t *dir,
                           const char *name, uint32_t len)
{
    if (dir->di.type != T_DIR) return 0;

    struct dirent de;
    for (uint32_t off = 0; off < dir->di.size; off += sizeof(de)) {
        if (minix3_inode_read(sb, dir, &de, sizeof(de), off, NULL) != sizeof(de))
            break;
        if (de.inum == 0) continue;

        // Ensure name is compared correctly (up to DIRSIZ)
        // name from VFS might not be null terminated if it's exactly len
        if (strlen(name) > DIRSIZ) return 0; // name too long

        if (strncmp(name, de.name, DIRSIZ) == 0) {
             return de.inum;
        }
    }
    return 0;
}

static int minix3_dir_link(minix3_sb_t *sb, minix3_inode_t *dir,
                          const char *name, uint32_t len, uint32_t inum)
{
    struct dirent de;
    uint32_t off;

    // Check if name exists
    if (minix3_dir_lookup(sb, dir, name, len) != 0) return -1;

    // Find empty slot
    for (off = 0; off < dir->di.size; off += sizeof(de)) {
        if (minix3_inode_read(sb, dir, &de, sizeof(de), off, NULL) != sizeof(de))
            break;
        if (de.inum == 0) break;
    }

    memset(&de, 0, sizeof(de));
    strncpy(de.name, name, DIRSIZ);
    de.inum = (uint16_t)inum;

    if (minix3_inode_write(sb, dir, &de, sizeof(de), off, NULL) != sizeof(de))
        return -1;

    return 0;
}

static int minix3_dir_unlink(minix3_sb_t *sb, minix3_inode_t *dir, const char *name, uint32_t len)
{
    struct dirent de;
    for (uint32_t off = 0; off < dir->di.size; off += sizeof(de)) {
        if (minix3_inode_read(sb, dir, &de, sizeof(de), off, NULL) != sizeof(de))
            break;

        if (de.inum != 0 && strncmp(name, de.name, DIRSIZ) == 0) {
            de.inum = 0;
            if (minix3_inode_write(sb, dir, &de, sizeof(de), off, NULL) != sizeof(de))
                return -1;
            return 0;
        }
    }
    return -1;
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

    /* Allocate MINIX inode structure wrapper */
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
    if (!sb || !sb->fs_private || inum == 0) return NULL;
    minix3_sb_t *m3sb = (minix3_sb_t *)sb->fs_private;

    minix3_inode_t *m3inode = minix3_read_inode(m3sb, (uint32_t)inum);
    if (!m3inode) return NULL;

    struct vfs_inode *inode = malloc(sizeof(struct vfs_inode));
    if (!inode) {
        free(m3inode);
        return NULL;
    }

    memset(inode, 0, sizeof(*inode));
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
    if (!dir || !dir->fs_private || !dir->sb || !dir->sb->fs_private || !name) return 0;
    minix3_inode_t *m3dir = (minix3_inode_t *)dir->fs_private;
    minix3_sb_t *m3sb = (minix3_sb_t *)dir->sb->fs_private;
    return minix3_dir_lookup(m3sb, m3dir, name, len);
}

static uint32_t minix3_alloc_inode_internal(minix3_sb_t *sb, short type)
{
    // Linear scan of inodes to find free one
    for (uint32_t i = 1; i < sb->sb.ninodes; i++) {
        minix3_inode_t *node = minix3_read_inode(sb, i);
        if (node) {
            if (node->di.type == 0) {
                // Found free
                memset(&node->di, 0, sizeof(node->di));
                node->di.type = type;
                node->di.nlink = 1;
                atomic_store(&node->dirty, 1);
                minix3_write_inode(sb, node);
                free(node);
                return i;
            }
            free(node);
        }
    }
    return 0;
}

static struct vfs_inode* minix3_vfs_create(struct vfs_inode *dir, const char *name,
                                           uint32_t len, uint16_t mode)
{
    if (!dir || !dir->fs_private || !dir->sb || !dir->sb->fs_private || !name) return NULL;
    minix3_inode_t *m3dir = (minix3_inode_t *)dir->fs_private;
    minix3_sb_t *m3sb = (minix3_sb_t *)dir->sb->fs_private;

    uint32_t inum = minix3_alloc_inode_internal(m3sb, T_FILE);
    if (inum == 0) return NULL;

    if (minix3_dir_link(m3sb, m3dir, name, len, inum) < 0) {
        return NULL;
    }

    return minix3_vfs_read_inode(dir->sb, inum);
}

static int minix3_vfs_mkdir(struct vfs_inode *dir, const char *name,
                            uint32_t len, uint16_t mode)
{
    if (!dir || !dir->fs_private || !dir->sb || !dir->sb->fs_private || !name) return -1;
    minix3_inode_t *m3dir = (minix3_inode_t *)dir->fs_private;
    minix3_sb_t *m3sb = (minix3_sb_t *)dir->sb->fs_private;

    uint32_t inum = minix3_alloc_inode_internal(m3sb, T_DIR);
    if (inum == 0) return -1;

    if (minix3_dir_link(m3sb, m3dir, name, len, inum) < 0) return -1;

    // Initialize . and ..
    minix3_inode_t *newdir = minix3_read_inode(m3sb, inum);
    if (newdir) {
        minix3_dir_link(m3sb, newdir, ".", 1, inum);
        minix3_dir_link(m3sb, newdir, "..", 2, m3dir->inum);
        free(newdir);
    }
    return 0;
}

static int minix3_vfs_unlink(struct vfs_inode *dir, const char *name, uint32_t len)
{
    if (!dir || !dir->fs_private || !dir->sb || !dir->sb->fs_private || !name) return -1;
    minix3_inode_t *m3dir = (minix3_inode_t *)dir->fs_private;
    minix3_sb_t *m3sb = (minix3_sb_t *)dir->sb->fs_private;

    // TODO: Decrement link count of victim inode (requires looking it up first)
    // For now, just unlink name
    return minix3_dir_unlink(m3sb, m3dir, name, len);
}

static int minix3_vfs_rmdir(struct vfs_inode *dir, const char *name, uint32_t len)
{
    return minix3_vfs_unlink(dir, name, len);
}

static int minix3_vfs_open(struct vfs_inode *inode, struct vfs_file *file)
{
    return 0;
}

static int minix3_vfs_release(struct vfs_file *file)
{
    return 0;
}

static ssize_t minix3_vfs_read(struct vfs_file *file, void *buf,
                               size_t count, uint64_t offset)
{
    if (!file || !file->inode || !file->inode->fs_private ||
        !file->inode->sb || !file->inode->sb->fs_private || !buf) return -1;

    minix3_inode_t *m3inode = (minix3_inode_t *)file->inode->fs_private;
    minix3_sb_t *m3sb = (minix3_sb_t *)file->inode->sb->fs_private;

    return minix3_inode_read(m3sb, m3inode, buf, count, offset, &file->capability);
}

static ssize_t minix3_vfs_write(struct vfs_file *file, const void *buf,
                                size_t count, uint64_t offset)
{
    if (!file || !file->inode || !file->inode->fs_private ||
        !file->inode->sb || !file->inode->sb->fs_private || !buf) return -1;

    minix3_inode_t *m3inode = (minix3_inode_t *)file->inode->fs_private;
    minix3_sb_t *m3sb = (minix3_sb_t *)file->inode->sb->fs_private;

    return minix3_inode_write(m3sb, m3inode, buf, count, offset, &file->capability);
}

static int minix3_vfs_fsync(struct vfs_file *file)
{
    if (!file || !file->inode) return -1;
    return minix3_vfs_write_inode(file->inode);
}

static int minix3_vfs_readdir(struct vfs_file *file,
                              int (*callback)(void *, const char *, uint64_t),
                              void *ctx)
{
    if (!file || !callback || !file->inode) return -1;
    minix3_sb_t *msb = (minix3_sb_t *)file->inode->sb->fs_private;
    minix3_inode_t *m3inode = (minix3_inode_t *)file->inode->fs_private;

    struct dirent de;
    for (uint32_t off = 0; off < m3inode->di.size; off += sizeof(de)) {
        if (minix3_inode_read(msb, m3inode, &de, sizeof(de), off, &file->capability) != sizeof(de))
            break;
        if (de.inum == 0) continue;

        callback(ctx, de.name, de.inum);
    }
    return 0;
}

