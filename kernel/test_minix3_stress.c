#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <assert.h>
#include <time.h>
#include <stdatomic.h>

// Mock kernel headers/types
#include "vfs.h"
#include "minix3_fs.h"
#include "buffer_cache.h"

// Stubs for kernel symbols
void panic(const char *s) {
    fprintf(stderr, "PANIC: %s\n", s);
    abort();
}

// RAM Disk
#define RAMDISK_SIZE (10 * 1024 * 1024) // 10MB
#define BLOCKS (RAMDISK_SIZE / 512)
static uint8_t *ramdisk_data;

void ramdisk_init() {
    ramdisk_data = malloc(RAMDISK_SIZE);
    memset(ramdisk_data, 0, RAMDISK_SIZE);
}

// BCache IO Stubs
int bcache_io_read(buffer_cache_t *cache, bcache_entry_t *entry) {
    if (entry->blockno >= BLOCKS) return -1;
    memcpy(entry->data, ramdisk_data + entry->blockno * 512, 512);
    atomic_fetch_or(&entry->flags, BCACHE_VALID);
    return 0;
}

int bcache_io_write(buffer_cache_t *cache, bcache_entry_t *entry) {
    if (entry->blockno >= BLOCKS) return -1;
    memcpy(ramdisk_data + entry->blockno * 512, entry->data, 512);
    atomic_fetch_and(&entry->flags, ~BCACHE_DIRTY);
    return 0;
}

int bcache_io_read_async(buffer_cache_t *cache, bcache_entry_t *entry) {
    return bcache_io_read(cache, entry);
}

int bcache_io_flush_device(buffer_cache_t *cache, uint32_t dev) {
    return 0;
}

bool bcache_io_device_exists(uint32_t dev) {
    return true;
}

// MKFS Logic (Simplified xv6 layout)
// IPB is defined in fs.h

void mkfs() {
    struct superblock sb;
    sb.size = BLOCKS;
    sb.nblocks = BLOCKS - 100;
    sb.ninodes = 200;
    sb.nlog = 30;
    sb.logstart = 2;
    sb.inodestart = 2 + 30;
    sb.bmapstart = 2 + 30 + (200/IPB + 1);

    // Write SB
    memcpy(ramdisk_data + 512, &sb, sizeof(sb));

    // Initialize root inode (inum 1)
    uint32_t root_addr = sb.inodestart * 512 + (1 * sizeof(struct dinode));
    struct dinode root;
    memset(&root, 0, sizeof(root));
    root.type = T_DIR;
    root.nlink = 1;
    root.size = 0;
    memcpy(ramdisk_data + root_addr, &root, sizeof(root));

    // Initialize Bitmap: Mark metadata blocks as used
    // sb.bmapstart points to the start of bitmap blocks.
    // We need to mark blocks 0 to bmapstart (approx) as used.
    // Let's mark the first 100 blocks as used to cover boot, sb, log, inodes, and bitmap itself.
    if (sb.bmapstart < BLOCKS) {
        uint8_t *bmap = ramdisk_data + sb.bmapstart * 512;
        for (int i = 0; i < 100; i++) {
            bmap[i/8] |= (1 << (i%8));
        }
    }
}

int main() {
    ramdisk_init();
    mkfs();

    printf("Initializing subsystems...\n");
    vfs_init();
    minix3_init();
    bcache_get_global();

    printf("Mounting filesystem...\n");
    if (vfs_mount("ramdisk", "/mnt", FS_TYPE_MINIX3, 0) != 0) {
        printf("Mount failed\n");
        return 1;
    }

    struct vfs_inode *root = vfs_path_lookup("/mnt");
    if (!root) {
        printf("Root lookup failed\n");
        return 1;
    }
    printf("Root inode found: %lu\n", root->inum);
    vfs_inode_put(root);

    // Test 1: Directory Explosion
    printf("Test 1: Directory Explosion...\n");
    struct vfs_inode *dir = vfs_path_lookup("/mnt");
    for (int i = 0; i < 100; i++) {
        char name[32];
        sprintf(name, "file%d", i);
        struct vfs_inode *newfile = dir->sb->i_op->create(dir, name, strlen(name), 0644);
        if (!newfile) {
            printf("Failed to create %s\n", name);
            return 1;
        }
        vfs_inode_put(newfile);
    }
    printf("Created 100 files.\n");

    // Test 2: Large File
    printf("Test 2: Large File...\n");
    struct vfs_inode *lfile = dir->sb->i_op->create(dir, "large", 5, 0644);
    if (!lfile) {
        printf("Failed to create large file\n");
        return 1;
    }

    // Write 20KB (40 blocks) -> triggers indirect
    char buf[512];
    for (int i = 0; i < 512; i++) buf[i] = (char)i;

    struct vfs_file f;
    f.inode = lfile;
    f.capability.rights = 0xFFFF; // Full rights

    for (int i = 0; i < 40; i++) {
        ssize_t written = lfile->sb->f_op->write(&f, buf, 512, i * 512);
        if (written != 512) {
            printf("Write failed at block %d\n", i);
            return 1;
        }
    }
    printf("Wrote 20KB.\n");

    // Read back verification
    char check[512];
    for (int i = 0; i < 40; i++) {
        ssize_t read = lfile->sb->f_op->read(&f, check, 512, i * 512);
        if (read != 512) {
            printf("Read failed at block %d\n", i);
            return 1;
        }
        if (memcmp(buf, check, 512) != 0) {
            printf("Data mismatch at block %d\n", i);
            return 1;
        }
    }
    printf("Verification successful.\n");
    vfs_inode_put(lfile);
    vfs_inode_put(dir);

    printf("All tests passed.\n");
    return 0;
}
