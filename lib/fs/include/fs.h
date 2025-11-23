/**
 * @file fs.h
 * @brief User-Space File System Structures (Phase 8)
 *
 * These structures match the xv6 on-disk layout exactly,
 * allowing us to read fs.img files created by xv6 mkfs.
 */

#ifndef LIBOS_FS_H
#define LIBOS_FS_H

#include <stdint.h>

// ═══════════════════════════════════════════════════════════════════════════
// File System Constants
// ═══════════════════════════════════════════════════════════════════════════

#define BSIZE       1024    // Block size (bytes)
#define ROOTINO     1       // Root directory inode number
#define NDIRECT     12      // Number of direct block pointers
#define NINDIRECT   (BSIZE / sizeof(uint32_t))  // Indirect block entries
#define MAXFILE     (NDIRECT + NINDIRECT)       // Max file size in blocks

#define DIRSIZ      14      // Max directory entry name length
#define IPB         (BSIZE / sizeof(struct dinode))  // Inodes per block

// File types
#define T_DIR       1       // Directory
#define T_FILE      2       // Regular file
#define T_DEVICE    3       // Device

// ═══════════════════════════════════════════════════════════════════════════
// On-Disk Structures
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Superblock - Describes the file system layout
 * Located at block 1 (block 0 is boot sector)
 */
struct superblock {
    uint32_t magic;         // Magic number (0x10203040 for xv6)
    uint32_t size;          // Size of file system image (blocks)
    uint32_t nblocks;       // Number of data blocks
    uint32_t ninodes;       // Number of inodes
    uint32_t nlog;          // Number of log blocks
    uint32_t logstart;      // Block number of first log block
    uint32_t inodestart;    // Block number of first inode block
    uint32_t bmapstart;     // Block number of first free map block
};

#define FSMAGIC 0x10203040

/**
 * On-disk inode structure
 * Describes a single file or directory
 */
struct dinode {
    int16_t  type;          // File type (T_DIR, T_FILE, T_DEVICE)
    int16_t  major;         // Major device number (T_DEVICE only)
    int16_t  minor;         // Minor device number (T_DEVICE only)
    int16_t  nlink;         // Number of links to inode
    uint32_t size;          // Size of file (bytes)
    uint32_t addrs[NDIRECT+1];  // Data block addresses (last is indirect)
};

/**
 * Directory entry
 * Each directory is an array of these
 */
struct dirent {
    uint16_t inum;          // Inode number (0 = unused entry)
    char name[DIRSIZ];      // File name (null-padded)
};

// ═══════════════════════════════════════════════════════════════════════════
// In-Memory Structures
// ═══════════════════════════════════════════════════════════════════════════

/**
 * In-memory inode (cached copy of dinode)
 */
struct inode {
    uint32_t dev;           // Device number
    uint32_t inum;          // Inode number
    int      ref;           // Reference count
    int      valid;         // Has been read from disk?

    // Copy of dinode fields
    int16_t  type;
    int16_t  major;
    int16_t  minor;
    int16_t  nlink;
    uint32_t size;
    uint32_t addrs[NDIRECT+1];
};

/**
 * Buffer (block cache entry)
 */
struct buf {
    int valid;              // Has been read from disk?
    int dirty;              // Needs to be written back?
    uint32_t dev;           // Device number
    uint32_t blockno;       // Block number
    uint8_t data[BSIZE];    // Block data
};

// ═══════════════════════════════════════════════════════════════════════════
// File System API
// ═══════════════════════════════════════════════════════════════════════════

// Initialization
int fs_init(void);

// Superblock
void readsb(int dev, struct superblock *sb);

// Block I/O
struct buf* bread(uint32_t dev, uint32_t blockno);
void bwrite(struct buf *b);
void brelse(struct buf *b);

// Inode operations
struct inode* iget(uint32_t dev, uint32_t inum);
void ilock(struct inode *ip);
void iunlock(struct inode *ip);
void iput(struct inode *ip);
int readi(struct inode *ip, void *dst, uint32_t off, uint32_t n);

// Directory operations
struct inode* dirlookup(struct inode *dp, const char *name, uint32_t *poff);
int namecmp(const char *s, const char *t);

// Path resolution
struct inode* namei(const char *path);

// High-level operations
int fs_ls(const char *path);

#endif // LIBOS_FS_H
