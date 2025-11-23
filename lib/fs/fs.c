/**
 * @file fs.c
 * @brief User-Space File System Logic (Phase 8)
 *
 * Implements inode operations, directory lookups, and path resolution.
 * Based on xv6 fs.c, adapted for user-space operation.
 */

#include "include/fs.h"
#include "../virtio/virtio.h"

// Forward declarations
extern void print(const char *s);
extern void print_hex(uint64_t n);
extern void bio_init(void);

// Global superblock (cached)
static struct superblock sb;
static int fs_initialized = 0;

// Simple inode cache
#define NINODE 16
static struct inode inode_cache[NINODE];

// ═══════════════════════════════════════════════════════════════════════════
// Helper Functions
// ═══════════════════════════════════════════════════════════════════════════

static void print_str(const char *s) { print(s); }

static void memcpy_local(void *dst, const void *src, uint32_t n) {
    uint8_t *d = (uint8_t *)dst;
    const uint8_t *s = (const uint8_t *)src;
    for (uint32_t i = 0; i < n; i++) d[i] = s[i];
}

static void memset_local(void *dst, int c, uint32_t n) {
    uint8_t *d = (uint8_t *)dst;
    for (uint32_t i = 0; i < n; i++) d[i] = (uint8_t)c;
}

// ═══════════════════════════════════════════════════════════════════════════
// Superblock
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Read the superblock from disk
 */
void readsb(int dev, struct superblock *sb_out) {
    struct buf *bp = bread(dev, 1);  // Superblock is at block 1
    if (!bp) {
        print("[FS] ERROR: Could not read superblock!\n");
        return;
    }
    memcpy_local(sb_out, bp->data, sizeof(*sb_out));
    brelse(bp);
}

// ═══════════════════════════════════════════════════════════════════════════
// Inode Operations
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Get an inode from cache or allocate a new cache entry
 */
struct inode* iget(uint32_t dev, uint32_t inum) {
    struct inode *empty = 0;

    // Look for cached inode
    for (int i = 0; i < NINODE; i++) {
        if (inode_cache[i].ref > 0 &&
            inode_cache[i].dev == dev &&
            inode_cache[i].inum == inum) {
            inode_cache[i].ref++;
            return &inode_cache[i];
        }
        if (empty == 0 && inode_cache[i].ref == 0) {
            empty = &inode_cache[i];
        }
    }

    // Allocate new cache entry
    if (empty == 0) {
        print("[FS] ERROR: No free inode cache entries!\n");
        return 0;
    }

    empty->dev = dev;
    empty->inum = inum;
    empty->ref = 1;
    empty->valid = 0;
    return empty;
}

/**
 * Lock an inode and read from disk if necessary
 */
void ilock(struct inode *ip) {
    if (!ip || ip->ref < 1) {
        print("[FS] ERROR: ilock on invalid inode!\n");
        return;
    }

    if (ip->valid) return;  // Already loaded

    // Read inode from disk
    uint32_t block = sb.inodestart + ip->inum / IPB;
    struct buf *bp = bread(ip->dev, block);
    if (!bp) {
        print("[FS] ERROR: Could not read inode block!\n");
        return;
    }

    struct dinode *dip = (struct dinode *)bp->data + ip->inum % IPB;
    ip->type = dip->type;
    ip->major = dip->major;
    ip->minor = dip->minor;
    ip->nlink = dip->nlink;
    ip->size = dip->size;
    memcpy_local(ip->addrs, dip->addrs, sizeof(ip->addrs));
    brelse(bp);

    ip->valid = 1;

    if (ip->type == 0) {
        print("[FS] WARNING: ilock on type 0 inode!\n");
    }
}

/**
 * Unlock an inode (no-op in simple implementation)
 */
void iunlock(struct inode *ip) {
    (void)ip;
    // No locking in single-threaded user-space
}

/**
 * Release a reference to an inode
 */
void iput(struct inode *ip) {
    if (!ip) return;
    if (ip->ref > 0) ip->ref--;
}

/**
 * Get the disk block number for the nth block of an inode
 */
static uint32_t bmap(struct inode *ip, uint32_t bn) {
    if (bn < NDIRECT) {
        return ip->addrs[bn];
    }

    bn -= NDIRECT;
    if (bn < NINDIRECT) {
        // Load indirect block
        if (ip->addrs[NDIRECT] == 0) return 0;

        struct buf *bp = bread(ip->dev, ip->addrs[NDIRECT]);
        if (!bp) return 0;

        uint32_t *addrs = (uint32_t *)bp->data;
        uint32_t addr = addrs[bn];
        brelse(bp);
        return addr;
    }

    print("[FS] ERROR: bmap out of range!\n");
    return 0;
}

/**
 * Read data from an inode
 */
int readi(struct inode *ip, void *dst, uint32_t off, uint32_t n) {
    if (!ip->valid) {
        print("[FS] ERROR: readi on invalid inode!\n");
        return -1;
    }

    if (off > ip->size || off + n < off) return 0;
    if (off + n > ip->size) n = ip->size - off;

    uint32_t tot = 0;
    uint8_t *d = (uint8_t *)dst;

    for (; tot < n; tot += BSIZE, off += BSIZE, d += BSIZE) {
        uint32_t bn = bmap(ip, off / BSIZE);
        if (bn == 0) {
            // Sparse file - zero fill
            uint32_t m = n - tot;
            if (m > BSIZE) m = BSIZE;
            memset_local(d, 0, m);
            continue;
        }

        struct buf *bp = bread(ip->dev, bn);
        if (!bp) return -1;

        uint32_t m = n - tot;
        if (m > BSIZE - off % BSIZE) m = BSIZE - off % BSIZE;
        memcpy_local(d, bp->data + off % BSIZE, m);
        brelse(bp);
    }

    return tot;
}

// ═══════════════════════════════════════════════════════════════════════════
// Directory Operations
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Compare two directory names
 */
int namecmp(const char *s, const char *t) {
    int i;
    for (i = 0; i < DIRSIZ && s[i] && t[i]; i++) {
        if (s[i] != t[i]) return s[i] - t[i];
    }
    if (i < DIRSIZ) {
        if (s[i]) return 1;
        if (t[i]) return -1;
    }
    return 0;
}

/**
 * Look up a name in a directory
 */
struct inode* dirlookup(struct inode *dp, const char *name, uint32_t *poff) {
    if (dp->type != T_DIR) {
        print("[FS] ERROR: dirlookup not DIR!\n");
        return 0;
    }

    struct dirent de;
    for (uint32_t off = 0; off < dp->size; off += sizeof(de)) {
        if (readi(dp, &de, off, sizeof(de)) != sizeof(de)) {
            print("[FS] ERROR: dirlookup read!\n");
            return 0;
        }
        if (de.inum == 0) continue;
        if (namecmp(name, de.name) == 0) {
            if (poff) *poff = off;
            return iget(dp->dev, de.inum);
        }
    }
    return 0;
}

// ═══════════════════════════════════════════════════════════════════════════
// Path Resolution
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Skip path element, return pointer to next element
 */
static const char* skipelem(const char *path, char *name) {
    while (*path == '/') path++;
    if (*path == 0) return 0;

    const char *s = path;
    while (*path != '/' && *path != 0) path++;

    int len = path - s;
    if (len >= DIRSIZ) {
        memcpy_local(name, s, DIRSIZ);
    } else {
        memcpy_local(name, s, len);
        name[len] = 0;
    }
    while (*path == '/') path++;
    return path;
}

/**
 * Look up a path and return the inode
 */
struct inode* namei(const char *path) {
    struct inode *ip;
    char name[DIRSIZ];

    if (*path == '/') {
        ip = iget(0, ROOTINO);
    } else {
        // Relative path from root (no CWD concept yet)
        ip = iget(0, ROOTINO);
    }

    while ((path = skipelem(path, name)) != 0) {
        ilock(ip);
        if (ip->type != T_DIR) {
            iput(ip);
            return 0;
        }
        struct inode *next = dirlookup(ip, name, 0);
        iput(ip);
        if (next == 0) return 0;
        ip = next;
    }

    ilock(ip);
    return ip;
}

// ═══════════════════════════════════════════════════════════════════════════
// High-Level Operations
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Print a number as decimal
 */
static void print_uint(uint32_t n) {
    if (n == 0) { print("0"); return; }
    char buf[12];
    int i = 0;
    while (n > 0) { buf[i++] = '0' + (n % 10); n /= 10; }
    char out[12];
    for (int j = 0; j < i; j++) out[j] = buf[i - 1 - j];
    out[i] = '\0';
    print(out);
}

/**
 * List directory contents
 */
int fs_ls(const char *path) {
    struct inode *dp = namei(path);
    if (!dp) {
        print("[FS] ERROR: Path not found: ");
        print(path);
        print("\n");
        return -1;
    }

    if (dp->type != T_DIR) {
        print("[FS] ERROR: Not a directory: ");
        print(path);
        print("\n");
        iput(dp);
        return -1;
    }

    print("\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("  Directory: ");
    print(path);
    print("\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("  Type  Size       Name\n");
    print("  ----  ---------  --------------\n");

    struct dirent de;
    for (uint32_t off = 0; off < dp->size; off += sizeof(de)) {
        if (readi(dp, &de, off, sizeof(de)) != sizeof(de)) break;
        if (de.inum == 0) continue;

        // Get inode for type and size info
        struct inode *ip = iget(dp->dev, de.inum);
        ilock(ip);

        // Print type
        print("  ");
        switch (ip->type) {
            case T_DIR:    print("DIR "); break;
            case T_FILE:   print("FILE"); break;
            case T_DEVICE: print("DEV "); break;
            default:       print("??? "); break;
        }

        // Print size (right-aligned)
        print("  ");
        uint32_t sz = ip->size;
        if (sz < 10) print("        ");
        else if (sz < 100) print("       ");
        else if (sz < 1000) print("      ");
        else if (sz < 10000) print("     ");
        else if (sz < 100000) print("    ");
        else if (sz < 1000000) print("   ");
        else print("  ");
        print_uint(ip->size);

        // Print name
        print("  ");
        // Null-terminate name safely
        char namebuf[DIRSIZ + 1];
        for (int i = 0; i < DIRSIZ; i++) namebuf[i] = de.name[i];
        namebuf[DIRSIZ] = '\0';
        print(namebuf);
        print("\n");

        iput(ip);
    }

    print("═══════════════════════════════════════════════════════════\n");
    print("\n");

    iput(dp);
    return 0;
}

// ═══════════════════════════════════════════════════════════════════════════
// Initialization
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Initialize the file system
 */
int fs_init(void) {
    if (fs_initialized) return 0;

    print("[FS] Initializing file system...\n");

    // Initialize block I/O
    bio_init();

    // Initialize inode cache
    for (int i = 0; i < NINODE; i++) {
        inode_cache[i].ref = 0;
        inode_cache[i].valid = 0;
    }

    // Read superblock
    readsb(0, &sb);

    print("[FS] Superblock:\n");
    print("     Magic:      ");
    print_hex(sb.magic);
    print("\n     Size:       ");
    print_uint(sb.size);
    print(" blocks\n");
    print("     Inodes:     ");
    print_uint(sb.ninodes);
    print("\n     Data:       ");
    print_uint(sb.nblocks);
    print(" blocks\n");
    print("     Inode start: block ");
    print_uint(sb.inodestart);
    print("\n");

    if (sb.magic != FSMAGIC) {
        print("[FS] WARNING: Invalid magic number!\n");
        print("     Expected: ");
        print_hex(FSMAGIC);
        print("\n     Got:      ");
        print_hex(sb.magic);
        print("\n");
    }

    fs_initialized = 1;
    print("[FS] File system ready.\n\n");
    return 0;
}
