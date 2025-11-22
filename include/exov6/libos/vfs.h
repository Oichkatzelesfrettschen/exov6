/**
 * @file vfs.h
 * @brief Virtual File System (VFS) Layer
 *
 * Provides a unified abstraction layer for multiple filesystem types:
 * - ext4 (extent-based with journaling)
 * - F2FS (Flash-Friendly File System)
 * - MINIX v3 (simple educational filesystem)
 *
 * Integrates with PDAC (Probabilistic DAG Algebra with Capabilities)
 * for fine-grained access control.
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <stdatomic.h>
#include <sys/types.h>
#include "fs.h"

#ifdef __cplusplus
extern "C" {
#endif

/*******************************************************************************
 * FORWARD DECLARATIONS
 ******************************************************************************/

struct vfs_inode;
struct vfs_dentry;
struct vfs_file;
struct vfs_super_block;
struct vfs_mount;

/*******************************************************************************
 * FILESYSTEM TYPES
 ******************************************************************************/

/**
 * @brief Supported filesystem types
 */
typedef enum {
    FS_TYPE_NONE = 0,
    FS_TYPE_MINIX3,       /**< MINIX v3 filesystem */
    FS_TYPE_EXT4,         /**< ext4 filesystem */
    FS_TYPE_F2FS,         /**< Flash-Friendly File System */
    FS_TYPE_PROCFS,       /**< Process filesystem (pseudo) */
    FS_TYPE_DEVFS,        /**< Device filesystem (pseudo) */
    FS_TYPE_MAX
} fs_type_t;

/**
 * @brief Filesystem feature flags
 */
#define VFS_FEATURE_JOURNALING    (1 << 0)  /**< Supports journaling */
#define VFS_FEATURE_EXTENTS       (1 << 1)  /**< Uses extent trees */
#define VFS_FEATURE_FLASH_OPT     (1 << 2)  /**< Flash optimized */
#define VFS_FEATURE_LARGE_FILES   (1 << 3)  /**< Files >4GB */
#define VFS_FEATURE_SYMLINKS      (1 << 4)  /**< Symbolic links */
#define VFS_FEATURE_HARD_LINKS    (1 << 5)  /**< Hard links */
#define VFS_FEATURE_CAPABILITIES  (1 << 6)  /**< PDAC capabilities */

/*******************************************************************************
 * CAPABILITY INTEGRATION (PDAC)
 ******************************************************************************/

/**
 * @brief File access rights (PDAC)
 */
typedef enum {
    CAP_READ      = (1 << 0),  /**< Read permission */
    CAP_WRITE     = (1 << 1),  /**< Write permission */
    CAP_EXECUTE   = (1 << 2),  /**< Execute permission */
    CAP_APPEND    = (1 << 3),  /**< Append-only permission */
    CAP_DELETE    = (1 << 4),  /**< Delete permission */
    CAP_SETATTR   = (1 << 5),  /**< Set attributes permission */
    CAP_GETATTR   = (1 << 6),  /**< Get attributes permission */
    CAP_READDIR   = (1 << 7),  /**< Read directory permission */
    CAP_CHOWN     = (1 << 8),  /**< Change ownership permission */
    CAP_ALL       = 0x1FF      /**< All permissions */
} vfs_cap_rights_t;

/**
 * @brief File capability
 */
typedef struct {
    uint64_t inode_num;        /**< Inode number */
    uint32_t rights;           /**< Access rights (vfs_cap_rights_t) */
    uint32_t owner_uid;        /**< Owner user ID */
    uint64_t expiry;           /**< Expiration timestamp (0 = never) */
    uint64_t signature;        /**< Cryptographic signature */
} vfs_capability_t;

/*******************************************************************************
 * SUPERBLOCK OPERATIONS
 ******************************************************************************/

struct vfs_super_operations {
    /**
     * @brief Allocate and initialize an inode
     *
     * @param sb    Superblock
     * @return New inode or NULL on error
     */
    struct vfs_inode* (*alloc_inode)(struct vfs_super_block *sb);

    /**
     * @brief Destroy an inode
     *
     * @param inode  Inode to destroy
     */
    void (*destroy_inode)(struct vfs_inode *inode);

    /**
     * @brief Write inode to disk
     *
     * @param inode  Inode to write
     * @return 0 on success, negative on error
     */
    int (*write_inode)(struct vfs_inode *inode);

    /**
     * @brief Read inode from disk
     *
     * @param sb     Superblock
     * @param inum   Inode number
     * @return Inode or NULL on error
     */
    struct vfs_inode* (*read_inode)(struct vfs_super_block *sb, uint64_t inum);

    /**
     * @brief Write superblock to disk
     *
     * @param sb  Superblock
     * @return 0 on success, negative on error
     */
    int (*write_super)(struct vfs_super_block *sb);

    /**
     * @brief Sync filesystem to disk
     *
     * @param sb  Superblock
     * @return 0 on success, negative on error
     */
    int (*sync_fs)(struct vfs_super_block *sb);

    /**
     * @brief Get filesystem statistics
     *
     * @param sb     Superblock
     * @param stats  Output statistics
     * @return 0 on success, negative on error
     */
    int (*statfs)(struct vfs_super_block *sb, void *stats);
};

/*******************************************************************************
 * INODE OPERATIONS
 ******************************************************************************/

struct vfs_inode_operations {
    /**
     * @brief Look up a name in a directory
     *
     * @param dir   Directory inode
     * @param name  Name to look up
     * @param len   Name length
     * @return Inode number or 0 if not found
     */
    uint64_t (*lookup)(struct vfs_inode *dir, const char *name, uint32_t len);

    /**
     * @brief Create a new file
     *
     * @param dir    Directory inode
     * @param name   File name
     * @param len    Name length
     * @param mode   File mode
     * @return New inode or NULL on error
     */
    struct vfs_inode* (*create)(struct vfs_inode *dir, const char *name,
                                uint32_t len, uint16_t mode);

    /**
     * @brief Create a directory
     *
     * @param dir    Parent directory inode
     * @param name   Directory name
     * @param len    Name length
     * @param mode   Directory mode
     * @return 0 on success, negative on error
     */
    int (*mkdir)(struct vfs_inode *dir, const char *name,
                 uint32_t len, uint16_t mode);

    /**
     * @brief Remove a directory entry
     *
     * @param dir   Directory inode
     * @param name  Entry name
     * @param len   Name length
     * @return 0 on success, negative on error
     */
    int (*unlink)(struct vfs_inode *dir, const char *name, uint32_t len);

    /**
     * @brief Remove a directory
     *
     * @param dir   Parent directory inode
     * @param name  Directory name
     * @param len   Name length
     * @return 0 on success, negative on error
     */
    int (*rmdir)(struct vfs_inode *dir, const char *name, uint32_t len);

    /**
     * @brief Create a symbolic link
     *
     * @param dir     Directory inode
     * @param name    Link name
     * @param len     Name length
     * @param target  Link target
     * @return 0 on success, negative on error
     */
    int (*symlink)(struct vfs_inode *dir, const char *name,
                   uint32_t len, const char *target);

    /**
     * @brief Rename a file/directory
     *
     * @param old_dir   Old directory
     * @param old_name  Old name
     * @param old_len   Old name length
     * @param new_dir   New directory
     * @param new_name  New name
     * @param new_len   New name length
     * @return 0 on success, negative on error
     */
    int (*rename)(struct vfs_inode *old_dir, const char *old_name, uint32_t old_len,
                  struct vfs_inode *new_dir, const char *new_name, uint32_t new_len);
};

/*******************************************************************************
 * FILE OPERATIONS
 ******************************************************************************/

struct vfs_file_operations {
    /**
     * @brief Open a file
     *
     * @param inode  Inode to open
     * @param file   File structure
     * @return 0 on success, negative on error
     */
    int (*open)(struct vfs_inode *inode, struct vfs_file *file);

    /**
     * @brief Close a file
     *
     * @param file  File structure
     * @return 0 on success, negative on error
     */
    int (*release)(struct vfs_file *file);

    /**
     * @brief Read from a file
     *
     * @param file    File structure
     * @param buf     Output buffer
     * @param count   Bytes to read
     * @param offset  File offset
     * @return Bytes read or negative on error
     */
    ssize_t (*read)(struct vfs_file *file, void *buf,
                    size_t count, uint64_t offset);

    /**
     * @brief Write to a file
     *
     * @param file    File structure
     * @param buf     Input buffer
     * @param count   Bytes to write
     * @param offset  File offset
     * @return Bytes written or negative on error
     */
    ssize_t (*write)(struct vfs_file *file, const void *buf,
                     size_t count, uint64_t offset);

    /**
     * @brief Flush file data to disk
     *
     * @param file  File structure
     * @return 0 on success, negative on error
     */
    int (*fsync)(struct vfs_file *file);

    /**
     * @brief Read directory entries
     *
     * @param file      File structure (directory)
     * @param callback  Callback for each entry
     * @param ctx       Context for callback
     * @return 0 on success, negative on error
     */
    int (*readdir)(struct vfs_file *file,
                   int (*callback)(void *ctx, const char *name, uint64_t inum),
                   void *ctx);
};

/*******************************************************************************
 * VFS SUPERBLOCK
 ******************************************************************************/

/**
 * @brief VFS superblock
 */
struct vfs_super_block {
    /* Identification */
    fs_type_t fs_type;                 /**< Filesystem type */
    uint32_t magic;                    /**< Magic number */
    uint32_t features;                 /**< Feature flags */

    /* Size information */
    uint64_t total_blocks;             /**< Total blocks */
    uint64_t free_blocks;              /**< Free blocks */
    uint64_t total_inodes;             /**< Total inodes */
    uint64_t free_inodes;              /**< Free inodes */
    uint32_t block_size;               /**< Block size in bytes */

    /* Operations */
    const struct vfs_super_operations *s_op;
    const struct vfs_inode_operations *i_op;
    const struct vfs_file_operations *f_op;

    /* Mount information */
    struct vfs_mount *mount;           /**< Mount point */
    struct vfs_inode *root_inode;      /**< Root inode */

    /* Reference counting */
    _Atomic uint32_t refcount;         /**< Reference count */

    /* Filesystem-specific data */
    void *fs_private;                  /**< Private filesystem data */
};

/*******************************************************************************
 * VFS INODE
 ******************************************************************************/

/**
 * @brief VFS inode
 */
struct vfs_inode {
    /* Identification */
    uint64_t inum;                     /**< Inode number */
    struct vfs_super_block *sb;        /**< Superblock */

    /* File attributes */
    uint16_t mode;                     /**< File mode (type + permissions) */
    uint16_t nlink;                    /**< Number of hard links */
    uint32_t uid;                      /**< Owner user ID */
    uint32_t gid;                      /**< Owner group ID */
    uint64_t size;                     /**< File size in bytes */

    /* Timestamps */
    uint64_t atime;                    /**< Access time */
    uint64_t mtime;                    /**< Modification time */
    uint64_t ctime;                    /**< Change time */

    /* Caching state */
    _Atomic uint32_t state;            /**< Inode state flags */
    _Atomic uint32_t refcount;         /**< Reference count */

    /* PDAC capability */
    vfs_capability_t capability;       /**< Associated capability */

    /* Filesystem-specific data */
    void *fs_private;                  /**< Private filesystem data */
};

/**
 * @brief Inode state flags
 */
#define VFS_INODE_DIRTY      (1 << 0)  /**< Inode modified */
#define VFS_INODE_LOCKED     (1 << 1)  /**< Inode locked */
#define VFS_INODE_FREEING    (1 << 2)  /**< Inode being freed */
#define VFS_INODE_NEW        (1 << 3)  /**< Newly allocated */

/*******************************************************************************
 * VFS FILE
 ******************************************************************************/

/**
 * @brief VFS file handle
 */
struct vfs_file {
    struct vfs_inode *inode;           /**< Inode */
    uint32_t flags;                    /**< Open flags */
    uint32_t mode;                     /**< Open mode */
    uint64_t offset;                   /**< Current file offset */
    _Atomic uint32_t refcount;         /**< Reference count */

    /* PDAC capability check */
    vfs_capability_t capability;       /**< Capability for this file */

    void *private_data;                /**< Filesystem-specific data */
};

/**
 * @brief File open flags
 */
#define VFS_O_RDONLY    0x0000         /**< Read-only */
#define VFS_O_WRONLY    0x0001         /**< Write-only */
#define VFS_O_RDWR      0x0002         /**< Read-write */
#define VFS_O_CREAT     0x0040         /**< Create if not exists */
#define VFS_O_EXCL      0x0080         /**< Exclusive create */
#define VFS_O_TRUNC     0x0200         /**< Truncate */
#define VFS_O_APPEND    0x0400         /**< Append mode */
#define VFS_O_DIRECTORY 0x10000        /**< Must be directory */

/*******************************************************************************
 * VFS DENTRY (Directory Entry)
 ******************************************************************************/

/**
 * @brief VFS directory entry
 */
struct vfs_dentry {
    char name[256];                    /**< Entry name */
    uint32_t name_len;                 /**< Name length */
    struct vfs_inode *inode;           /**< Associated inode */
    struct vfs_dentry *parent;         /**< Parent dentry */
    _Atomic uint32_t refcount;         /**< Reference count */

    /* Hash chain for dentry cache */
    struct vfs_dentry *next;
};

/*******************************************************************************
 * VFS MOUNT
 ******************************************************************************/

/**
 * @brief VFS mount point
 */
struct vfs_mount {
    char mountpoint[256];              /**< Mount point path */
    struct vfs_super_block *sb;        /**< Superblock */
    struct vfs_dentry *root;           /**< Root dentry */
    uint32_t flags;                    /**< Mount flags */
    _Atomic uint32_t refcount;         /**< Reference count */

    struct vfs_mount *next;            /**< Next mount */
};

/**
 * @brief Mount flags
 */
#define VFS_MOUNT_RDONLY     (1 << 0)  /**< Read-only mount */
#define VFS_MOUNT_NOEXEC     (1 << 1)  /**< No execute */
#define VFS_MOUNT_NOSUID     (1 << 2)  /**< No suid */
#define VFS_MOUNT_NODEV      (1 << 3)  /**< No device files */

/*******************************************************************************
 * VFS API
 ******************************************************************************/

/**
 * @brief Initialize VFS subsystem
 *
 * @return 0 on success, negative on error
 */
int vfs_init(void);

/**
 * @brief Register a filesystem type
 *
 * @param type     Filesystem type
 * @param s_op     Superblock operations
 * @param i_op     Inode operations
 * @param f_op     File operations
 * @return 0 on success, negative on error
 */
int vfs_register_filesystem(fs_type_t type,
                            const struct vfs_super_operations *s_op,
                            const struct vfs_inode_operations *i_op,
                            const struct vfs_file_operations *f_op);

/**
 * @brief Mount a filesystem
 *
 * @param dev         Device path
 * @param mountpoint  Mount point path
 * @param fs_type     Filesystem type
 * @param flags       Mount flags
 * @return 0 on success, negative on error
 */
int vfs_mount(const char *dev, const char *mountpoint,
              fs_type_t fs_type, uint32_t flags);

/**
 * @brief Unmount a filesystem
 *
 * @param mountpoint  Mount point path
 * @return 0 on success, negative on error
 */
int vfs_umount(const char *mountpoint);

/**
 * @brief Get inode by path
 *
 * @param path  File path
 * @return Inode or NULL if not found
 */
struct vfs_inode* vfs_path_lookup(const char *path);

/**
 * @brief Allocate inode reference
 *
 * @param inode  Inode
 */
static inline void vfs_inode_get(struct vfs_inode *inode)
{
    if (inode) {
        atomic_fetch_add(&inode->refcount, 1);
    }
}

/**
 * @brief Release inode reference
 *
 * @param inode  Inode
 */
void vfs_inode_put(struct vfs_inode *inode);

/**
 * @brief Check if capability allows operation
 *
 * @param cap     Capability
 * @param rights  Required rights
 * @return true if allowed
 */
static inline bool vfs_cap_check(const vfs_capability_t *cap, uint32_t rights)
{
    if (!cap) return false;

    /* Check rights */
    if ((cap->rights & rights) != rights) {
        return false;
    }

    /* Check expiry */
    if (cap->expiry > 0) {
        /* TODO: Get current time and compare */
        /* For now, assume not expired */
    }

    return true;
}

#ifdef __cplusplus
}
#endif
