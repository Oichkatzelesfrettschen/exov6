/**
 * @file vfs_file.h
 * @brief VFS File Operations API
 *
 * High-level file operations API using VFS layer.
 * Provides standard POSIX-like interface.
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include "vfs.h"

#ifdef __cplusplus
extern "C" {
#endif

/*******************************************************************************
 * FILE DESCRIPTOR TABLE
 ******************************************************************************/

#define VFS_MAX_OPEN_FILES  1024       /**< Max open files per process */

/**
 * @brief File descriptor entry
 */
typedef struct {
    struct vfs_file *file;             /**< VFS file handle */
    uint32_t flags;                    /**< File descriptor flags */
    _Atomic uint32_t refcount;         /**< Reference count */
} vfs_fd_entry_t;

/**
 * @brief File descriptor table
 */
typedef struct {
    vfs_fd_entry_t entries[VFS_MAX_OPEN_FILES];
    _Atomic uint32_t next_fd;          /**< Next available FD */
} vfs_fd_table_t;

/*******************************************************************************
 * FILE OPERATIONS
 ******************************************************************************/

/**
 * @brief Open a file
 *
 * @param path   File path
 * @param flags  Open flags (VFS_O_*)
 * @param mode   File mode (for creation)
 * @return File descriptor or negative on error
 */
int vfs_open(const char *path, uint32_t flags, uint16_t mode);

/**
 * @brief Close a file
 *
 * @param fd  File descriptor
 * @return 0 on success, negative on error
 */
int vfs_close(int fd);

/**
 * @brief Read from a file
 *
 * @param fd     File descriptor
 * @param buf    Output buffer
 * @param count  Bytes to read
 * @return Bytes read or negative on error
 */
ssize_t vfs_read(int fd, void *buf, size_t count);

/**
 * @brief Write to a file
 *
 * @param fd     File descriptor
 * @param buf    Input buffer
 * @param count  Bytes to write
 * @return Bytes written or negative on error
 */
ssize_t vfs_write(int fd, const void *buf, size_t count);

/**
 * @brief Seek within a file
 *
 * @param fd      File descriptor
 * @param offset  Offset
 * @param whence  SEEK_SET, SEEK_CUR, or SEEK_END
 * @return New offset or negative on error
 */
int64_t vfs_lseek(int fd, int64_t offset, int whence);

/**
 * @brief Sync file to disk
 *
 * @param fd  File descriptor
 * @return 0 on success, negative on error
 */
int vfs_fsync(int fd);

/**
 * @brief Truncate a file
 *
 * @param path    File path
 * @param length  New length
 * @return 0 on success, negative on error
 */
int vfs_truncate(const char *path, uint64_t length);

/**
 * @brief Truncate an open file
 *
 * @param fd      File descriptor
 * @param length  New length
 * @return 0 on success, negative on error
 */
int vfs_ftruncate(int fd, uint64_t length);

/*******************************************************************************
 * DIRECTORY OPERATIONS
 ******************************************************************************/

/**
 * @brief Directory entry callback
 *
 * @param ctx   Context pointer
 * @param name  Entry name
 * @param inum  Inode number
 * @return 0 to continue, non-zero to stop
 */
typedef int (*vfs_readdir_callback_t)(void *ctx, const char *name, uint64_t inum);

/**
 * @brief Read directory entries
 *
 * @param fd        File descriptor (directory)
 * @param callback  Callback for each entry
 * @param ctx       Context for callback
 * @return 0 on success, negative on error
 */
int vfs_readdir(int fd, vfs_readdir_callback_t callback, void *ctx);

/**
 * @brief Create a directory
 *
 * @param path  Directory path
 * @param mode  Directory mode
 * @return 0 on success, negative on error
 */
int vfs_mkdir(const char *path, uint16_t mode);

/**
 * @brief Remove a directory
 *
 * @param path  Directory path
 * @return 0 on success, negative on error
 */
int vfs_rmdir(const char *path);

/*******************************************************************************
 * FILE/DIRECTORY MANAGEMENT
 ******************************************************************************/

/**
 * @brief Create a file
 *
 * @param path  File path
 * @param mode  File mode
 * @return 0 on success, negative on error
 */
int vfs_create(const char *path, uint16_t mode);

/**
 * @brief Remove a file
 *
 * @param path  File path
 * @return 0 on success, negative on error
 */
int vfs_unlink(const char *path);

/**
 * @brief Rename a file or directory
 *
 * @param oldpath  Old path
 * @param newpath  New path
 * @return 0 on success, negative on error
 */
int vfs_rename(const char *oldpath, const char *newpath);

/**
 * @brief Create a symbolic link
 *
 * @param target   Link target
 * @param linkpath Link path
 * @return 0 on success, negative on error
 */
int vfs_symlink(const char *target, const char *linkpath);

/**
 * @brief Read a symbolic link
 *
 * @param path    Link path
 * @param buf     Output buffer
 * @param bufsiz  Buffer size
 * @return Bytes written or negative on error
 */
ssize_t vfs_readlink(const char *path, char *buf, size_t bufsiz);

/*******************************************************************************
 * FILE ATTRIBUTES
 ******************************************************************************/

/**
 * @brief File statistics
 */
typedef struct {
    uint64_t inum;        /**< Inode number */
    uint16_t mode;        /**< File mode */
    uint16_t nlink;       /**< Number of links */
    uint32_t uid;         /**< Owner UID */
    uint32_t gid;         /**< Owner GID */
    uint64_t size;        /**< File size */
    uint64_t atime;       /**< Access time */
    uint64_t mtime;       /**< Modification time */
    uint64_t ctime;       /**< Change time */
} vfs_stat_t;

/**
 * @brief Get file statistics
 *
 * @param path  File path
 * @param st    Output statistics
 * @return 0 on success, negative on error
 */
int vfs_stat(const char *path, vfs_stat_t *st);

/**
 * @brief Get file statistics (don't follow symlinks)
 *
 * @param path  File path
 * @param st    Output statistics
 * @return 0 on success, negative on error
 */
int vfs_lstat(const char *path, vfs_stat_t *st);

/**
 * @brief Get file statistics by fd
 *
 * @param fd  File descriptor
 * @param st  Output statistics
 * @return 0 on success, negative on error
 */
int vfs_fstat(int fd, vfs_stat_t *st);

/**
 * @brief Change file ownership
 *
 * @param path  File path
 * @param uid   New owner UID
 * @param gid   New owner GID
 * @return 0 on success, negative on error
 */
int vfs_chown(const char *path, uint32_t uid, uint32_t gid);

/**
 * @brief Change file mode
 *
 * @param path  File path
 * @param mode  New mode
 * @return 0 on success, negative on error
 */
int vfs_chmod(const char *path, uint16_t mode);

/*******************************************************************************
 * FILE DESCRIPTOR TABLE MANAGEMENT
 ******************************************************************************/

/**
 * @brief Initialize file descriptor table
 *
 * @param table  FD table
 * @return 0 on success, negative on error
 */
int vfs_fd_table_init(vfs_fd_table_t *table);

/**
 * @brief Destroy file descriptor table
 *
 * Closes all open files.
 *
 * @param table  FD table
 */
void vfs_fd_table_destroy(vfs_fd_table_t *table);

/**
 * @brief Allocate a file descriptor
 *
 * @param table  FD table
 * @param file   VFS file handle
 * @param flags  FD flags
 * @return File descriptor or negative on error
 */
int vfs_fd_alloc(vfs_fd_table_t *table, struct vfs_file *file, uint32_t flags);

/**
 * @brief Free a file descriptor
 *
 * @param table  FD table
 * @param fd     File descriptor
 * @return 0 on success, negative on error
 */
int vfs_fd_free(vfs_fd_table_t *table, int fd);

/**
 * @brief Get file from descriptor
 *
 * @param table  FD table
 * @param fd     File descriptor
 * @return VFS file handle or NULL
 */
struct vfs_file* vfs_fd_get_file(vfs_fd_table_t *table, int fd);

/**
 * @brief Get per-process FD table
 *
 * @return Current process FD table
 */
vfs_fd_table_t* vfs_get_fd_table(void);

/*******************************************************************************
 * SEEK WHENCE
 ******************************************************************************/

#define SEEK_SET  0  /**< Seek from beginning */
#define SEEK_CUR  1  /**< Seek from current position */
#define SEEK_END  2  /**< Seek from end */

/*******************************************************************************
 * FILE MODE MACROS
 ******************************************************************************/

#define S_IFMT    0170000  /**< File type mask */
#define S_IFREG   0100000  /**< Regular file */
#define S_IFDIR   0040000  /**< Directory */
#define S_IFLNK   0120000  /**< Symbolic link */
#define S_IFCHR   0020000  /**< Character device */
#define S_IFBLK   0060000  /**< Block device */

#define S_ISREG(m)  (((m) & S_IFMT) == S_IFREG)  /**< Is regular file */
#define S_ISDIR(m)  (((m) & S_IFMT) == S_IFDIR)  /**< Is directory */
#define S_ISLNK(m)  (((m) & S_IFMT) == S_IFLNK)  /**< Is symlink */

#define S_IRWXU   0000700  /**< User RWX */
#define S_IRUSR   0000400  /**< User read */
#define S_IWUSR   0000200  /**< User write */
#define S_IXUSR   0000100  /**< User execute */

#define S_IRWXG   0000070  /**< Group RWX */
#define S_IRGRP   0000040  /**< Group read */
#define S_IWGRP   0000020  /**< Group write */
#define S_IXGRP   0000010  /**< Group execute */

#define S_IRWXO   0000007  /**< Other RWX */
#define S_IROTH   0000004  /**< Other read */
#define S_IWOTH   0000002  /**< Other write */
#define S_IXOTH   0000001  /**< Other execute */

#ifdef __cplusplus
}
#endif
