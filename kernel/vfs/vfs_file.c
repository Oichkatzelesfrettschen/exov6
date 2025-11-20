/**
 * @file vfs_file.c
 * @brief VFS File Operations Implementation
 */

#include "vfs_file.h"
#include "vfs_icache.h"
#include "vfs_dcache.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

/*******************************************************************************
 * GLOBAL STATE
 ******************************************************************************/

static vfs_fd_table_t g_fd_table;
static bool g_fd_table_initialized = false;

/*******************************************************************************
 * FD TABLE MANAGEMENT
 ******************************************************************************/

int vfs_fd_table_init(vfs_fd_table_t *table)
{
    if (!table) return -1;

    memset(table, 0, sizeof(*table));
    atomic_store(&table->next_fd, 0);

    return 0;
}

void vfs_fd_table_destroy(vfs_fd_table_t *table)
{
    if (!table) return;

    /* Close all open files */
    for (int i = 0; i < VFS_MAX_OPEN_FILES; i++) {
        if (table->entries[i].file) {
            /* Release file */
            atomic_fetch_sub(&table->entries[i].file->refcount, 1);
            free(table->entries[i].file);
            table->entries[i].file = NULL;
        }
    }
}

int vfs_fd_alloc(vfs_fd_table_t *table, struct vfs_file *file, uint32_t flags)
{
    if (!table || !file) return -1;

    /* Find free slot */
    for (int i = 0; i < VFS_MAX_OPEN_FILES; i++) {
        if (!table->entries[i].file) {
            /* Found free slot */
            table->entries[i].file = file;
            table->entries[i].flags = flags;
            atomic_store(&table->entries[i].refcount, 1);
            atomic_fetch_add(&file->refcount, 1);
            return i;
        }
    }

    return -1;  /* No free slots */
}

int vfs_fd_free(vfs_fd_table_t *table, int fd)
{
    if (!table || fd < 0 || fd >= VFS_MAX_OPEN_FILES) {
        return -1;
    }

    if (!table->entries[fd].file) {
        return -1;  /* Not open */
    }

    /* Release file reference */
    struct vfs_file *file = table->entries[fd].file;
    uint32_t old = atomic_fetch_sub(&file->refcount, 1);

    if (old == 1) {
        /* Last reference - close file */
        if (file->inode && file->inode->sb && file->inode->sb->f_op &&
            file->inode->sb->f_op->release) {
            file->inode->sb->f_op->release(file);
        }

        /* Release inode */
        vfs_inode_put(file->inode);

        /* Free file structure */
        free(file);
    }

    table->entries[fd].file = NULL;
    return 0;
}

struct vfs_file* vfs_fd_get_file(vfs_fd_table_t *table, int fd)
{
    if (!table || fd < 0 || fd >= VFS_MAX_OPEN_FILES) {
        return NULL;
    }

    return table->entries[fd].file;
}

vfs_fd_table_t* vfs_get_fd_table(void)
{
    if (!g_fd_table_initialized) {
        vfs_fd_table_init(&g_fd_table);
        g_fd_table_initialized = true;
    }
    return &g_fd_table;
}

/*******************************************************************************
 * FILE OPERATIONS
 ******************************************************************************/

int vfs_open(const char *path, uint32_t flags, uint16_t mode)
{
    if (!path) return -1;

    vfs_fd_table_t *table = vfs_get_fd_table();

    /* Look up inode */
    struct vfs_inode *inode = vfs_path_lookup(path);

    /* Handle O_CREAT */
    if (!inode && (flags & VFS_O_CREAT)) {
        /* TODO: Create file */
        return -1;  /* Not implemented yet */
    }

    if (!inode) {
        return -1;  /* File not found */
    }

    /* Check if O_DIRECTORY and not a directory */
    if ((flags & VFS_O_DIRECTORY) && !S_ISDIR(inode->mode)) {
        vfs_inode_put(inode);
        return -1;
    }

    /* Allocate file structure */
    struct vfs_file *file = malloc(sizeof(struct vfs_file));
    if (!file) {
        vfs_inode_put(inode);
        return -1;
    }

    memset(file, 0, sizeof(*file));

    file->inode = inode;
    file->flags = flags;
    file->mode = mode;
    file->offset = 0;
    atomic_store(&file->refcount, 0);  /* Will be incremented by vfs_fd_alloc */

    /* Call filesystem open */
    if (inode->sb && inode->sb->f_op && inode->sb->f_op->open) {
        if (inode->sb->f_op->open(inode, file) < 0) {
            free(file);
            vfs_inode_put(inode);
            return -1;
        }
    }

    /* Handle O_TRUNC */
    if (flags & VFS_O_TRUNC) {
        /* TODO: Truncate file */
    }

    /* Allocate file descriptor */
    int fd = vfs_fd_alloc(table, file, 0);
    if (fd < 0) {
        free(file);
        vfs_inode_put(inode);
        return -1;
    }

    return fd;
}

int vfs_close(int fd)
{
    vfs_fd_table_t *table = vfs_get_fd_table();
    return vfs_fd_free(table, fd);
}

ssize_t vfs_read(int fd, void *buf, size_t count)
{
    if (!buf || count == 0) return -1;

    vfs_fd_table_t *table = vfs_get_fd_table();
    struct vfs_file *file = vfs_fd_get_file(table, fd);

    if (!file) return -1;

    /* Check read permission */
    if ((file->flags & VFS_O_WRONLY) == VFS_O_WRONLY) {
        return -1;  /* Write-only */
    }

    /* Call filesystem read */
    if (!file->inode->sb || !file->inode->sb->f_op ||
        !file->inode->sb->f_op->read) {
        return -1;
    }

    ssize_t result = file->inode->sb->f_op->read(file, buf, count, file->offset);

    if (result > 0) {
        file->offset += result;
    }

    return result;
}

ssize_t vfs_write(int fd, const void *buf, size_t count)
{
    if (!buf || count == 0) return -1;

    vfs_fd_table_t *table = vfs_get_fd_table();
    struct vfs_file *file = vfs_fd_get_file(table, fd);

    if (!file) return -1;

    /* Check write permission */
    if ((file->flags & VFS_O_RDONLY) == VFS_O_RDONLY &&
        (file->flags & VFS_O_WRONLY) == 0 &&
        (file->flags & VFS_O_RDWR) == 0) {
        return -1;  /* Read-only */
    }

    /* Handle append mode */
    if (file->flags & VFS_O_APPEND) {
        file->offset = file->inode->size;
    }

    /* Call filesystem write */
    if (!file->inode->sb || !file->inode->sb->f_op ||
        !file->inode->sb->f_op->write) {
        return -1;
    }

    ssize_t result = file->inode->sb->f_op->write(file, buf, count, file->offset);

    if (result > 0) {
        file->offset += result;
    }

    return result;
}

int64_t vfs_lseek(int fd, int64_t offset, int whence)
{
    vfs_fd_table_t *table = vfs_get_fd_table();
    struct vfs_file *file = vfs_fd_get_file(table, fd);

    if (!file) return -1;

    int64_t new_offset;

    switch (whence) {
        case SEEK_SET:
            new_offset = offset;
            break;

        case SEEK_CUR:
            new_offset = file->offset + offset;
            break;

        case SEEK_END:
            new_offset = file->inode->size + offset;
            break;

        default:
            return -1;
    }

    if (new_offset < 0) {
        return -1;
    }

    file->offset = new_offset;
    return new_offset;
}

int vfs_fsync(int fd)
{
    vfs_fd_table_t *table = vfs_get_fd_table();
    struct vfs_file *file = vfs_fd_get_file(table, fd);

    if (!file) return -1;

    /* Call filesystem fsync */
    if (file->inode->sb && file->inode->sb->f_op &&
        file->inode->sb->f_op->fsync) {
        return file->inode->sb->f_op->fsync(file);
    }

    return 0;  /* No-op if not supported */
}

/*******************************************************************************
 * DIRECTORY OPERATIONS
 ******************************************************************************/

int vfs_readdir(int fd, vfs_readdir_callback_t callback, void *ctx)
{
    if (!callback) return -1;

    vfs_fd_table_t *table = vfs_get_fd_table();
    struct vfs_file *file = vfs_fd_get_file(table, fd);

    if (!file) return -1;

    /* Check if directory */
    if (!S_ISDIR(file->inode->mode)) {
        return -1;
    }

    /* Call filesystem readdir */
    if (!file->inode->sb || !file->inode->sb->f_op ||
        !file->inode->sb->f_op->readdir) {
        return -1;
    }

    return file->inode->sb->f_op->readdir(file, callback, ctx);
}

int vfs_mkdir(const char *path, uint16_t mode)
{
    if (!path) return -1;

    /* TODO: Parse path to get parent directory and name */
    /* TODO: Look up parent directory */
    /* TODO: Call filesystem mkdir */

    return -1;  /* Not implemented yet */
}

int vfs_rmdir(const char *path)
{
    if (!path) return -1;

    /* TODO: Parse path */
    /* TODO: Call filesystem rmdir */

    return -1;  /* Not implemented yet */
}

/*******************************************************************************
 * FILE/DIRECTORY MANAGEMENT
 ******************************************************************************/

int vfs_create(const char *path, uint16_t mode)
{
    if (!path) return -1;

    /* TODO: Parse path */
    /* TODO: Call filesystem create */

    return -1;  /* Not implemented yet */
}

int vfs_unlink(const char *path)
{
    if (!path) return -1;

    /* TODO: Parse path */
    /* TODO: Call filesystem unlink */

    return -1;  /* Not implemented yet */
}

int vfs_rename(const char *oldpath, const char *newpath)
{
    if (!oldpath || !newpath) return -1;

    /* TODO: Parse paths */
    /* TODO: Call filesystem rename */

    return -1;  /* Not implemented yet */
}

int vfs_symlink(const char *target, const char *linkpath)
{
    if (!target || !linkpath) return -1;

    /* TODO: Parse linkpath */
    /* TODO: Call filesystem symlink */

    return -1;  /* Not implemented yet */
}

ssize_t vfs_readlink(const char *path, char *buf, size_t bufsiz)
{
    if (!path || !buf || bufsiz == 0) return -1;

    /* TODO: Implement readlink */

    return -1;  /* Not implemented yet */
}

/*******************************************************************************
 * FILE ATTRIBUTES
 ******************************************************************************/

int vfs_stat(const char *path, vfs_stat_t *st)
{
    if (!path || !st) return -1;

    struct vfs_inode *inode = vfs_path_lookup(path);
    if (!inode) return -1;

    memset(st, 0, sizeof(*st));
    st->inum = inode->inum;
    st->mode = inode->mode;
    st->nlink = inode->nlink;
    st->uid = inode->uid;
    st->gid = inode->gid;
    st->size = inode->size;
    st->atime = inode->atime;
    st->mtime = inode->mtime;
    st->ctime = inode->ctime;

    vfs_inode_put(inode);
    return 0;
}

int vfs_lstat(const char *path, vfs_stat_t *st)
{
    /* TODO: Don't follow symlinks */
    return vfs_stat(path, st);
}

int vfs_fstat(int fd, vfs_stat_t *st)
{
    if (!st) return -1;

    vfs_fd_table_t *table = vfs_get_fd_table();
    struct vfs_file *file = vfs_fd_get_file(table, fd);

    if (!file) return -1;

    memset(st, 0, sizeof(*st));
    st->inum = file->inode->inum;
    st->mode = file->inode->mode;
    st->nlink = file->inode->nlink;
    st->uid = file->inode->uid;
    st->gid = file->inode->gid;
    st->size = file->inode->size;
    st->atime = file->inode->atime;
    st->mtime = file->inode->mtime;
    st->ctime = file->inode->ctime;

    return 0;
}

int vfs_chown(const char *path, uint32_t uid, uint32_t gid)
{
    if (!path) return -1;

    struct vfs_inode *inode = vfs_path_lookup(path);
    if (!inode) return -1;

    inode->uid = uid;
    inode->gid = gid;

    /* Mark dirty */
    atomic_fetch_or(&inode->state, VFS_INODE_DIRTY);

    vfs_inode_put(inode);
    return 0;
}

int vfs_chmod(const char *path, uint16_t mode)
{
    if (!path) return -1;

    struct vfs_inode *inode = vfs_path_lookup(path);
    if (!inode) return -1;

    /* Preserve file type, change permissions */
    inode->mode = (inode->mode & S_IFMT) | (mode & 07777);

    /* Mark dirty */
    atomic_fetch_or(&inode->state, VFS_INODE_DIRTY);

    vfs_inode_put(inode);
    return 0;
}

int vfs_truncate(const char *path, uint64_t length)
{
    if (!path) return -1;

    /* TODO: Implement truncate */

    return -1;  /* Not implemented yet */
}

int vfs_ftruncate(int fd, uint64_t length)
{
    vfs_fd_table_t *table = vfs_get_fd_table();
    struct vfs_file *file = vfs_fd_get_file(table, fd);

    if (!file) return -1;

    /* TODO: Implement ftruncate */

    return -1;  /* Not implemented yet */
}
