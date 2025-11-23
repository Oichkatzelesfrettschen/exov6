/**
 * @file linux_file.c
 * @brief Linux file I/O syscall implementations
 *
 * This file implements Linux file and I/O syscalls for the exokernel libOS.
 * Provides openat, read, write, close, ioctl, and related file operations.
 *
 * File Descriptor Model:
 * - Process-local file descriptor table
 * - Reference counting for shared file descriptions
 * - Support for regular files, directories, pipes, sockets
 */

#include "linux_syscall.h"
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

/* Forward declarations for exokernel primitives */
extern int exo_open(const char *path, int flags, int mode);
extern int exo_close(int fd);
extern ssize_t exo_read(int fd, void *buf, size_t count);
extern ssize_t exo_write(int fd, const void *buf, size_t count);
extern off_t exo_seek(int fd, off_t offset, int whence);
extern int exo_stat(const char *path, void *stat_buf);
extern int exo_fstat(int fd, void *stat_buf);
extern int exo_ioctl(int fd, unsigned long request, void *arg);

/*============================================================================
 * File Descriptor Table
 *============================================================================*/

/**
 * Open file description (shared between dup'd descriptors)
 */
struct linux_file {
    int exo_fd;              /* Underlying exokernel file descriptor */
    int flags;               /* Open flags */
    int mode;                /* File mode */
    off_t offset;            /* Current file position */
    int refcount;            /* Reference count */
    int type;                /* File type (regular, dir, pipe, socket, etc.) */
    void *private_data;      /* Type-specific data */
};

/* File types */
#define LINUX_FT_UNKNOWN    0
#define LINUX_FT_REGULAR    1
#define LINUX_FT_DIRECTORY  2
#define LINUX_FT_PIPE       3
#define LINUX_FT_SOCKET     4
#define LINUX_FT_CHARDEV    5
#define LINUX_FT_BLOCKDEV   6
#define LINUX_FT_FIFO       7
#define LINUX_FT_SYMLINK    8
#define LINUX_FT_EVENTFD    9
#define LINUX_FT_TIMERFD    10
#define LINUX_FT_SIGNALFD   11
#define LINUX_FT_EPOLL      12
#define LINUX_FT_INOTIFY    13

/**
 * Per-process file descriptor table
 */
struct linux_fdtable {
    struct linux_file *fds[LINUX_OPEN_MAX];  /* File descriptors */
    unsigned long close_on_exec;              /* Close-on-exec bitmap (first 64) */
    int max_fd;                               /* Highest open fd */
};

/* Per-process fd table (simplified - real impl uses process table) */
static struct linux_fdtable *current_fdt = NULL;

/* File allocation pool */
static struct linux_file file_pool[LINUX_OPEN_MAX];
static int file_pool_index = 0;

/*============================================================================
 * File Table Management
 *============================================================================*/

/**
 * Initialize file descriptor table
 */
static void init_fdtable(void)
{
    static struct linux_fdtable fdt_storage;

    if (current_fdt == NULL) {
        current_fdt = &fdt_storage;
        for (int i = 0; i < LINUX_OPEN_MAX; i++) {
            current_fdt->fds[i] = NULL;
        }
        current_fdt->close_on_exec = 0;
        current_fdt->max_fd = -1;

        /* Standard file descriptors (0, 1, 2 should be open) */
        /* TODO: Initialize stdin, stdout, stderr */
    }
}

/**
 * Allocate a file structure
 */
static struct linux_file *alloc_file(void)
{
    if (file_pool_index >= LINUX_OPEN_MAX) {
        return NULL;
    }

    struct linux_file *file = &file_pool[file_pool_index++];
    file->exo_fd = -1;
    file->flags = 0;
    file->mode = 0;
    file->offset = 0;
    file->refcount = 1;
    file->type = LINUX_FT_UNKNOWN;
    file->private_data = NULL;

    return file;
}

/**
 * Get file from fd
 */
static struct linux_file *get_file(int fd)
{
    if (!current_fdt) {
        init_fdtable();
    }

    if (fd < 0 || fd >= LINUX_OPEN_MAX) {
        return NULL;
    }

    return current_fdt->fds[fd];
}

/**
 * Allocate a new file descriptor
 */
static int alloc_fd(int min_fd)
{
    if (!current_fdt) {
        init_fdtable();
    }

    for (int fd = min_fd; fd < LINUX_OPEN_MAX; fd++) {
        if (current_fdt->fds[fd] == NULL) {
            return fd;
        }
    }

    return -LINUX_EMFILE;
}

/**
 * Install file at descriptor
 */
static int install_fd(int fd, struct linux_file *file)
{
    if (!current_fdt) {
        init_fdtable();
    }

    if (fd < 0 || fd >= LINUX_OPEN_MAX) {
        return -LINUX_EBADF;
    }

    /* Close existing fd if any */
    if (current_fdt->fds[fd] != NULL) {
        struct linux_file *old = current_fdt->fds[fd];
        old->refcount--;
        if (old->refcount == 0 && old->exo_fd >= 0) {
            exo_close(old->exo_fd);
        }
    }

    current_fdt->fds[fd] = file;
    if (fd > current_fdt->max_fd) {
        current_fdt->max_fd = fd;
    }

    return fd;
}

/**
 * Close a file descriptor
 */
static int close_fd(int fd)
{
    if (!current_fdt) {
        return -LINUX_EBADF;
    }

    if (fd < 0 || fd >= LINUX_OPEN_MAX) {
        return -LINUX_EBADF;
    }

    struct linux_file *file = current_fdt->fds[fd];
    if (!file) {
        return -LINUX_EBADF;
    }

    current_fdt->fds[fd] = NULL;
    current_fdt->close_on_exec &= ~(1UL << fd);

    file->refcount--;
    if (file->refcount == 0) {
        if (file->exo_fd >= 0) {
            exo_close(file->exo_fd);
        }
        /* File struct goes back to pool eventually */
    }

    /* Update max_fd */
    if (fd == current_fdt->max_fd) {
        while (current_fdt->max_fd >= 0 &&
               current_fdt->fds[current_fdt->max_fd] == NULL) {
            current_fdt->max_fd--;
        }
    }

    return 0;
}

/*============================================================================
 * Path Resolution
 *============================================================================*/

/**
 * Resolve path relative to directory fd
 */
static int resolve_path(int dirfd, const char *pathname, char *resolved,
                        size_t resolved_size, int flags)
{
    if (!pathname) {
        return -LINUX_EFAULT;
    }

    /* Empty pathname with AT_EMPTY_PATH */
    if (pathname[0] == '\0') {
        if (!(flags & LINUX_AT_EMPTY_PATH)) {
            return -LINUX_ENOENT;
        }
        /* Use dirfd itself */
        if (dirfd == LINUX_AT_FDCWD) {
            /* TODO: Get current working directory */
            resolved[0] = '/';
            resolved[1] = '\0';
        } else {
            /* TODO: Get path from fd */
            return -LINUX_ENOSYS;
        }
        return 0;
    }

    /* Absolute path */
    if (pathname[0] == '/') {
        size_t len = 0;
        while (pathname[len] && len < resolved_size - 1) {
            resolved[len] = pathname[len];
            len++;
        }
        resolved[len] = '\0';
        return 0;
    }

    /* Relative path */
    if (dirfd == LINUX_AT_FDCWD) {
        /* Relative to current directory */
        /* TODO: Prepend cwd */
        size_t len = 0;
        while (pathname[len] && len < resolved_size - 1) {
            resolved[len] = pathname[len];
            len++;
        }
        resolved[len] = '\0';
    } else {
        /* Relative to dirfd */
        /* TODO: Get dirfd path and concatenate */
        return -LINUX_ENOSYS;
    }

    return 0;
}

/*============================================================================
 * Flag Conversion
 *============================================================================*/

/**
 * Convert Linux open flags to exokernel flags
 */
static int linux_flags_to_exo(int linux_flags)
{
    int exo_flags = 0;

    /* Access mode */
    int accmode = linux_flags & LINUX_O_ACCMODE;
    if (accmode == LINUX_O_RDONLY) exo_flags |= 0x0000;
    if (accmode == LINUX_O_WRONLY) exo_flags |= 0x0001;
    if (accmode == LINUX_O_RDWR)   exo_flags |= 0x0002;

    /* Creation flags */
    if (linux_flags & LINUX_O_CREAT)     exo_flags |= 0x0040;
    if (linux_flags & LINUX_O_EXCL)      exo_flags |= 0x0080;
    if (linux_flags & LINUX_O_TRUNC)     exo_flags |= 0x0200;
    if (linux_flags & LINUX_O_APPEND)    exo_flags |= 0x0400;
    if (linux_flags & LINUX_O_NONBLOCK)  exo_flags |= 0x0800;
    if (linux_flags & LINUX_O_DIRECTORY) exo_flags |= 0x10000;
    if (linux_flags & LINUX_O_NOFOLLOW)  exo_flags |= 0x20000;

    return exo_flags;
}

/*============================================================================
 * open/openat Implementation
 *============================================================================*/

/**
 * Open a file relative to directory fd
 */
long linux_sys_openat(int dirfd, const char *pathname, int flags, int mode)
{
    init_fdtable();

    /* Resolve path */
    char resolved[1024];
    int ret = resolve_path(dirfd, pathname, resolved, sizeof(resolved), 0);
    if (ret < 0) {
        return ret;
    }

    /* Allocate file structure */
    struct linux_file *file = alloc_file();
    if (!file) {
        return -LINUX_ENFILE;
    }

    /* Open via exokernel */
    int exo_flags = linux_flags_to_exo(flags);
    int exo_fd = exo_open(resolved, exo_flags, mode);
    if (exo_fd < 0) {
        return -LINUX_ENOENT; /* Map error appropriately */
    }

    file->exo_fd = exo_fd;
    file->flags = flags;
    file->mode = mode;
    file->offset = 0;
    file->type = (flags & LINUX_O_DIRECTORY) ? LINUX_FT_DIRECTORY : LINUX_FT_REGULAR;

    /* Allocate fd */
    int fd = alloc_fd(0);
    if (fd < 0) {
        exo_close(exo_fd);
        return fd;
    }

    /* Handle O_CLOEXEC */
    if (flags & LINUX_O_CLOEXEC) {
        current_fdt->close_on_exec |= (1UL << fd);
    }

    install_fd(fd, file);
    return fd;
}

/**
 * Open file (legacy, uses current directory)
 */
long linux_sys_open(const char *pathname, int flags, int mode)
{
    return linux_sys_openat(LINUX_AT_FDCWD, pathname, flags, mode);
}

/**
 * Create file
 */
long linux_sys_creat(const char *pathname, int mode)
{
    return linux_sys_openat(LINUX_AT_FDCWD, pathname,
                           LINUX_O_CREAT | LINUX_O_WRONLY | LINUX_O_TRUNC, mode);
}

/*============================================================================
 * close Implementation
 *============================================================================*/

/**
 * Close a file descriptor
 */
long linux_sys_close(int fd)
{
    return close_fd(fd);
}

/**
 * Close a range of file descriptors
 */
long linux_sys_close_range(unsigned int first, unsigned int last,
                           unsigned int flags)
{
    if (first > last) {
        return -LINUX_EINVAL;
    }

    if (last >= LINUX_OPEN_MAX) {
        last = LINUX_OPEN_MAX - 1;
    }

    for (unsigned int fd = first; fd <= last; fd++) {
        close_fd(fd);
    }

    return 0;
}

/*============================================================================
 * read/write Implementation
 *============================================================================*/

/**
 * Read from file descriptor
 */
long linux_sys_read(int fd, void *buf, size_t count)
{
    struct linux_file *file = get_file(fd);
    if (!file) {
        return -LINUX_EBADF;
    }

    if (!buf) {
        return -LINUX_EFAULT;
    }

    ssize_t ret = exo_read(file->exo_fd, buf, count);
    if (ret > 0) {
        file->offset += ret;
    }

    return ret;
}

/**
 * Write to file descriptor
 */
long linux_sys_write(int fd, const void *buf, size_t count)
{
    struct linux_file *file = get_file(fd);
    if (!file) {
        return -LINUX_EBADF;
    }

    if (!buf) {
        return -LINUX_EFAULT;
    }

    /* Handle O_APPEND */
    if (file->flags & LINUX_O_APPEND) {
        /* Seek to end first */
        file->offset = exo_seek(file->exo_fd, 0, 2); /* SEEK_END */
    }

    ssize_t ret = exo_write(file->exo_fd, buf, count);
    if (ret > 0) {
        file->offset += ret;
    }

    return ret;
}

/**
 * Read from file at offset
 */
long linux_sys_pread64(int fd, void *buf, size_t count, off_t offset)
{
    struct linux_file *file = get_file(fd);
    if (!file) {
        return -LINUX_EBADF;
    }

    /* Save current position */
    off_t saved = file->offset;

    /* Seek and read */
    exo_seek(file->exo_fd, offset, 0); /* SEEK_SET */
    ssize_t ret = exo_read(file->exo_fd, buf, count);

    /* Restore position */
    exo_seek(file->exo_fd, saved, 0);

    return ret;
}

/**
 * Write to file at offset
 */
long linux_sys_pwrite64(int fd, const void *buf, size_t count, off_t offset)
{
    struct linux_file *file = get_file(fd);
    if (!file) {
        return -LINUX_EBADF;
    }

    off_t saved = file->offset;

    exo_seek(file->exo_fd, offset, 0);
    ssize_t ret = exo_write(file->exo_fd, buf, count);

    exo_seek(file->exo_fd, saved, 0);

    return ret;
}

/*============================================================================
 * Vectored I/O
 *============================================================================*/

/**
 * Read into multiple buffers
 */
long linux_sys_readv(int fd, const struct linux_iovec *iov, int iovcnt)
{
    if (iovcnt < 0 || iovcnt > LINUX_IOV_MAX) {
        return -LINUX_EINVAL;
    }

    ssize_t total = 0;
    for (int i = 0; i < iovcnt; i++) {
        ssize_t ret = linux_sys_read(fd, iov[i].iov_base, iov[i].iov_len);
        if (ret < 0) {
            return (total > 0) ? total : ret;
        }
        total += ret;
        if ((size_t)ret < iov[i].iov_len) {
            break; /* Short read */
        }
    }

    return total;
}

/**
 * Write from multiple buffers
 */
long linux_sys_writev(int fd, const struct linux_iovec *iov, int iovcnt)
{
    if (iovcnt < 0 || iovcnt > LINUX_IOV_MAX) {
        return -LINUX_EINVAL;
    }

    ssize_t total = 0;
    for (int i = 0; i < iovcnt; i++) {
        ssize_t ret = linux_sys_write(fd, iov[i].iov_base, iov[i].iov_len);
        if (ret < 0) {
            return (total > 0) ? total : ret;
        }
        total += ret;
        if ((size_t)ret < iov[i].iov_len) {
            break; /* Short write */
        }
    }

    return total;
}

/**
 * Positional vectored read
 */
long linux_sys_preadv(int fd, const struct linux_iovec *iov, int iovcnt,
                      off_t offset)
{
    struct linux_file *file = get_file(fd);
    if (!file) {
        return -LINUX_EBADF;
    }

    off_t saved = file->offset;
    exo_seek(file->exo_fd, offset, 0);

    ssize_t total = linux_sys_readv(fd, iov, iovcnt);

    exo_seek(file->exo_fd, saved, 0);
    file->offset = saved;

    return total;
}

/**
 * Positional vectored write
 */
long linux_sys_pwritev(int fd, const struct linux_iovec *iov, int iovcnt,
                       off_t offset)
{
    struct linux_file *file = get_file(fd);
    if (!file) {
        return -LINUX_EBADF;
    }

    off_t saved = file->offset;
    exo_seek(file->exo_fd, offset, 0);

    ssize_t total = linux_sys_writev(fd, iov, iovcnt);

    exo_seek(file->exo_fd, saved, 0);
    file->offset = saved;

    return total;
}

/*============================================================================
 * lseek Implementation
 *============================================================================*/

/**
 * Reposition file offset
 */
long linux_sys_lseek(int fd, off_t offset, int whence)
{
    struct linux_file *file = get_file(fd);
    if (!file) {
        return -LINUX_EBADF;
    }

    /* Validate whence */
    if (whence < 0 || whence > 2) {
        return -LINUX_EINVAL;
    }

    off_t new_offset = exo_seek(file->exo_fd, offset, whence);
    if (new_offset >= 0) {
        file->offset = new_offset;
    }

    return new_offset;
}

/*============================================================================
 * stat/fstat Implementation
 *============================================================================*/

/**
 * Get file status by fd
 */
long linux_sys_fstat(int fd, struct linux_stat *statbuf)
{
    struct linux_file *file = get_file(fd);
    if (!file) {
        return -LINUX_EBADF;
    }

    if (!statbuf) {
        return -LINUX_EFAULT;
    }

    return exo_fstat(file->exo_fd, statbuf);
}

/**
 * Get file status by path
 */
long linux_sys_stat(const char *pathname, struct linux_stat *statbuf)
{
    if (!pathname || !statbuf) {
        return -LINUX_EFAULT;
    }

    return exo_stat(pathname, statbuf);
}

/**
 * Get file status (don't follow symlinks)
 */
long linux_sys_lstat(const char *pathname, struct linux_stat *statbuf)
{
    /* TODO: Implement symlink-aware stat */
    return linux_sys_stat(pathname, statbuf);
}

/**
 * Get file status relative to directory fd
 */
long linux_sys_newfstatat(int dirfd, const char *pathname,
                          struct linux_stat *statbuf, int flags)
{
    char resolved[1024];
    int ret = resolve_path(dirfd, pathname, resolved, sizeof(resolved), flags);
    if (ret < 0) {
        return ret;
    }

    if (flags & LINUX_AT_SYMLINK_NOFOLLOW) {
        return linux_sys_lstat(resolved, statbuf);
    }

    return linux_sys_stat(resolved, statbuf);
}

/**
 * Get extended file status (statx)
 */
long linux_sys_statx(int dirfd, const char *pathname, int flags,
                     unsigned int mask, struct linux_statx *statxbuf)
{
    /* TODO: Implement full statx with extended attributes */
    /* For now, convert to regular stat */
    struct linux_stat st;
    long ret = linux_sys_newfstatat(dirfd, pathname, &st, flags);
    if (ret < 0) {
        return ret;
    }

    /* Fill statx from stat */
    statxbuf->stx_mask = mask & 0x7ff;
    statxbuf->stx_blksize = st.st_blksize;
    statxbuf->stx_attributes = 0;
    statxbuf->stx_nlink = st.st_nlink;
    statxbuf->stx_uid = st.st_uid;
    statxbuf->stx_gid = st.st_gid;
    statxbuf->stx_mode = st.st_mode;
    statxbuf->stx_ino = st.st_ino;
    statxbuf->stx_size = st.st_size;
    statxbuf->stx_blocks = st.st_blocks;

    return 0;
}

/*============================================================================
 * dup/dup2/dup3 Implementation
 *============================================================================*/

/**
 * Duplicate file descriptor
 */
long linux_sys_dup(int oldfd)
{
    struct linux_file *file = get_file(oldfd);
    if (!file) {
        return -LINUX_EBADF;
    }

    int newfd = alloc_fd(0);
    if (newfd < 0) {
        return newfd;
    }

    file->refcount++;
    install_fd(newfd, file);

    return newfd;
}

/**
 * Duplicate fd to specific number
 */
long linux_sys_dup2(int oldfd, int newfd)
{
    if (oldfd == newfd) {
        /* Check if oldfd is valid */
        if (!get_file(oldfd)) {
            return -LINUX_EBADF;
        }
        return newfd;
    }

    struct linux_file *file = get_file(oldfd);
    if (!file) {
        return -LINUX_EBADF;
    }

    if (newfd < 0 || newfd >= LINUX_OPEN_MAX) {
        return -LINUX_EBADF;
    }

    /* Close newfd if open */
    close_fd(newfd);

    file->refcount++;
    install_fd(newfd, file);

    return newfd;
}

/**
 * Duplicate fd with flags
 */
long linux_sys_dup3(int oldfd, int newfd, int flags)
{
    if (oldfd == newfd) {
        return -LINUX_EINVAL;
    }

    long ret = linux_sys_dup2(oldfd, newfd);
    if (ret < 0) {
        return ret;
    }

    if (flags & LINUX_O_CLOEXEC) {
        current_fdt->close_on_exec |= (1UL << newfd);
    }

    return ret;
}

/*============================================================================
 * fcntl Implementation
 *============================================================================*/

/**
 * File control operations
 */
long linux_sys_fcntl(int fd, int cmd, unsigned long arg)
{
    struct linux_file *file = get_file(fd);
    if (!file) {
        return -LINUX_EBADF;
    }

    switch (cmd) {
    case LINUX_F_DUPFD:
        /* Duplicate to fd >= arg */
        {
            int newfd = alloc_fd((int)arg);
            if (newfd < 0) return newfd;
            file->refcount++;
            install_fd(newfd, file);
            return newfd;
        }

    case LINUX_F_DUPFD_CLOEXEC:
        {
            int newfd = alloc_fd((int)arg);
            if (newfd < 0) return newfd;
            file->refcount++;
            install_fd(newfd, file);
            current_fdt->close_on_exec |= (1UL << newfd);
            return newfd;
        }

    case LINUX_F_GETFD:
        return (current_fdt->close_on_exec & (1UL << fd)) ? LINUX_FD_CLOEXEC : 0;

    case LINUX_F_SETFD:
        if (arg & LINUX_FD_CLOEXEC) {
            current_fdt->close_on_exec |= (1UL << fd);
        } else {
            current_fdt->close_on_exec &= ~(1UL << fd);
        }
        return 0;

    case LINUX_F_GETFL:
        return file->flags;

    case LINUX_F_SETFL:
        /* Only some flags can be changed */
        file->flags = (file->flags & ~LINUX_O_SETFL_MASK) |
                      (arg & LINUX_O_SETFL_MASK);
        return 0;

    case LINUX_F_GETLK:
    case LINUX_F_SETLK:
    case LINUX_F_SETLKW:
        /* TODO: Implement file locking */
        return -LINUX_ENOSYS;

    case LINUX_F_GETOWN:
    case LINUX_F_SETOWN:
        /* TODO: Implement async I/O owner */
        return 0;

    default:
        return -LINUX_EINVAL;
    }
}

/*============================================================================
 * ioctl Implementation
 *============================================================================*/

/**
 * Device control
 */
long linux_sys_ioctl(int fd, unsigned long request, unsigned long arg)
{
    struct linux_file *file = get_file(fd);
    if (!file) {
        return -LINUX_EBADF;
    }

    /* Handle generic ioctls */
    switch (request) {
    case LINUX_FIONREAD:
        /* Get number of bytes available */
        /* TODO: Implement properly */
        *((int *)arg) = 0;
        return 0;

    case LINUX_FIONBIO:
        /* Set/clear non-blocking */
        if (*((int *)arg)) {
            file->flags |= LINUX_O_NONBLOCK;
        } else {
            file->flags &= ~LINUX_O_NONBLOCK;
        }
        return 0;

    case LINUX_FIOCLEX:
        current_fdt->close_on_exec |= (1UL << fd);
        return 0;

    case LINUX_FIONCLEX:
        current_fdt->close_on_exec &= ~(1UL << fd);
        return 0;

    default:
        /* Pass to underlying driver */
        return exo_ioctl(file->exo_fd, request, (void *)arg);
    }
}

/*============================================================================
 * pipe Implementation
 *============================================================================*/

/**
 * Create pipe
 */
long linux_sys_pipe(int pipefd[2])
{
    return linux_sys_pipe2(pipefd, 0);
}

/**
 * Create pipe with flags
 */
long linux_sys_pipe2(int pipefd[2], int flags)
{
    init_fdtable();

    /* Allocate two file structures */
    struct linux_file *read_file = alloc_file();
    struct linux_file *write_file = alloc_file();

    if (!read_file || !write_file) {
        return -LINUX_ENFILE;
    }

    /* Allocate fds */
    int read_fd = alloc_fd(0);
    if (read_fd < 0) {
        return read_fd;
    }

    int write_fd = alloc_fd(read_fd + 1);
    if (write_fd < 0) {
        return write_fd;
    }

    /* TODO: Create actual pipe in exokernel */
    /* For now, create placeholder entries */
    read_file->type = LINUX_FT_PIPE;
    read_file->flags = LINUX_O_RDONLY | (flags & LINUX_O_NONBLOCK);
    write_file->type = LINUX_FT_PIPE;
    write_file->flags = LINUX_O_WRONLY | (flags & LINUX_O_NONBLOCK);

    install_fd(read_fd, read_file);
    install_fd(write_fd, write_file);

    if (flags & LINUX_O_CLOEXEC) {
        current_fdt->close_on_exec |= (1UL << read_fd);
        current_fdt->close_on_exec |= (1UL << write_fd);
    }

    pipefd[0] = read_fd;
    pipefd[1] = write_fd;

    return 0;
}

/*============================================================================
 * Directory Operations
 *============================================================================*/

/**
 * Get directory entries
 */
long linux_sys_getdents64(int fd, void *dirp, size_t count)
{
    struct linux_file *file = get_file(fd);
    if (!file) {
        return -LINUX_EBADF;
    }

    if (file->type != LINUX_FT_DIRECTORY) {
        return -LINUX_ENOTDIR;
    }

    /* TODO: Implement directory reading */
    return -LINUX_ENOSYS;
}

/**
 * Create directory
 */
long linux_sys_mkdir(const char *pathname, int mode)
{
    return linux_sys_mkdirat(LINUX_AT_FDCWD, pathname, mode);
}

/**
 * Create directory relative to fd
 */
long linux_sys_mkdirat(int dirfd, const char *pathname, int mode)
{
    char resolved[1024];
    int ret = resolve_path(dirfd, pathname, resolved, sizeof(resolved), 0);
    if (ret < 0) {
        return ret;
    }

    /* TODO: Call exokernel mkdir */
    return -LINUX_ENOSYS;
}

/**
 * Remove directory
 */
long linux_sys_rmdir(const char *pathname)
{
    /* TODO: Implement */
    return -LINUX_ENOSYS;
}

/*============================================================================
 * Link Operations
 *============================================================================*/

/**
 * Unlink (delete) file
 */
long linux_sys_unlink(const char *pathname)
{
    return linux_sys_unlinkat(LINUX_AT_FDCWD, pathname, 0);
}

/**
 * Unlink relative to fd
 */
long linux_sys_unlinkat(int dirfd, const char *pathname, int flags)
{
    char resolved[1024];
    int ret = resolve_path(dirfd, pathname, resolved, sizeof(resolved), 0);
    if (ret < 0) {
        return ret;
    }

    /* TODO: Call exokernel unlink */
    return -LINUX_ENOSYS;
}

/**
 * Create hard link
 */
long linux_sys_link(const char *oldpath, const char *newpath)
{
    return linux_sys_linkat(LINUX_AT_FDCWD, oldpath,
                           LINUX_AT_FDCWD, newpath, 0);
}

/**
 * Create hard link relative to fds
 */
long linux_sys_linkat(int olddirfd, const char *oldpath,
                      int newdirfd, const char *newpath, int flags)
{
    /* TODO: Implement */
    return -LINUX_ENOSYS;
}

/**
 * Create symbolic link
 */
long linux_sys_symlink(const char *target, const char *linkpath)
{
    return linux_sys_symlinkat(target, LINUX_AT_FDCWD, linkpath);
}

/**
 * Create symbolic link relative to fd
 */
long linux_sys_symlinkat(const char *target, int newdirfd, const char *linkpath)
{
    /* TODO: Implement */
    return -LINUX_ENOSYS;
}

/**
 * Read symbolic link
 */
long linux_sys_readlink(const char *pathname, char *buf, size_t bufsiz)
{
    return linux_sys_readlinkat(LINUX_AT_FDCWD, pathname, buf, bufsiz);
}

/**
 * Read symbolic link relative to fd
 */
long linux_sys_readlinkat(int dirfd, const char *pathname,
                          char *buf, size_t bufsiz)
{
    /* TODO: Implement */
    return -LINUX_ENOSYS;
}

/*============================================================================
 * Rename Operations
 *============================================================================*/

/**
 * Rename file
 */
long linux_sys_rename(const char *oldpath, const char *newpath)
{
    return linux_sys_renameat(LINUX_AT_FDCWD, oldpath,
                             LINUX_AT_FDCWD, newpath);
}

/**
 * Rename file relative to fds
 */
long linux_sys_renameat(int olddirfd, const char *oldpath,
                        int newdirfd, const char *newpath)
{
    return linux_sys_renameat2(olddirfd, oldpath, newdirfd, newpath, 0);
}

/**
 * Rename with flags
 */
long linux_sys_renameat2(int olddirfd, const char *oldpath,
                         int newdirfd, const char *newpath,
                         unsigned int flags)
{
    /* TODO: Implement */
    return -LINUX_ENOSYS;
}

/*============================================================================
 * Permission Operations
 *============================================================================*/

/**
 * Check access permissions
 */
long linux_sys_access(const char *pathname, int mode)
{
    return linux_sys_faccessat(LINUX_AT_FDCWD, pathname, mode, 0);
}

/**
 * Check access relative to fd
 */
long linux_sys_faccessat(int dirfd, const char *pathname, int mode, int flags)
{
    char resolved[1024];
    int ret = resolve_path(dirfd, pathname, resolved, sizeof(resolved), flags);
    if (ret < 0) {
        return ret;
    }

    /* TODO: Implement actual permission check */
    return 0;
}

/**
 * Change file mode
 */
long linux_sys_chmod(const char *pathname, int mode)
{
    return linux_sys_fchmodat(LINUX_AT_FDCWD, pathname, mode, 0);
}

/**
 * Change file mode by fd
 */
long linux_sys_fchmod(int fd, int mode)
{
    struct linux_file *file = get_file(fd);
    if (!file) {
        return -LINUX_EBADF;
    }

    /* TODO: Implement */
    return -LINUX_ENOSYS;
}

/**
 * Change file mode relative to fd
 */
long linux_sys_fchmodat(int dirfd, const char *pathname, int mode, int flags)
{
    /* TODO: Implement */
    return -LINUX_ENOSYS;
}

/**
 * Change file owner
 */
long linux_sys_chown(const char *pathname, int owner, int group)
{
    return linux_sys_fchownat(LINUX_AT_FDCWD, pathname, owner, group, 0);
}

/**
 * Change file owner by fd
 */
long linux_sys_fchown(int fd, int owner, int group)
{
    struct linux_file *file = get_file(fd);
    if (!file) {
        return -LINUX_EBADF;
    }

    /* TODO: Implement */
    return -LINUX_ENOSYS;
}

/**
 * Change file owner (don't follow symlinks)
 */
long linux_sys_lchown(const char *pathname, int owner, int group)
{
    return linux_sys_fchownat(LINUX_AT_FDCWD, pathname, owner, group,
                             LINUX_AT_SYMLINK_NOFOLLOW);
}

/**
 * Change file owner relative to fd
 */
long linux_sys_fchownat(int dirfd, const char *pathname,
                        int owner, int group, int flags)
{
    /* TODO: Implement */
    return -LINUX_ENOSYS;
}

/*============================================================================
 * Truncate Operations
 *============================================================================*/

/**
 * Truncate file by path
 */
long linux_sys_truncate(const char *path, off_t length)
{
    /* TODO: Implement */
    return -LINUX_ENOSYS;
}

/**
 * Truncate file by fd
 */
long linux_sys_ftruncate(int fd, off_t length)
{
    struct linux_file *file = get_file(fd);
    if (!file) {
        return -LINUX_EBADF;
    }

    /* TODO: Implement */
    return -LINUX_ENOSYS;
}

/*============================================================================
 * Sync Operations
 *============================================================================*/

/**
 * Sync file to disk
 */
long linux_sys_fsync(int fd)
{
    struct linux_file *file = get_file(fd);
    if (!file) {
        return -LINUX_EBADF;
    }

    /* TODO: Call exokernel sync */
    return 0;
}

/**
 * Sync file data (not metadata)
 */
long linux_sys_fdatasync(int fd)
{
    return linux_sys_fsync(fd);
}

/**
 * Sync file range
 */
long linux_sys_sync_file_range(int fd, off_t offset, off_t nbytes,
                               unsigned int flags)
{
    return linux_sys_fsync(fd);
}

/**
 * Sync entire filesystem
 */
long linux_sys_sync(void)
{
    /* TODO: Implement global sync */
    return 0;
}

/**
 * Sync filesystem containing fd
 */
long linux_sys_syncfs(int fd)
{
    return linux_sys_fsync(fd);
}

/*============================================================================
 * Working Directory
 *============================================================================*/

/* Current working directory (simplified) */
static char current_cwd[1024] = "/";

/**
 * Get current working directory
 */
long linux_sys_getcwd(char *buf, size_t size)
{
    if (!buf) {
        return -LINUX_EFAULT;
    }

    size_t len = 0;
    while (current_cwd[len] && len < size - 1) {
        buf[len] = current_cwd[len];
        len++;
    }
    buf[len] = '\0';

    return len + 1;
}

/**
 * Change working directory
 */
long linux_sys_chdir(const char *path)
{
    if (!path) {
        return -LINUX_EFAULT;
    }

    /* TODO: Verify path exists */
    size_t len = 0;
    while (path[len] && len < sizeof(current_cwd) - 1) {
        current_cwd[len] = path[len];
        len++;
    }
    current_cwd[len] = '\0';

    return 0;
}

/**
 * Change working directory by fd
 */
long linux_sys_fchdir(int fd)
{
    struct linux_file *file = get_file(fd);
    if (!file) {
        return -LINUX_EBADF;
    }

    if (file->type != LINUX_FT_DIRECTORY) {
        return -LINUX_ENOTDIR;
    }

    /* TODO: Get path from fd and set cwd */
    return -LINUX_ENOSYS;
}

/*============================================================================
 * File Mask
 *============================================================================*/

static int current_umask = 022;

/**
 * Set file mode creation mask
 */
long linux_sys_umask(int mask)
{
    int old = current_umask;
    current_umask = mask & 0777;
    return old;
}

/*============================================================================
 * Copy File Range
 *============================================================================*/

/**
 * Copy data between file descriptors
 */
long linux_sys_copy_file_range(int fd_in, off_t *off_in,
                               int fd_out, off_t *off_out,
                               size_t len, unsigned int flags)
{
    /* TODO: Implement efficient copy */
    /* For now, do it the slow way */
    char buf[4096];
    ssize_t total = 0;

    while (len > 0) {
        size_t chunk = (len > sizeof(buf)) ? sizeof(buf) : len;
        ssize_t nr;

        if (off_in) {
            nr = linux_sys_pread64(fd_in, buf, chunk, *off_in);
            if (nr > 0) *off_in += nr;
        } else {
            nr = linux_sys_read(fd_in, buf, chunk);
        }

        if (nr <= 0) break;

        ssize_t nw;
        if (off_out) {
            nw = linux_sys_pwrite64(fd_out, buf, nr, *off_out);
            if (nw > 0) *off_out += nw;
        } else {
            nw = linux_sys_write(fd_out, buf, nr);
        }

        if (nw <= 0) break;

        total += nw;
        len -= nw;
    }

    return total;
}

/*============================================================================
 * sendfile
 *============================================================================*/

/**
 * Transfer data between file descriptors (zero-copy)
 */
long linux_sys_sendfile(int out_fd, int in_fd, off_t *offset, size_t count)
{
    return linux_sys_copy_file_range(in_fd, offset, out_fd, NULL, count, 0);
}

/*============================================================================
 * splice/tee/vmsplice
 *============================================================================*/

/**
 * Splice data between pipe and fd
 */
long linux_sys_splice(int fd_in, off_t *off_in,
                      int fd_out, off_t *off_out,
                      size_t len, unsigned int flags)
{
    return linux_sys_copy_file_range(fd_in, off_in, fd_out, off_out, len, 0);
}

/**
 * Duplicate pipe content
 */
long linux_sys_tee(int fd_in, int fd_out, size_t len, unsigned int flags)
{
    /* TODO: Implement non-consuming copy */
    return -LINUX_ENOSYS;
}

/**
 * Splice user pages into pipe
 */
long linux_sys_vmsplice(int fd, const struct linux_iovec *iov,
                        unsigned long nr_segs, unsigned int flags)
{
    return linux_sys_writev(fd, iov, nr_segs);
}

/*============================================================================
 * fallocate
 *============================================================================*/

/**
 * Allocate file space
 */
long linux_sys_fallocate(int fd, int mode, off_t offset, off_t len)
{
    struct linux_file *file = get_file(fd);
    if (!file) {
        return -LINUX_EBADF;
    }

    /* TODO: Implement space allocation */
    return 0;
}

/*============================================================================
 * readahead
 *============================================================================*/

/**
 * Initiate file readahead
 */
long linux_sys_readahead(int fd, off_t offset, size_t count)
{
    struct linux_file *file = get_file(fd);
    if (!file) {
        return -LINUX_EBADF;
    }

    /* Advisory - no actual implementation needed */
    return 0;
}

/*============================================================================
 * fadvise
 *============================================================================*/

/**
 * Give advice about file access patterns
 */
long linux_sys_fadvise64(int fd, off_t offset, off_t len, int advice)
{
    struct linux_file *file = get_file(fd);
    if (!file) {
        return -LINUX_EBADF;
    }

    /* Advisory only */
    return 0;
}

/*============================================================================
 * name_to_handle_at / open_by_handle_at
 *============================================================================*/

/**
 * Obtain handle for pathname
 */
long linux_sys_name_to_handle_at(int dirfd, const char *pathname,
                                 void *handle, int *mount_id, int flags)
{
    return -LINUX_ENOSYS;
}

/**
 * Open file via handle
 */
long linux_sys_open_by_handle_at(int mount_fd, void *handle, int flags)
{
    return -LINUX_ENOSYS;
}
