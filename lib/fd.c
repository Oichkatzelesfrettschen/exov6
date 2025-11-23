/**
 * @file fd.c
 * @brief File Descriptor Layer - LibOS File Abstraction (Phase 11.2)
 *
 * ╔═══════════════════════════════════════════════════════════════════════════╗
 * ║  LIONS' COMMENTARY FOR THE POST-MONOLITHIC AGE                            ║
 * ║                                                                           ║
 * ║  LESSON: File Descriptors are a LibOS invention, not a kernel concept.    ║
 * ║                                                                           ║
 * ║  In UNIX V6, the kernel maintains the file descriptor table (per-process) ║
 * ║  and the open file table (system-wide). open() returns a kernel fd.       ║
 * ║                                                                           ║
 * ║  In ExoV6:                                                                ║
 * ║    - Kernel knows NOTHING about files                                     ║
 * ║    - fs_srv tracks its own "server handles"                               ║
 * ║    - THIS FILE maintains the per-process fd -> handle mapping             ║
 * ║    - fd 0/1/2 are console (no fs_srv involvement)                         ║
 * ║                                                                           ║
 * ║  The fd layer sits BETWEEN the application and fs_client:                 ║
 * ║                                                                           ║
 * ║    App code: fd_write(1, "hello")                                         ║
 * ║         ↓                                                                 ║
 * ║    fd.c: fd=1 is console → call sys_cputs()                               ║
 * ║                                                                           ║
 * ║    App code: fd_write(3, data)                                            ║
 * ║         ↓                                                                 ║
 * ║    fd.c: fd=3 maps to handle=7 → call write(7, data) [fs_client.c]        ║
 * ║                                                                           ║
 * ║  MECHANISM (Kernel): IPC, pages, console chars                            ║
 * ║  POLICY (LibOS): What "file descriptor" means                             ║
 * ╚═══════════════════════════════════════════════════════════════════════════╝
 */

#include <stdint.h>
#include <types.h>

/* ═══════════════════════════════════════════════════════════════════════════
 * Configuration
 * ═══════════════════════════════════════════════════════════════════════════ */

#define MAX_FD          32      /* Max open files per process */
#define FD_STDIN        0       /* Standard input */
#define FD_STDOUT       1       /* Standard output */
#define FD_STDERR       2       /* Standard error */

/* File descriptor types */
#define FD_TYPE_FREE    0       /* Slot is available */
#define FD_TYPE_CONSOLE 1       /* stdin/stdout/stderr - console I/O */
#define FD_TYPE_FILE    2       /* Regular file via fs_srv */
#define FD_TYPE_PIPE    3       /* Pipe (future) */

/* ═══════════════════════════════════════════════════════════════════════════
 * External Dependencies
 * ═══════════════════════════════════════════════════════════════════════════ */

/* Console I/O (kernel direct) */
extern void sys_cputs(const char *s, int len);
extern int sys_cgetc(void);

/* File operations (via fs_client.c which talks to fs_srv) */
extern int open(const char *path, int flags);
extern int read(int handle, void *buf, int n);
extern int write(int handle, const void *buf, int n);
extern int close(int handle);
extern int lseek(int handle, int offset, int whence);

/* Debug */
extern void print(const char *s);

/* Pipe operations (via lib/pipe.c) */
extern int pipe_create(void);
extern int pipe_read(int pipe_id, void *buf, int n);
extern int pipe_write(int pipe_id, const void *buf, int n);
extern void pipe_close_read(int pipe_id);
extern void pipe_close_write(int pipe_id);

/* Pipe end flags */
#define PIPE_READ_END   0x10    /* This fd is the read end */
#define PIPE_WRITE_END  0x20    /* This fd is the write end */

/* ═══════════════════════════════════════════════════════════════════════════
 * File Descriptor Table
 *
 * LESSON: This is the per-process state that UNIX puts in the kernel.
 * In ExoV6, it's LibOS state - each process can use different fd semantics!
 * ═══════════════════════════════════════════════════════════════════════════ */

struct fd_entry {
    int type;           /* FD_TYPE_* */
    int server_handle;  /* Handle returned by fs_srv (-1 for console) */
    uint64_t offset;    /* Current file offset (for lseek) */
    int flags;          /* Open flags (O_RDONLY, etc.) */
};

static struct fd_entry fd_table[MAX_FD];
static int fd_initialized = 0;

/* ═══════════════════════════════════════════════════════════════════════════
 * Initialization
 *
 * LESSON: stdin/stdout/stderr are pre-opened console devices.
 * In UNIX V6, the kernel sets these up. In ExoV6, we do it ourselves.
 * ═══════════════════════════════════════════════════════════════════════════ */

void fd_init(void) {
    if (fd_initialized) return;

    /* Clear all slots */
    for (int i = 0; i < MAX_FD; i++) {
        fd_table[i].type = FD_TYPE_FREE;
        fd_table[i].server_handle = -1;
        fd_table[i].offset = 0;
        fd_table[i].flags = 0;
    }

    /* Pre-open stdio (console) */
    fd_table[FD_STDIN].type = FD_TYPE_CONSOLE;
    fd_table[FD_STDIN].flags = 0x0001;  /* O_RDONLY */

    fd_table[FD_STDOUT].type = FD_TYPE_CONSOLE;
    fd_table[FD_STDOUT].flags = 0x0002;  /* O_WRONLY */

    fd_table[FD_STDERR].type = FD_TYPE_CONSOLE;
    fd_table[FD_STDERR].flags = 0x0002;  /* O_WRONLY */

    fd_initialized = 1;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * Internal Helpers
 * ═══════════════════════════════════════════════════════════════════════════ */

/**
 * Allocate the lowest available file descriptor
 */
static int fd_alloc(void) {
    fd_init();
    for (int i = 0; i < MAX_FD; i++) {
        if (fd_table[i].type == FD_TYPE_FREE) {
            return i;
        }
    }
    return -1;  /* No free slots */
}

/**
 * Validate file descriptor
 */
static int fd_valid(int fd) {
    if (fd < 0 || fd >= MAX_FD) return 0;
    if (fd_table[fd].type == FD_TYPE_FREE) return 0;
    return 1;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * fd_open() - Open a File
 *
 * LESSON: We allocate a local fd, call fs_client's open() to get a server
 * handle, then store the mapping. The application sees small integers (3, 4, 5...)
 * while the server uses its own handle space.
 * ═══════════════════════════════════════════════════════════════════════════ */

int fd_open(const char *path, int flags) {
    fd_init();

    /* Allocate local fd */
    int fd = fd_alloc();
    if (fd < 0) {
        return -1;  /* Too many open files */
    }

    /* Ask fs_srv to open the file */
    int handle = open(path, flags);
    if (handle < 0) {
        return handle;  /* Pass through error */
    }

    /* Record mapping */
    fd_table[fd].type = FD_TYPE_FILE;
    fd_table[fd].server_handle = handle;
    fd_table[fd].offset = 0;
    fd_table[fd].flags = flags;

    return fd;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * fd_close() - Close a File
 *
 * LESSON: We close the server handle AND free the local fd slot.
 * ═══════════════════════════════════════════════════════════════════════════ */

int fd_close(int fd) {
    if (!fd_valid(fd)) {
        return -1;
    }

    /* Don't close stdio */
    if (fd <= FD_STDERR && fd_table[fd].type == FD_TYPE_CONSOLE) {
        return 0;  /* Silently succeed (like UNIX) */
    }

    /* Close server handle if it's a file */
    if (fd_table[fd].type == FD_TYPE_FILE && fd_table[fd].server_handle >= 0) {
        close(fd_table[fd].server_handle);
    }

    /* Close pipe end */
    if (fd_table[fd].type == FD_TYPE_PIPE && fd_table[fd].server_handle >= 0) {
        if (fd_table[fd].flags & PIPE_READ_END) {
            pipe_close_read(fd_table[fd].server_handle);
        }
        if (fd_table[fd].flags & PIPE_WRITE_END) {
            pipe_close_write(fd_table[fd].server_handle);
        }
    }

    /* Free the slot */
    fd_table[fd].type = FD_TYPE_FREE;
    fd_table[fd].server_handle = -1;
    fd_table[fd].offset = 0;
    fd_table[fd].flags = 0;

    return 0;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * fd_read() - Read from a File Descriptor
 *
 * LESSON: stdin reads from console (blocking), files read from fs_srv.
 * This is where "everything is a file" gets implemented.
 * ═══════════════════════════════════════════════════════════════════════════ */

int fd_read(int fd, void *buf, int n) {
    if (!fd_valid(fd)) {
        return -1;
    }

    if (n <= 0) return 0;

    /* Console input */
    if (fd_table[fd].type == FD_TYPE_CONSOLE) {
        if (fd != FD_STDIN) {
            return -1;  /* Can only read from stdin */
        }

        /*
         * LIONS' LESSON: Reading from console is character-at-a-time.
         * We block until we get the requested bytes or newline.
         */
        char *p = (char *)buf;
        int count = 0;
        while (count < n) {
            int c = sys_cgetc();
            if (c < 0) {
                break;  /* Error or EOF */
            }
            *p++ = (char)c;
            count++;
            if (c == '\n' || c == '\r') {
                break;  /* Line-based input */
            }
        }
        return count;
    }

    /* File read via fs_srv */
    if (fd_table[fd].type == FD_TYPE_FILE) {
        int handle = fd_table[fd].server_handle;
        int bytes = read(handle, buf, n);
        if (bytes > 0) {
            fd_table[fd].offset += bytes;
        }
        return bytes;
    }

    /* Pipe read */
    if (fd_table[fd].type == FD_TYPE_PIPE) {
        if (!(fd_table[fd].flags & PIPE_READ_END)) {
            return -1;  /* Not the read end */
        }
        int pipe_id = fd_table[fd].server_handle;
        return pipe_read(pipe_id, buf, n);
    }

    return -1;  /* Unknown type */
}

/* ═══════════════════════════════════════════════════════════════════════════
 * fd_write() - Write to a File Descriptor
 *
 * LESSON: stdout/stderr write to console, files write to fs_srv.
 * ═══════════════════════════════════════════════════════════════════════════ */

int fd_write(int fd, const void *buf, int n) {
    if (!fd_valid(fd)) {
        return -1;
    }

    if (n <= 0) return 0;

    /* Console output */
    if (fd_table[fd].type == FD_TYPE_CONSOLE) {
        if (fd == FD_STDIN) {
            return -1;  /* Can't write to stdin */
        }
        /* sys_cputs expects a string, but we have raw bytes */
        sys_cputs((const char *)buf, n);
        return n;
    }

    /* File write via fs_srv */
    if (fd_table[fd].type == FD_TYPE_FILE) {
        int handle = fd_table[fd].server_handle;
        int bytes = write(handle, buf, n);
        if (bytes > 0) {
            fd_table[fd].offset += bytes;
        }
        return bytes;
    }

    /* Pipe write */
    if (fd_table[fd].type == FD_TYPE_PIPE) {
        if (!(fd_table[fd].flags & PIPE_WRITE_END)) {
            return -1;  /* Not the write end */
        }
        int pipe_id = fd_table[fd].server_handle;
        return pipe_write(pipe_id, buf, n);
    }

    return -1;  /* Unknown type */
}

/* ═══════════════════════════════════════════════════════════════════════════
 * fd_dup() - Duplicate a File Descriptor
 *
 * LESSON: This is UNIX shell magic - "2>&1" works because of dup().
 * We copy the fd_table entry, but both point to the same server handle.
 * ═══════════════════════════════════════════════════════════════════════════ */

int fd_dup(int fd) {
    if (!fd_valid(fd)) {
        return -1;
    }

    int new_fd = fd_alloc();
    if (new_fd < 0) {
        return -1;
    }

    /* Copy the entry (both now point to same server handle) */
    fd_table[new_fd].type = fd_table[fd].type;
    fd_table[new_fd].server_handle = fd_table[fd].server_handle;
    fd_table[new_fd].offset = fd_table[fd].offset;
    fd_table[new_fd].flags = fd_table[fd].flags;

    /*
     * NOTE: In a full implementation, we'd need reference counting on
     * server handles to know when to actually close them. For now,
     * we don't decrement the server's refcount - this is a simplification.
     */

    return new_fd;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * fd_dup2() - Duplicate to a Specific File Descriptor
 *
 * LESSON: dup2(oldfd, newfd) is essential for I/O redirection.
 * "command > file" closes fd 1, opens file as fd 1, then execs command.
 * ═══════════════════════════════════════════════════════════════════════════ */

int fd_dup2(int oldfd, int newfd) {
    if (!fd_valid(oldfd)) {
        return -1;
    }

    if (newfd < 0 || newfd >= MAX_FD) {
        return -1;
    }

    if (oldfd == newfd) {
        return newfd;  /* No-op */
    }

    /* Close newfd if it's open */
    if (fd_table[newfd].type != FD_TYPE_FREE) {
        fd_close(newfd);
    }

    /* Copy entry */
    fd_table[newfd].type = fd_table[oldfd].type;
    fd_table[newfd].server_handle = fd_table[oldfd].server_handle;
    fd_table[newfd].offset = fd_table[oldfd].offset;
    fd_table[newfd].flags = fd_table[oldfd].flags;

    return newfd;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * fd_lseek() - Seek in a File
 *
 * LESSON: Offset tracking is in LibOS. For now, we only track locally.
 * A full implementation would tell fs_srv about the seek.
 * ═══════════════════════════════════════════════════════════════════════════ */

#define SEEK_SET 0
#define SEEK_CUR 1
#define SEEK_END 2

int fd_lseek(int fd, int offset, int whence) {
    if (!fd_valid(fd)) {
        return -1;
    }

    if (fd_table[fd].type == FD_TYPE_CONSOLE) {
        return -1;  /* Can't seek console */
    }

    if (fd_table[fd].type == FD_TYPE_FILE) {
        switch (whence) {
        case SEEK_SET:
            fd_table[fd].offset = offset;
            break;
        case SEEK_CUR:
            fd_table[fd].offset += offset;
            break;
        case SEEK_END:
            /* Would need file size from fs_srv - not implemented */
            return -1;
        default:
            return -1;
        }
        return (int)fd_table[fd].offset;
    }

    return -1;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * fd_isatty() - Is File Descriptor a Terminal?
 *
 * LESSON: Essential for programs that need to know if they're interactive.
 * ═══════════════════════════════════════════════════════════════════════════ */

int fd_isatty(int fd) {
    if (!fd_valid(fd)) {
        return 0;
    }
    return fd_table[fd].type == FD_TYPE_CONSOLE;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * fd_pipe() - Create a Pipe
 *
 * LESSON: Returns two file descriptors - one for reading, one for writing.
 * This is essential for shell pipelines: "ls | grep foo"
 *
 * The shell:
 *   1. Creates pipe with fd_pipe(pipefd)
 *   2. Spawns left command with stdout → pipefd[1]
 *   3. Spawns right command with stdin → pipefd[0]
 *   4. Closes both ends in the parent
 *   5. Waits for both children
 * ═══════════════════════════════════════════════════════════════════════════ */

int fd_pipe(int pipefd[2]) {
    fd_init();

    /* Create the underlying pipe */
    int pipe_id = pipe_create();
    if (pipe_id < 0) {
        return -1;
    }

    /* Allocate read end fd */
    int read_fd = fd_alloc();
    if (read_fd < 0) {
        pipe_close_read(pipe_id);
        pipe_close_write(pipe_id);
        return -1;
    }

    /* Allocate write end fd */
    int write_fd = fd_alloc();
    if (write_fd < 0) {
        fd_table[read_fd].type = FD_TYPE_FREE;
        pipe_close_read(pipe_id);
        pipe_close_write(pipe_id);
        return -1;
    }

    /* Set up read end */
    fd_table[read_fd].type = FD_TYPE_PIPE;
    fd_table[read_fd].server_handle = pipe_id;
    fd_table[read_fd].offset = 0;
    fd_table[read_fd].flags = PIPE_READ_END;

    /* Set up write end */
    fd_table[write_fd].type = FD_TYPE_PIPE;
    fd_table[write_fd].server_handle = pipe_id;
    fd_table[write_fd].offset = 0;
    fd_table[write_fd].flags = PIPE_WRITE_END;

    /* Return fds */
    pipefd[0] = read_fd;   /* Read end */
    pipefd[1] = write_fd;  /* Write end */

    return 0;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * PEDAGOGICAL SUMMARY
 *
 * This file implements the FILE DESCRIPTOR ABSTRACTION that UNIX made famous.
 *
 * In UNIX V6 (kernel owns the abstraction):
 *   struct file {
 *       char f_flag;    // read/write
 *       char f_count;   // reference count
 *       struct inode *f_inode;
 *       char *f_offset[2];
 *   };
 *   // Kernel file table at files[100]
 *   // Per-process u_ofile[20] points to file table
 *
 * In ExoV6 (LibOS owns the abstraction):
 *   struct fd_entry {
 *       int type;           // console or file
 *       int server_handle;  // fs_srv's reference
 *       uint64_t offset;    // seek position
 *       int flags;          // open mode
 *   };
 *   // Per-process fd_table[] - entirely in user space!
 *
 * The KEY DIFFERENCE:
 *   - UNIX: Kernel validates every fd access (security at syscall boundary)
 *   - ExoV6: LibOS validates fd access (faster, less context switching)
 *           BUT we trust the process not to corrupt its own fd_table
 *
 * This is the EXOKERNEL TRADEOFF:
 *   Less kernel code = simpler kernel = fewer kernel bugs
 *   More LibOS code = more flexibility = application-specific optimization
 *
 * A malicious process could corrupt fd_table - but it can only hurt itself!
 * The fs_srv still validates handles, so one process can't access another's files.
 * ═══════════════════════════════════════════════════════════════════════════ */
