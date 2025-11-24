/**
 * @file fs_client.c
 * @brief File System Client - LibOS File Operations (Phase 11)
 *
 * ╔═══════════════════════════════════════════════════════════════════════════╗
 * ║  LIONS' COMMENTARY FOR THE POST-MONOLITHIC AGE                            ║
 * ║                                                                           ║
 * ║  LESSON: "Everything is a File" is a lie told by the LibOS.               ║
 * ║                                                                           ║
 * ║  In UNIX V6, the kernel implements open(), read(), close() directly.      ║
 * ║  The kernel knows about inodes, directories, file offsets.                ║
 * ║                                                                           ║
 * ║  In ExoV6, the kernel knows NOTHING about files. It only knows:           ║
 * ║    - Physical pages (sys_page_alloc)                                      ║
 * ║    - Virtual mappings (sys_page_map)                                      ║
 * ║    - IPC messages (sys_ipc_send/recv)                                     ║
 * ║                                                                           ║
 * ║  THIS FILE implements the "file" abstraction by sending IPC messages      ║
 * ║  to the File Server (fs_srv). The File Server owns the disk hardware      ║
 * ║  and implements the actual file system.                                   ║
 * ║                                                                           ║
 * ║  MECHANISM (Kernel): Raw IPC, raw pages                                   ║
 * ║  POLICY (LibOS): What "open" and "read" mean                              ║
 * ╚═══════════════════════════════════════════════════════════════════════════╝
 *
 * Architecture:
 *
 *   ┌─────────────┐         IPC          ┌─────────────┐
 *   │   Process   │ ──────────────────▶  │   fs_srv    │
 *   │  (LibOS)    │                      │  (owns disk)│
 *   │             │ ◀──────────────────  │             │
 *   │ open()      │       Response       │ VirtIO + FS │
 *   │ read()      │                      │             │
 *   │ close()     │                      │             │
 *   └─────────────┘                      └─────────────┘
 *
 * This is the MICROKERNEL way. This is the EXOKERNEL way.
 * The kernel is just a message router.
 */

#include <stdint.h>
#include <types.h>
#include <exov6_interface.h>
#include <fs_protocol.h>

/* ═══════════════════════════════════════════════════════════════════════════
 * External Dependencies
 * ═══════════════════════════════════════════════════════════════════════════ */

/* IPC primitives (the ONLY kernel interface we use) */
extern int sys_ipc_send(int target_pid, uint64 w0, uint64 w1, uint64 w2);
extern int sys_ipc_recv(int *sender_pid, uint64 *w0, uint64 *w1, uint64 *w2);

/* Page allocation for shared buffers */
extern uint64 sys_page_alloc_raw(void);
extern int sys_page_map_raw(int target_env, uint64 phys, uint64 virt, int perm);

/* Debug output */
extern void print(const char *s);
extern void print_hex(uint64 n);

/* Permission bits */
#define PERM_R  0x1
#define PERM_W  0x2

/* ═══════════════════════════════════════════════════════════════════════════
 * Shared Buffer for Bulk Data Transfer
 *
 * LESSON: IPC messages are small (3 words). For file data, we need shared
 * memory. The client allocates a page and shares it with the server.
 * This is how microkernels handle bulk data - NOT by copying in the kernel.
 * ═══════════════════════════════════════════════════════════════════════════ */

static uint64 shared_buf_pa = 0;        /* Physical address of shared buffer */
static void *shared_buf_va = 0;          /* Our virtual address */
static int shared_buf_mapped = 0;        /* Is buffer initialized? */

#define SHARED_BUF_VA   0x60000000ULL   /* Where we map our shared buffer */
#define SHARED_BUF_SIZE 4096            /* One page */

/**
 * Initialize the shared buffer for file data transfer
 *
 * LESSON: We allocate a page and tell the File Server about it.
 * Both processes can then read/write this page directly.
 * No kernel copying required!
 */
static int init_shared_buffer(void) {
    if (shared_buf_mapped) {
        return 0;  /* Already initialized */
    }

    /* Allocate physical page */
    shared_buf_pa = sys_page_alloc_raw();
    if ((int64_t)shared_buf_pa < 0) {
        print("[FS_CLIENT] ERROR: Failed to allocate shared buffer\n");
        return -1;
    }

    /* Map into our address space */
    if (sys_page_map_raw(0, shared_buf_pa, SHARED_BUF_VA, PERM_R | PERM_W) < 0) {
        print("[FS_CLIENT] ERROR: Failed to map shared buffer\n");
        return -1;
    }

    shared_buf_va = (void *)SHARED_BUF_VA;
    shared_buf_mapped = 1;

    return 0;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * String Helpers (We're freestanding - no libc)
 * ═══════════════════════════════════════════════════════════════════════════ */

static int strlen_local(const char *s) {
    int len = 0;
    while (*s++) len++;
    return len;
}

static void strcpy_local(char *dst, const char *src) {
    while (*src) *dst++ = *src++;
    *dst = '\0';
}

static void memcpy_local(void *dst, const void *src, int n) {
    uint8_t *d = (uint8_t *)dst;
    const uint8_t *s = (const uint8_t *)src;
    while (n-- > 0) *d++ = *s++;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * IPC Helper: Send Request, Wait for Response
 *
 * LESSON: Every "system call" in traditional UNIX becomes an IPC exchange
 * in microkernel/exokernel land. The kernel doesn't know what we're asking
 * for - it just delivers messages.
 * ═══════════════════════════════════════════════════════════════════════════ */

static int fs_call(int req_type, uint64 arg1, uint64 arg2,
                   uint64 *resp1, uint64 *resp2) {
    /* Send request to File Server */
    if (sys_ipc_send(FS_SERVER_PID, req_type, arg1, arg2) < 0) {
        return -1;
    }

    /* Wait for response */
    int server_pid;
    uint64 r0, r1, r2;
    if (sys_ipc_recv(&server_pid, &r0, &r1, &r2) < 0) {
        return -1;
    }

    /* Verify response is from File Server */
    if (server_pid != FS_SERVER_PID) {
        return -1;
    }

    /* Return results */
    if (resp1) *resp1 = r1;
    if (resp2) *resp2 = r2;

    return (int)r0;  /* Result code */
}

/* ═══════════════════════════════════════════════════════════════════════════
 * open() - Open a File
 *
 * LESSON: In UNIX, open() traps to kernel, kernel finds inode, allocates fd.
 * In ExoV6, open() sends IPC to fs_srv, fs_srv finds inode, returns handle.
 * The "file descriptor" is a LibOS concept we build on top of server handles.
 *
 * For now, we return the server's handle directly as the fd.
 * A full implementation would have a local fd table (see lib/fd.c).
 * ═══════════════════════════════════════════════════════════════════════════ */

int open(const char *path, int flags) {
    /* Initialize shared buffer if needed */
    if (init_shared_buffer() < 0) {
        return -1;
    }

    /* Copy path to shared buffer */
    int path_len = strlen_local(path);
    if (path_len >= SHARED_BUF_SIZE) {
        return -1;  /* Path too long */
    }
    strcpy_local((char *)shared_buf_va, path);

    /*
     * Send OPEN request
     *
     * Protocol:
     *   w0 = FS_REQ_OPEN
     *   w1 = Physical address of shared buffer (contains path)
     *   w2 = flags
     *
     * Response:
     *   w0 = file handle (>= 0) or error (< 0)
     */
    int fd = fs_call(FS_REQ_OPEN, shared_buf_pa, (uint64)flags, 0, 0);

    return fd;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * read() - Read from a File
 *
 * LESSON: Bulk data transfer via shared memory. The server reads disk data
 * into the shared buffer, then we copy it to the user's buffer.
 *
 * This is more complex than a monolithic kernel (one copy vs zero copies)
 * but the ISOLATION is worth it. The file system can crash without
 * bringing down the kernel.
 * ═══════════════════════════════════════════════════════════════════════════ */

int read(int fd, void *buf, int n) {
    if (n <= 0) return 0;
    if (n > SHARED_BUF_SIZE) n = SHARED_BUF_SIZE;

    /* Initialize shared buffer if needed */
    if (init_shared_buffer() < 0) {
        return -1;
    }

    /*
     * Send READ request
     *
     * Protocol:
     *   w0 = FS_REQ_READ
     *   w1 = file handle
     *   w2 = (size << 32) | offset  (we use 0 offset, sequential read)
     *
     * Response:
     *   w0 = bytes read (>= 0) or error (< 0)
     *   Data is in shared buffer
     */
    uint64 packed = ((uint64)n << 32) | 0;  /* size in upper, offset=0 */
    int bytes_read = fs_call(FS_REQ_READ, (uint64)fd, packed, 0, 0);

    if (bytes_read > 0) {
        /* Copy from shared buffer to user buffer */
        memcpy_local(buf, shared_buf_va, bytes_read);
    }

    return bytes_read;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * write() - Write to a File
 *
 * LESSON: Same pattern as read(), but data flows the other direction.
 * We copy to shared buffer, server writes to disk.
 * ═══════════════════════════════════════════════════════════════════════════ */

int write(int fd, const void *buf, int n) {
    if (n <= 0) return 0;
    if (n > SHARED_BUF_SIZE) n = SHARED_BUF_SIZE;

    /* Initialize shared buffer if needed */
    if (init_shared_buffer() < 0) {
        return -1;
    }

    /* Copy data to shared buffer */
    memcpy_local(shared_buf_va, buf, n);

    /*
     * Send WRITE request
     *
     * Protocol:
     *   w0 = FS_REQ_WRITE
     *   w1 = file handle
     *   w2 = size
     *   Data is in shared buffer
     *
     * Response:
     *   w0 = bytes written (>= 0) or error (< 0)
     */
    int bytes_written = fs_call(FS_REQ_WRITE, (uint64)fd, (uint64)n, 0, 0);

    return bytes_written;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * close() - Close a File
 *
 * LESSON: Just an IPC message. The server frees its internal state.
 * ═══════════════════════════════════════════════════════════════════════════ */

int close(int fd) {
    int result = fs_call(FS_REQ_CLOSE, (uint64)fd, 0, 0, 0);
    return result;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * stat() - Get File Status
 *
 * LESSON: File metadata is also retrieved via IPC.
 * ═══════════════════════════════════════════════════════════════════════════ */

int stat(int fd, int *type, uint64 *size) {
    uint64 t, s;
    int result = fs_call(FS_REQ_STAT, (uint64)fd, 0, &t, &s);

    if (result == 0) {
        if (type) *type = (int)t;
        if (size) *size = s;
    }

    return result;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * lseek() - Seek in File
 *
 * LESSON: File offset tracking can be done in LibOS (client-side) or server-side.
 * For TCC compatibility, we implement server-side seeking which allows the server
 * to maintain proper file offsets across multiple operations.
 * ═══════════════════════════════════════════════════════════════════════════ */

int lseek(int fd, int offset, int whence) {
    /*
     * Send LSEEK request
     *
     * Protocol:
     *   w0 = FS_REQ_LSEEK
     *   w1 = file handle
     *   w2 = (whence << 32) | offset
     *
     * Response:
     *   w0 = new file offset (>= 0) or error (< 0)
     */
    uint64 packed = FS_PACK_WHENCE_OFF(whence, offset);
    int new_offset = fs_call(FS_REQ_LSEEK, (uint64)fd, packed, 0, 0);

    return new_offset;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * unlink() - Remove a File
 *
 * LESSON: Unlike traditional UNIX where unlink() decrements link count,
 * in a simplified filesystem we just remove the directory entry.
 * ═══════════════════════════════════════════════════════════════════════════ */

int unlink(const char *path) {
    /* Initialize shared buffer if needed */
    if (init_shared_buffer() < 0) {
        return -1;
    }

    /* Copy path to shared buffer */
    int path_len = strlen_local(path);
    if (path_len >= SHARED_BUF_SIZE) {
        return -1;  /* Path too long */
    }
    strcpy_local((char *)shared_buf_va, path);

    /*
     * Send UNLINK request
     *
     * Protocol:
     *   w0 = FS_REQ_UNLINK
     *   w1 = Physical address of shared buffer (contains path)
     *   w2 = 0
     *
     * Response:
     *   w0 = 0 on success or error (< 0)
     */
    int result = fs_call(FS_REQ_UNLINK, shared_buf_pa, 0, 0, 0);

    return result;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * Directory Operations
 * ═══════════════════════════════════════════════════════════════════════════ */

/**
 * readdir() - Read a directory entry
 *
 * Returns: 1 if entry valid, 0 if end of directory, <0 on error
 */
int readdir(int fd, int index, uint32_t *inum, char *name) {
    uint64 i, n;
    int result = fs_call(FS_REQ_READDIR, (uint64)fd, (uint64)index, &i, &n);

    if (result > 0 && inum) {
        *inum = (uint32_t)i;
    }
    /* Note: Full name would come from shared buffer in complete impl */
    if (name) {
        name[0] = (char)n;  /* First char only for now */
        name[1] = '\0';
    }

    return result;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * PEDAGOGICAL SUMMARY
 *
 * What we've built here is the CLIENT SIDE of a client-server file system.
 *
 * In a monolithic kernel:
 *   open() -> syscall -> kernel VFS -> kernel FS -> kernel disk driver
 *
 * In ExoV6:
 *   open() -> IPC send -> fs_srv -> LibFS -> LibVirtIO -> hardware
 *              ↑                                           ↓
 *           user space                                  user space
 *
 * The kernel NEVER sees the file. It just routes messages.
 *
 * BENEFITS:
 * 1. File system bugs don't crash kernel
 * 2. Can have multiple file system implementations
 * 3. Each process can use different file abstractions
 * 4. Easier to verify (smaller trusted code base)
 *
 * COSTS:
 * 1. More context switches (IPC overhead)
 * 2. Shared memory complexity
 * 3. More code in user space
 *
 * The EXOKERNEL BET: The benefits of flexibility and isolation outweigh
 * the performance cost of IPC. Modern hardware (fast IPC, big caches)
 * makes this bet increasingly favorable.
 * ═══════════════════════════════════════════════════════════════════════════ */
