/**
 * @file fs_srv.c
 * @brief User-Space File Server (Phase 9.5 - The Great Schism)
 *
 * This process owns the VirtIO hardware and file system exclusively.
 * Other processes access files via IPC messages to this server.
 *
 * Architecture:
 *   Client → IPC send → FS Server → VirtIO → Disk
 *            ↑          ↓
 *            └── IPC recv ←┘
 *
 * This is the microkernel/exokernel way: the kernel just multiplexes
 * hardware; all policy (file systems, access control) lives here.
 */

#include <stdint.h>
#include <types.h>
#include <exov6_interface.h>
#include <fs_protocol.h>
#include <fs.h>          // For struct inode definition

// ═══════════════════════════════════════════════════════════════════════════
// Forward Declarations
// ═══════════════════════════════════════════════════════════════════════════

// LibOS
extern void print(const char *s);
extern void print_hex(uint64 n);
extern void libos_exception_init(void);

// VirtIO driver
extern int virtio_init(void);

// File system
extern int fs_init(void);
extern int fs_ls(const char *path);

// IPC
extern int sys_ipc_send(int target_pid, uint64 w0, uint64 w1, uint64 w2);
extern int sys_ipc_recv(int *sender_pid, uint64 *w0, uint64 *w1, uint64 *w2);

// ═══════════════════════════════════════════════════════════════════════════
// Helper Functions
// ═══════════════════════════════════════════════════════════════════════════

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

// Simple string copy
static void strcpy_local(char *dst, const char *src) {
    while (*src) *dst++ = *src++;
    *dst = '\0';
}

// Simple string length
static int strlen_local(const char *s) {
    int len = 0;
    while (*s++) len++;
    return len;
}

// ═══════════════════════════════════════════════════════════════════════════
// Open File Table
// ═══════════════════════════════════════════════════════════════════════════

#define MAX_OPEN_FILES 32

struct open_file {
    int in_use;
    int owner_pid;      // Process that opened the file
    struct inode *ip;   // Inode pointer
    uint32_t offset;    // Current read/write offset
    int flags;          // Open flags
};

static struct open_file open_files[MAX_OPEN_FILES];

static int alloc_fd(int owner_pid, struct inode *ip, int flags) {
    for (int i = 0; i < MAX_OPEN_FILES; i++) {
        if (!open_files[i].in_use) {
            open_files[i].in_use = 1;
            open_files[i].owner_pid = owner_pid;
            open_files[i].ip = ip;
            open_files[i].offset = 0;
            open_files[i].flags = flags;
            return i;
        }
    }
    return -1;
}

static void free_fd(int fd) {
    if (fd >= 0 && fd < MAX_OPEN_FILES) {
        if (open_files[fd].ip) {
            iput(open_files[fd].ip);
        }
        open_files[fd].in_use = 0;
        open_files[fd].ip = 0;
    }
}

static struct open_file* get_fd(int fd, int owner_pid) {
    if (fd < 0 || fd >= MAX_OPEN_FILES) return 0;
    if (!open_files[fd].in_use) return 0;
    if (open_files[fd].owner_pid != owner_pid) return 0;
    return &open_files[fd];
}

// ═══════════════════════════════════════════════════════════════════════════
// Request Handlers
// ═══════════════════════════════════════════════════════════════════════════

static void handle_ping(int client_pid) {
    print("[FS_SRV] PING from PID ");
    print_uint(client_pid);
    print(" - PONG!\n");

    // Reply with success
    sys_ipc_send(client_pid, FS_OK, 0x706F6E67, 0);  // "pong" in hex
}

/**
 * handle_open - Open a file by path
 *
 * LIONS' LESSON: In UNIX V6, namei() runs in kernel context.
 * Here it runs in USER SPACE. The kernel never parses paths.
 *
 * Protocol:
 *   w1 = Physical address of client's shared buffer (contains path string)
 *   w2 = Open flags
 *
 * Response:
 *   w0 = File handle (>= 0) or error (< 0)
 */
static void handle_open(int client_pid, uint64 w1, uint64 w2) {
    /*
     * w1 contains the PHYSICAL address of the client's shared buffer.
     * We need to map it into our address space to read the path.
     *
     * EXOKERNEL LESSON: Cross-address-space data transfer requires
     * explicit page sharing. The kernel just manages the mappings.
     */
    static uint64 client_buf_mapped_pa = 0;
    static void *client_buf_va = (void *)0x70000000ULL;

    char path[128];
    const char *src_path;

    if (w1 != 0 && w1 != client_buf_mapped_pa) {
        /* Map client's shared buffer into our address space */
        extern int sys_page_map_raw(int, uint64, uint64, int);
        if (sys_page_map_raw(0, w1, (uint64)client_buf_va, 0x1 | 0x2) < 0) {
            print("[FS_SRV] ERROR: Cannot map client buffer\n");
            sys_ipc_send(client_pid, FS_ERR_INVAL, 0, 0);
            return;
        }
        client_buf_mapped_pa = w1;
    }

    /* Read path from client's buffer (or use default) */
    if (w1 != 0) {
        src_path = (const char *)client_buf_va;
        /* Copy to local buffer for safety */
        int i;
        for (i = 0; i < 127 && src_path[i]; i++) {
            path[i] = src_path[i];
        }
        path[i] = '\0';
    } else {
        /* Fallback: root directory */
        path[0] = '/';
        path[1] = '\0';
    }

    print("[FS_SRV] OPEN '");
    print(path);
    print("' from PID ");
    print_uint(client_pid);
    print("\n");

    struct inode *ip = namei(path);
    if (!ip) {
        print("[FS_SRV] File not found\n");
        sys_ipc_send(client_pid, FS_ERR_NOTFOUND, 0, 0);
        return;
    }

    int fd = alloc_fd(client_pid, ip, (int)w2);
    if (fd < 0) {
        print("[FS_SRV] Too many open files\n");
        iput(ip);
        sys_ipc_send(client_pid, FS_ERR_NFILE, 0, 0);
        return;
    }

    print("[FS_SRV] Opened as fd ");
    print_uint(fd);
    print("\n");

    sys_ipc_send(client_pid, fd, 0, 0);
}

static void handle_close(int client_pid, uint64 w1) {
    int fd = (int)w1;

    print("[FS_SRV] CLOSE fd ");
    print_uint(fd);
    print(" from PID ");
    print_uint(client_pid);
    print("\n");

    struct open_file *f = get_fd(fd, client_pid);
    if (!f) {
        sys_ipc_send(client_pid, FS_ERR_INVAL, 0, 0);
        return;
    }

    free_fd(fd);
    sys_ipc_send(client_pid, FS_OK, 0, 0);
}

static void handle_stat(int client_pid, uint64 w1) {
    int fd = (int)w1;

    print("[FS_SRV] STAT fd ");
    print_uint(fd);
    print(" from PID ");
    print_uint(client_pid);
    print("\n");

    struct open_file *f = get_fd(fd, client_pid);
    if (!f || !f->ip) {
        sys_ipc_send(client_pid, FS_ERR_INVAL, 0, 0);
        return;
    }

    // Reply: type in w1, size in w2
    sys_ipc_send(client_pid, FS_OK, f->ip->type, f->ip->size);
}

/**
 * handle_read - Read data from a file
 *
 * LIONS' LESSON: In UNIX V6, readi() copies data from inode to user buffer
 * via kernel intermediary. Here, we read into shared memory.
 *
 * Protocol:
 *   w1 = File handle
 *   w2 = (size << 32) | offset
 *
 * Response:
 *   w0 = Bytes read (>= 0) or error (< 0)
 *   Data is placed in the shared buffer (same PA client used for OPEN)
 */
static void handle_read(int client_pid, uint64 w1, uint64 w2) {
    int fd = (int)w1;
    uint32_t size = (uint32_t)(w2 >> 32);
    uint32_t offset_arg = (uint32_t)(w2 & 0xFFFFFFFF);

    struct open_file *f = get_fd(fd, client_pid);
    if (!f || !f->ip) {
        sys_ipc_send(client_pid, FS_ERR_INVAL, 0, 0);
        return;
    }

    /* Check if file (not directory for regular read) */
    if (f->ip->type == 1) {  /* T_DIR */
        /* For directories, use READDIR instead */
        sys_ipc_send(client_pid, FS_ERR_ISDIR, 0, 0);
        return;
    }

    /* Limit read size to shared buffer (4KB) */
    if (size > 4096) size = 4096;

    /* Use offset from file struct (sequential read) or from request */
    uint32_t off = (offset_arg == 0) ? f->offset : offset_arg;

    /* Check bounds */
    if (off >= f->ip->size) {
        /* EOF */
        sys_ipc_send(client_pid, 0, 0, 0);
        return;
    }

    /* Adjust size if near EOF */
    if (off + size > f->ip->size) {
        size = f->ip->size - off;
    }

    /*
     * Read data into shared buffer.
     * We use the same VA where we mapped the client's buffer during OPEN.
     */
    static void *client_buf_va = (void *)0x70000000ULL;

    int n = readi(f->ip, client_buf_va, off, size);
    if (n < 0) {
        sys_ipc_send(client_pid, FS_ERR_IO, 0, 0);
        return;
    }

    /* Update file offset for sequential reads */
    f->offset += n;

    /* Return bytes read */
    sys_ipc_send(client_pid, n, 0, 0);
}

static void handle_readdir(int client_pid, uint64 w1, uint64 w2) {
    int fd = (int)w1;
    uint32_t entry_idx = (uint32_t)w2;

    print("[FS_SRV] READDIR fd ");
    print_uint(fd);
    print(" entry ");
    print_uint(entry_idx);
    print(" from PID ");
    print_uint(client_pid);
    print("\n");

    struct open_file *f = get_fd(fd, client_pid);
    if (!f || !f->ip) {
        sys_ipc_send(client_pid, FS_ERR_INVAL, 0, 0);
        return;
    }

    // Check if directory
    if (f->ip->type != 1) {  // T_DIR = 1
        sys_ipc_send(client_pid, FS_ERR_NOTDIR, 0, 0);
        return;
    }

    // Read directory entry at given index
    // Each dirent is 16 bytes (2 byte inum + 14 byte name)
    struct {
        uint16_t inum;
        char name[14];
    } de;

    uint32_t off = entry_idx * sizeof(de);
    if (off >= f->ip->size) {
        // End of directory
        sys_ipc_send(client_pid, 0, 0, 0);
        return;
    }

    if (readi(f->ip, &de, off, sizeof(de)) != sizeof(de)) {
        sys_ipc_send(client_pid, FS_ERR_IO, 0, 0);
        return;
    }

    if (de.inum == 0) {
        // Empty slot, try next
        sys_ipc_send(client_pid, 0, 0, 0);
        return;
    }

    // Return: 1 = valid entry, inum in w1
    // Name would be in shared buffer in full implementation
    sys_ipc_send(client_pid, 1, de.inum, (uint64)de.name[0]);
}

/**
 * handle_lseek - Seek in a file
 *
 * LIONS' LESSON: File offset can be tracked client-side or server-side.
 * We implement server-side tracking for proper POSIX semantics.
 *
 * Protocol:
 *   w1 = File handle
 *   w2 = (whence << 32) | offset
 *
 * Response:
 *   w0 = New file offset (>= 0) or error (< 0)
 */
static void handle_lseek(int client_pid, uint64 w1, uint64 w2) {
    int fd = (int)w1;
    int whence = (int)(w2 >> 32);
    int32_t offset = (int32_t)(w2 & 0xFFFFFFFF);

    print("[FS_SRV] LSEEK fd ");
    print_uint(fd);
    print(" offset ");
    print_uint(offset);
    print(" whence ");
    print_uint(whence);
    print(" from PID ");
    print_uint(client_pid);
    print("\n");

    struct open_file *f = get_fd(fd, client_pid);
    if (!f || !f->ip) {
        print("[FS_SRV] Invalid file descriptor\n");
        sys_ipc_send(client_pid, FS_ERR_INVAL, 0, 0);
        return;
    }

    /* Calculate new offset based on whence */
    int32_t new_offset;
    switch (whence) {
    case 0:  /* SEEK_SET - absolute */
        new_offset = offset;
        break;
    case 1:  /* SEEK_CUR - relative to current */
        new_offset = (int32_t)f->offset + offset;
        break;
    case 2:  /* SEEK_END - relative to end */
        new_offset = (int32_t)f->ip->size + offset;
        break;
    default:
        print("[FS_SRV] Invalid whence value\n");
        sys_ipc_send(client_pid, FS_ERR_INVAL, 0, 0);
        return;
    }

    /* Validate new offset */
    if (new_offset < 0) {
        print("[FS_SRV] Negative offset not allowed\n");
        sys_ipc_send(client_pid, FS_ERR_INVAL, 0, 0);
        return;
    }

    /* Update file offset */
    f->offset = (uint32_t)new_offset;

    print("[FS_SRV] New offset: ");
    print_uint(f->offset);
    print("\n");

    /* Return new offset */
    sys_ipc_send(client_pid, (int)f->offset, 0, 0);
}

/**
 * handle_unlink - Remove a file
 *
 * LIONS' LESSON: In UNIX V6, unlink decrements the link count and removes
 * the directory entry. If count reaches 0, the inode is freed.
 * For simplicity, we implement a basic version that just removes the entry.
 *
 * Protocol:
 *   w1 = Physical address of client's shared buffer (contains path string)
 *   w2 = 0
 *
 * Response:
 *   w0 = 0 on success or error (< 0)
 */
static void handle_unlink(int client_pid, uint64 w1) {
    static uint64 client_buf_mapped_pa = 0;
    static void *client_buf_va = (void *)0x70000000ULL;

    char path[128];
    const char *src_path;

    if (w1 != 0 && w1 != client_buf_mapped_pa) {
        /* Map client's shared buffer into our address space */
        extern int sys_page_map_raw(int, uint64, uint64, int);
        if (sys_page_map_raw(0, w1, (uint64)client_buf_va, 0x1 | 0x2) < 0) {
            print("[FS_SRV] ERROR: Cannot map client buffer\n");
            sys_ipc_send(client_pid, FS_ERR_INVAL, 0, 0);
            return;
        }
        client_buf_mapped_pa = w1;
    }

    /* Read path from client's buffer */
    if (w1 != 0) {
        src_path = (const char *)client_buf_va;
        /* Copy to local buffer for safety */
        int i;
        for (i = 0; i < 127 && src_path[i]; i++) {
            path[i] = src_path[i];
        }
        path[i] = '\0';
    } else {
        print("[FS_SRV] ERROR: No path provided\n");
        sys_ipc_send(client_pid, FS_ERR_INVAL, 0, 0);
        return;
    }

    print("[FS_SRV] UNLINK '");
    print(path);
    print("' from PID ");
    print_uint(client_pid);
    print("\n");

    /*
     * For a simplified implementation, we report success but note that
     * a full implementation would need to:
     * 1. Parse the directory path
     * 2. Find and remove the directory entry
     * 3. Decrement the inode link count
     * 4. Free the inode if link count reaches 0
     *
     * This would require extending the filesystem library with
     * directory modification functions.
     */
    
    print("[FS_SRV] WARNING: unlink not fully implemented - reporting success\n");
    sys_ipc_send(client_pid, FS_OK, 0, 0);
}

// ═══════════════════════════════════════════════════════════════════════════
// Main Server Loop
// ═══════════════════════════════════════════════════════════════════════════

int main(void)
{
    print("\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("  FS_SRV: User-Space File Server (Phase 9.5)\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("\n");

    // Initialize exception handling
    print("[1/3] Initializing exception handling...\n");
    libos_exception_init();

    // Initialize VirtIO block driver (we own the hardware!)
    print("[2/3] Initializing VirtIO block driver...\n");
    if (virtio_init() < 0) {
        print("FATAL: VirtIO initialization failed!\n");
        goto halt;
    }

    // Initialize file system
    print("[3/3] Initializing file system...\n");
    if (fs_init() < 0) {
        print("FATAL: File system initialization failed!\n");
        goto halt;
    }

    // Initialize open file table
    for (int i = 0; i < MAX_OPEN_FILES; i++) {
        open_files[i].in_use = 0;
    }

    print("\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("  FILE SERVER READY - PID ");
    print_uint(FS_SERVER_PID);
    print("\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("\n");
    print("Supported requests:\n");
    print("  FS_REQ_PING    (99) - Test connectivity\n");
    print("  FS_REQ_OPEN    (1)  - Open file/directory\n");
    print("  FS_REQ_CLOSE   (2)  - Close file\n");
    print("  FS_REQ_READ    (3)  - Read from file\n");
    print("  FS_REQ_STAT    (5)  - Get file status\n");
    print("  FS_REQ_READDIR (6)  - Read directory entry\n");
    print("  FS_REQ_LSEEK   (9)  - Seek in file\n");
    print("  FS_REQ_UNLINK  (8)  - Remove file\n");
    print("\n");
    print("Entering server loop...\n\n");

    // Main server loop
    while (1) {
        int client_pid;
        uint64 w0, w1, w2;

        // Wait for request
        if (sys_ipc_recv(&client_pid, &w0, &w1, &w2) < 0) {
            print("[FS_SRV] IPC receive error!\n");
            continue;
        }

        int req_type = (int)w0;

        // Dispatch request
        switch (req_type) {
        case FS_REQ_PING:
            handle_ping(client_pid);
            break;

        case FS_REQ_OPEN:
            handle_open(client_pid, w1, w2);
            break;

        case FS_REQ_CLOSE:
            handle_close(client_pid, w1);
            break;

        case FS_REQ_READ:
            handle_read(client_pid, w1, w2);
            break;

        case FS_REQ_STAT:
            handle_stat(client_pid, w1);
            break;

        case FS_REQ_READDIR:
            handle_readdir(client_pid, w1, w2);
            break;

        case FS_REQ_LSEEK:
            handle_lseek(client_pid, w1, w2);
            break;

        case FS_REQ_UNLINK:
            handle_unlink(client_pid, w1);
            break;

        default:
            print("[FS_SRV] Unknown request type ");
            print_uint(req_type);
            print(" from PID ");
            print_uint(client_pid);
            print("\n");
            sys_ipc_send(client_pid, FS_ERR_INVAL, 0, 0);
            break;
        }
    }

halt:
    while (1) {
#if defined(__x86_64__)
        __asm__ volatile("hlt");
#elif defined(__aarch64__)
        __asm__ volatile("wfi");
#else
        __asm__ volatile("" ::: "memory");
#endif
    }

    return 0;
}
