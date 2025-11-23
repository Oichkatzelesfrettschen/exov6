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

static void handle_open(int client_pid, uint64 w1, uint64 w2) {
    // w1 = path pointer (in shared buffer)
    // w2 = flags

    // For simplicity, path is passed directly (in real impl, use shared mem)
    // Here we just support opening root directory for now
    const char *path = "/";  // Simplified: always open root

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
    print("  FS_REQ_STAT    (5)  - Get file status\n");
    print("  FS_REQ_READDIR (6)  - Read directory entry\n");
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

        case FS_REQ_STAT:
            handle_stat(client_pid, w1);
            break;

        case FS_REQ_READDIR:
            handle_readdir(client_pid, w1, w2);
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
