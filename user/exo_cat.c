/**
 * @file exo_cat.c
 * @brief ExoV6 Cat Utility (Phase 11.7)
 *
 * ╔═══════════════════════════════════════════════════════════════════════════╗
 * ║  LIONS' COMMENTARY FOR THE POST-MONOLITHIC AGE                            ║
 * ║                                                                           ║
 * ║  LESSON: A utility using the LibOS file descriptor abstraction.           ║
 * ║                                                                           ║
 * ║  Stack:                                                                   ║
 * ║    exo_cat → fd_open/fd_read/fd_write → fs_client → IPC → fs_srv         ║
 * ║                                                                           ║
 * ║  The kernel sees ONLY:                                                    ║
 * ║    - IPC messages (sys_ipc_send/recv)                                     ║
 * ║    - Console output (sys_cputs for stdout)                                ║
 * ║                                                                           ║
 * ║  Compare to UNIX cat:                                                     ║
 * ║    cat → read() syscall → kernel VFS → kernel FS → disk driver            ║
 * ║                                                                           ║
 * ║  The ExoV6 path has more hops, but each hop is user-space replaceable!   ║
 * ╚═══════════════════════════════════════════════════════════════════════════╝
 */

#include <stdint.h>
#include <types.h>
#include <fd.h>
#include <fs_protocol.h>

/* ═══════════════════════════════════════════════════════════════════════════
 * External Dependencies
 * ═══════════════════════════════════════════════════════════════════════════ */

extern void print(const char *s);
extern void libos_exception_init(void);

/* ═══════════════════════════════════════════════════════════════════════════
 * cat_fd() - Cat a single file descriptor to stdout
 * ═══════════════════════════════════════════════════════════════════════════ */

static void cat_fd(int fd) {
    char buf[512];
    int n;

    while ((n = fd_read(fd, buf, sizeof(buf))) > 0) {
        if (fd_write(FD_STDOUT, buf, n) != n) {
            print("exo_cat: write error\n");
            return;
        }
    }

    if (n < 0) {
        print("exo_cat: read error\n");
    }
}

/* ═══════════════════════════════════════════════════════════════════════════
 * Main Entry Point
 * ═══════════════════════════════════════════════════════════════════════════ */

int main(int argc, char **argv) {
    /* Initialize LibOS */
    fd_init();
    libos_exception_init();

    print("ExoV6 Cat - File Concatenation Utility\n");
    print("Using LibOS fd layer → fs_client → fs_srv → disk\n\n");

    /* No arguments: read from stdin */
    if (argc <= 1) {
        print("(reading from stdin, press Ctrl-D to end)\n");
        cat_fd(FD_STDIN);
        print("\n[EOF]\n");
    } else {
        /* Process each file argument */
        for (int i = 1; i < argc; i++) {
            print("=== ");
            print(argv[i]);
            print(" ===\n");

            int fd = fd_open(argv[i], FS_O_RDONLY);
            if (fd < 0) {
                print("exo_cat: cannot open ");
                print(argv[i]);
                print("\n");
                continue;
            }

            cat_fd(fd);
            fd_close(fd);
            print("\n");
        }
    }

    /* Halt */
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

/* ═══════════════════════════════════════════════════════════════════════════
 * PEDAGOGICAL NOTE
 *
 * This tiny cat utility demonstrates the full ExoV6 I/O stack:
 *
 *   main() calls fd_open("/etc/passwd", O_RDONLY)
 *     ↓
 *   fd.c: allocate local fd=3, call open("/etc/passwd", flags)
 *     ↓
 *   fs_client.c: send IPC(FS_REQ_OPEN, ...) to fs_srv
 *     ↓
 *   kernel: route IPC message to fs_srv
 *     ↓
 *   fs_srv: lookup inode, allocate handle=7, reply
 *     ↓
 *   fd.c: store mapping fd=3 → handle=7
 *     ↓
 *   main() calls fd_read(3, buf, 512)
 *     ↓
 *   fd.c: fd=3 → handle=7, call read(7, buf, 512)
 *     ↓
 *   fs_client.c: send IPC(FS_REQ_READ, handle=7, size=512)
 *     ↓
 *   kernel: route IPC to fs_srv
 *     ↓
 *   fs_srv: read from VirtIO disk via libvirtio, copy to shared buf
 *     ↓
 *   fs_client.c: copy from shared buf to user buf
 *     ↓
 *   main() calls fd_write(1, buf, n)
 *     ↓
 *   fd.c: fd=1 is console → call sys_cputs(buf, n)
 *     ↓
 *   kernel: write to UART/console
 *
 * Every step except the kernel IPC routing and sys_cputs is REPLACEABLE!
 * ═══════════════════════════════════════════════════════════════════════════ */
