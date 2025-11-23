/**
 * @file fs_test.c
 * @brief User-Space File System Test (Phase 8)
 *
 * This test demonstrates the full exokernel stack:
 *   User Program → LibFS → VirtIO Driver → Hardware
 *
 * It reads an xv6 fs.img and lists the root directory contents.
 */

#include <stdint.h>
#include <types.h>
#include <exov6_interface.h>

// LibOS functions
extern void print(const char *s);
extern void print_hex(uint64 n);
extern void libos_exception_init(void);
extern void scheduler_init(void);

// VirtIO driver
extern int virtio_init(void);
extern int virtio_is_ready(void);

// File system
extern int fs_init(void);
extern int fs_ls(const char *path);

int main(void)
{
    print("\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("  FS_TEST: User-Space File System (Phase 8)\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("\n");
    print("This test demonstrates the full exokernel I/O stack:\n");
    print("  User Program → LibFS → VirtIO Driver → Hardware\n");
    print("\n");

    // Initialize exception handling (for upcalls/IRQs)
    print("[1/4] Initializing exception handling...\n");
    libos_exception_init();

    // Initialize scheduler (for preemption)
    print("[2/4] Initializing scheduler...\n");
    scheduler_init();

    // Initialize VirtIO block driver
    print("[3/4] Initializing VirtIO block driver...\n");
    if (virtio_init() < 0) {
        print("ERROR: VirtIO initialization failed!\n");
        print("Make sure QEMU has a disk image attached.\n");
        goto halt;
    }

    // Initialize file system
    print("[4/4] Initializing file system...\n");
    if (fs_init() < 0) {
        print("ERROR: File system initialization failed!\n");
        goto halt;
    }

    // ═══════════════════════════════════════════════════════════════════
    // Test: List root directory
    // ═══════════════════════════════════════════════════════════════════

    print("═══════════════════════════════════════════════════════════\n");
    print("  LISTING ROOT DIRECTORY\n");
    print("═══════════════════════════════════════════════════════════\n");

    if (fs_ls("/") < 0) {
        print("ERROR: Could not list root directory!\n");
        goto halt;
    }

    // ═══════════════════════════════════════════════════════════════════
    // Success!
    // ═══════════════════════════════════════════════════════════════════

    print("═══════════════════════════════════════════════════════════\n");
    print("  PHASE 8 COMPLETE: USER-SPACE FILE SYSTEM\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("\n");
    print("The exokernel OS now has LONG-TERM MEMORY:\n");
    print("  - VirtIO block driver reads raw sectors\n");
    print("  - LibFS interprets bytes as files/directories\n");
    print("  - NO kernel file system code needed!\n");
    print("\n");
    print("The OS can now:\n");
    print("  1. SURVIVE (Scheduler/Preemption)\n");
    print("  2. SEE (Console)\n");
    print("  3. TOUCH (VirtIO Disk Driver)\n");
    print("  4. REACT (IRQs/Upcalls)\n");
    print("  5. REMEMBER (File System)\n");
    print("\n");

halt:
    // Halt
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
