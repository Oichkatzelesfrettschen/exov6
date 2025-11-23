/**
 * @file virtio_driver.c
 * @brief User-Space VirtIO Block Driver (Phase 7)
 *
 * This is the ultimate exokernel demonstration: a user-space disk driver
 * that directly accesses VirtIO hardware without kernel mediation.
 *
 * The Architecture:
 * 1. MECHANISM: Kernel exports VirtIO MMIO region via sys_page_map()
 * 2. POLICY: User driver initializes VirtIO queues and issues I/O
 * 3. INTERRUPTS: Disk completion fires IRQ -> kernel upcalls -> driver
 *
 * VirtIO MMIO Specification: https://docs.oasis-open.org/virtio/virtio/v1.1/
 */

#include <stdint.h>
#include <types.h>
#include <exov6_interface.h>

// Forward declarations from lib/
extern void print(const char *s);
extern void print_hex(uint64 n);
extern uint64 sys_alloc_page(void);
extern int sys_map_page(int target_env, uint64 phys, uint64 virt, int perm);
extern void sys_cputs(const char *s, int len);
extern void libos_exception_init(void);

// Where we'll map the VirtIO MMIO registers
#define VIRTIO_VADDR    0x40000000ULL

// Helper: read a 32-bit MMIO register
static inline uint32_t virtio_read32(volatile uint32_t *base, uint32_t offset) {
    return base[offset / 4];
}

// Helper: write a 32-bit MMIO register
static inline void virtio_write32(volatile uint32_t *base, uint32_t offset, uint32_t val) {
    base[offset / 4] = val;
}

// Helper: print a 32-bit number
static void print_uint32(uint32_t n) {
    if (n == 0) {
        print("0");
        return;
    }
    char buf[12];
    int i = 0;
    while (n > 0) {
        buf[i++] = '0' + (n % 10);
        n /= 10;
    }
    // Reverse
    char out[12];
    for (int j = 0; j < i; j++) {
        out[j] = buf[i - 1 - j];
    }
    out[i] = '\0';
    print(out);
}

int main(void)
{
    print("\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("  VIRTIO_DRIVER: User-Space Block Device Test (Phase 7)\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("\n");

    // Initialize exception handling (for potential IRQ upcalls)
    print("[1] Initializing exception handling...\n");
    libos_exception_init();

    // Step 1: Map the VirtIO MMIO region
    print("[2] Mapping VirtIO MMIO region...\n");
    print("    Physical: ");
    print_hex(VIRTIO0_BASE);
    print("\n    Virtual:  ");
    print_hex(VIRTIO_VADDR);
    print("\n");

    // Request MMIO mapping from kernel (requires LABEL_HIGH)
    int result = sys_map_page(0, VIRTIO0_BASE, VIRTIO_VADDR, 0x3);  // RW permissions

    if (result < 0) {
        print("    FAILED: Could not map VirtIO MMIO region!\n");
        print("    (Process may lack LABEL_HIGH privilege)\n");
        return -1;
    }
    print("    SUCCESS: MMIO region mapped!\n\n");

    volatile uint32_t *base = (volatile uint32_t *)VIRTIO_VADDR;

    // Step 2: Read and verify Magic Value
    print("[3] Checking VirtIO Magic Value...\n");
    uint32_t magic = virtio_read32(base, VIRTIO_MMIO_MAGIC_VALUE);
    print("    Magic: ");
    print_hex(magic);
    print(" (expected 0x74726976 = 'virt')\n");

    if (magic != VIRTIO_MAGIC) {
        print("    FAILED: Invalid Magic Value!\n");
        print("    This is not a VirtIO device.\n");
        return -1;
    }
    print("    SUCCESS: Magic Value verified!\n\n");

    // Step 3: Read device information
    print("[4] Reading device information...\n");

    uint32_t version = virtio_read32(base, VIRTIO_MMIO_VERSION);
    uint32_t device_id = virtio_read32(base, VIRTIO_MMIO_DEVICE_ID);
    uint32_t vendor_id = virtio_read32(base, VIRTIO_MMIO_VENDOR_ID);

    print("    Version:   ");
    print_uint32(version);
    print(" (1=legacy, 2=modern)\n");

    print("    Device ID: ");
    print_uint32(device_id);
    if (device_id == 0) {
        print(" (NO DEVICE PRESENT)\n");
    } else if (device_id == 1) {
        print(" (Network Card)\n");
    } else if (device_id == 2) {
        print(" (Block Device - DISK)\n");
    } else if (device_id == 4) {
        print(" (Random Number Generator)\n");
    } else {
        print(" (Unknown)\n");
    }

    print("    Vendor ID: ");
    print_hex(vendor_id);
    print("\n\n");

    // Check if device is present
    if (device_id == 0) {
        print("═══════════════════════════════════════════════════════════\n");
        print("  WARNING: No VirtIO device present at this address.\n");
        print("  Make sure QEMU is started with a block device:\n");
        print("    -drive file=disk.img,format=raw,if=none,id=disk0 \\\n");
        print("    -device virtio-blk-device,drive=disk0\n");
        print("═══════════════════════════════════════════════════════════\n");
        return -1;
    }

    // Step 4: Read device features
    print("[5] Reading device features...\n");
    uint32_t features = virtio_read32(base, VIRTIO_MMIO_DEVICE_FEATURES);
    print("    Features: ");
    print_hex(features);
    print("\n");

    if (features & VIRTIO_BLK_F_RO) {
        print("    - Read-Only device\n");
    }
    if (features & VIRTIO_BLK_F_BLK_SIZE) {
        print("    - Block size negotiable\n");
    }
    if (features & VIRTIO_BLK_F_GEOMETRY) {
        print("    - Geometry available\n");
    }
    print("\n");

    // Step 5: Read current device status
    print("[6] Reading device status...\n");
    uint32_t status = virtio_read32(base, VIRTIO_MMIO_STATUS);
    print("    Status: ");
    print_hex(status);
    print("\n");

    if (status == 0) {
        print("    Device is RESET (not initialized)\n");
    } else {
        if (status & VIRTIO_STATUS_ACKNOWLEDGE)
            print("    - ACKNOWLEDGE\n");
        if (status & VIRTIO_STATUS_DRIVER)
            print("    - DRIVER\n");
        if (status & VIRTIO_STATUS_FEATURES_OK)
            print("    - FEATURES_OK\n");
        if (status & VIRTIO_STATUS_DRIVER_OK)
            print("    - DRIVER_OK\n");
        if (status & VIRTIO_STATUS_FAILED)
            print("    - FAILED\n");
    }

    print("\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("  VIRTIO SANITY CHECK PASSED!\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("\n");
    print("The user-space driver successfully:\n");
    print("  1. Mapped VirtIO MMIO region from kernel\n");
    print("  2. Verified Magic Value (device is VirtIO)\n");
    print("  3. Read device type and features\n");
    print("\n");
    print("Next steps for full driver implementation:\n");
    print("  1. Initialize device (set status bits)\n");
    print("  2. Set up virtqueues (descriptor rings)\n");
    print("  3. Negotiate features\n");
    print("  4. Issue read/write requests\n");
    print("  5. Handle completion interrupts via upcall\n");
    print("\n");
    print("═══════════════════════════════════════════════════════════\n");

    // Spin forever
    while (1) {
#if defined(__x86_64__)
        __asm__ volatile("hlt");
#elif defined(__aarch64__)
        __asm__ volatile("wfi");  // Wait For Interrupt (ARM64)
#else
        __asm__ volatile("" ::: "memory");  // Generic busy-wait
#endif
    }

    return 0;
}
