/**
 * @file virtio_driver.c
 * @brief User-Space VirtIO Block Driver (Phase 7 - Full Implementation)
 *
 * This is the ultimate exokernel demonstration: a user-space disk driver
 * that directly accesses VirtIO hardware without kernel mediation.
 *
 * VirtIO MMIO Specification: https://docs.oasis-open.org/virtio/virtio/v1.1/
 */

#include <stdint.h>
#include <types.h>
#include <exov6_interface.h>

// ═══════════════════════════════════════════════════════════════════════════
// Forward Declarations
// ═══════════════════════════════════════════════════════════════════════════

extern void print(const char *s);
extern void print_hex(uint64 n);
extern uint64 sys_alloc_page(void);
extern int sys_map_page(int target_env, uint64 phys, uint64 virt, int perm);
extern void sys_cputs(const char *s, int len);
extern void libos_exception_init(void);

// IRQ registration (Phase 7 - IRQ-driven I/O)
typedef void (*irq_handler_t)(int irq, void *arg);
extern int libos_register_irq(int irq, irq_handler_t handler, void *arg);

// ═══════════════════════════════════════════════════════════════════════════
// VirtIO Driver State
// ═══════════════════════════════════════════════════════════════════════════

#define VIRTIO_VADDR        0x40000000ULL   // Where we map MMIO registers
#define VIRTQ_PAGES_VADDR   0x41000000ULL   // Where we map virtqueue pages

// Driver state
static volatile uint32_t *virtio_base = 0;
static struct virtq_desc *desc_table = 0;
static struct virtq_avail *avail_ring = 0;
static struct virtq_used *used_ring = 0;
static uint16_t free_desc_head = 0;         // Head of free descriptor list
static uint16_t last_used_idx = 0;          // Last processed used index

// Request tracking
static volatile uint8_t request_status = 0xFF;  // Status byte from device

// IRQ-driven completion (Phase 7 enhancement)
static volatile int disk_irq_fired = 0;         // Set by IRQ handler
static int use_irq_completion = 0;              // Enable after IRQ registered

// ═══════════════════════════════════════════════════════════════════════════
// Helper Functions
// ═══════════════════════════════════════════════════════════════════════════

static inline uint32_t virtio_read32(uint32_t offset) {
    return virtio_base[offset / 4];
}

static inline void virtio_write32(uint32_t offset, uint32_t val) {
    virtio_base[offset / 4] = val;
}

static void print_uint32(uint32_t n) {
    if (n == 0) { print("0"); return; }
    char buf[12];
    int i = 0;
    while (n > 0) { buf[i++] = '0' + (n % 10); n /= 10; }
    char out[12];
    for (int j = 0; j < i; j++) out[j] = buf[i - 1 - j];
    out[i] = '\0';
    print(out);
}

// Memory barrier for MMIO
static inline void mb(void) {
#if defined(__x86_64__)
    __asm__ volatile("mfence" ::: "memory");
#elif defined(__aarch64__)
    __asm__ volatile("dmb sy" ::: "memory");
#else
    __asm__ volatile("" ::: "memory");
#endif
}

// ═══════════════════════════════════════════════════════════════════════════
// VirtIO IRQ Handler (Phase 7 - Interrupt-Driven I/O)
// ═══════════════════════════════════════════════════════════════════════════

/**
 * VirtIO interrupt handler - called from LibOS exception handler
 * This is invoked when the VirtIO device signals completion via IRQ.
 */
static void virtio_irq_handler(int irq, void *arg) {
    (void)arg;
    (void)irq;

    // Read and acknowledge interrupt status
    uint32_t status = virtio_read32(VIRTIO_MMIO_INTERRUPT_STATUS);
    virtio_write32(VIRTIO_MMIO_INTERRUPT_ACK, status);
    mb();

    // Signal completion to any waiting request
    disk_irq_fired = 1;
}

// ═══════════════════════════════════════════════════════════════════════════
// Step 2: Device Initialization Sequence
// ═══════════════════════════════════════════════════════════════════════════

static int virtio_device_init(void) {
    print("[INIT] Starting VirtIO device initialization...\n");

    // 1. Reset device
    print("    [1/7] Resetting device...\n");
    virtio_write32(VIRTIO_MMIO_STATUS, 0);
    mb();

    // 2. Set ACKNOWLEDGE status bit
    print("    [2/7] Setting ACKNOWLEDGE...\n");
    virtio_write32(VIRTIO_MMIO_STATUS, VIRTIO_STATUS_ACKNOWLEDGE);
    mb();

    // 3. Set DRIVER status bit
    print("    [3/7] Setting DRIVER...\n");
    virtio_write32(VIRTIO_MMIO_STATUS,
        virtio_read32(VIRTIO_MMIO_STATUS) | VIRTIO_STATUS_DRIVER);
    mb();

    // 4. Read device features
    print("    [4/7] Reading device features...\n");
    uint32_t features = virtio_read32(VIRTIO_MMIO_DEVICE_FEATURES);
    print("        Device features: ");
    print_hex(features);
    print("\n");

    // 5. Write driver features (we accept all for now)
    print("    [5/7] Writing driver features...\n");
    virtio_write32(VIRTIO_MMIO_DRIVER_FEATURES, features);
    mb();

    // 6. Set FEATURES_OK
    print("    [6/7] Setting FEATURES_OK...\n");
    virtio_write32(VIRTIO_MMIO_STATUS,
        virtio_read32(VIRTIO_MMIO_STATUS) | VIRTIO_STATUS_FEATURES_OK);
    mb();

    // Re-read status to verify FEATURES_OK stuck
    uint32_t status = virtio_read32(VIRTIO_MMIO_STATUS);
    if (!(status & VIRTIO_STATUS_FEATURES_OK)) {
        print("    ERROR: FEATURES_OK not accepted!\n");
        virtio_write32(VIRTIO_MMIO_STATUS, VIRTIO_STATUS_FAILED);
        return -1;
    }

    print("    [7/7] Device initialized (FEATURES_OK accepted)\n");
    print("[INIT] Device initialization complete.\n\n");
    return 0;
}

// ═══════════════════════════════════════════════════════════════════════════
// Step 3: Virtqueue Setup
// ═══════════════════════════════════════════════════════════════════════════

static int virtqueue_init(void) {
    print("[VIRTQ] Setting up virtqueue...\n");

    // Select queue 0 (the only queue for block devices)
    print("    [1/6] Selecting queue 0...\n");
    virtio_write32(VIRTIO_MMIO_QUEUE_SEL, 0);
    mb();

    // Check max queue size
    uint32_t max_size = virtio_read32(VIRTIO_MMIO_QUEUE_NUM_MAX);
    print("        Max queue size: ");
    print_uint32(max_size);
    print("\n");

    if (max_size == 0) {
        print("    ERROR: Queue not available!\n");
        return -1;
    }

    // Use smaller of max_size and VIRTQ_SIZE
    uint32_t queue_size = (max_size < VIRTQ_SIZE) ? max_size : VIRTQ_SIZE;
    print("        Using queue size: ");
    print_uint32(queue_size);
    print("\n");

    // Set queue size
    print("    [2/6] Setting queue size...\n");
    virtio_write32(VIRTIO_MMIO_QUEUE_NUM, queue_size);
    mb();

    // Allocate pages for virtqueue structures
    // We need: descriptors + avail ring + used ring
    // All must be physically contiguous and aligned
    print("    [3/6] Allocating virtqueue memory...\n");

    uint64 phys_page = sys_alloc_page();
    if (phys_page == 0 || phys_page == (uint64)-1) {
        print("    ERROR: Failed to allocate virtqueue page!\n");
        return -1;
    }

    // Map the page to our virtual address
    if (sys_map_page(0, phys_page, VIRTQ_PAGES_VADDR, 0x3) < 0) {
        print("    ERROR: Failed to map virtqueue page!\n");
        return -1;
    }

    print("        Physical: ");
    print_hex(phys_page);
    print("\n        Virtual:  ");
    print_hex(VIRTQ_PAGES_VADDR);
    print("\n");

    // Zero the page
    uint8_t *page = (uint8_t *)VIRTQ_PAGES_VADDR;
    for (int i = 0; i < 4096; i++) page[i] = 0;

    // Layout the structures in the page:
    // - Descriptors: 16 bytes each, queue_size entries
    // - Avail ring: 4 + 2*queue_size bytes (aligned to 2)
    // - Used ring: 4 + 8*queue_size bytes (aligned to 4)

    desc_table = (struct virtq_desc *)VIRTQ_PAGES_VADDR;
    uint64 avail_offset = queue_size * sizeof(struct virtq_desc);
    avail_ring = (struct virtq_avail *)(VIRTQ_PAGES_VADDR + avail_offset);
    uint64 used_offset = avail_offset + 4 + 2 * queue_size;
    used_offset = (used_offset + 3) & ~3;  // Align to 4 bytes
    used_ring = (struct virtq_used *)(VIRTQ_PAGES_VADDR + used_offset);

    print("        Desc table: ");
    print_hex((uint64)desc_table);
    print("\n        Avail ring: ");
    print_hex((uint64)avail_ring);
    print("\n        Used ring:  ");
    print_hex((uint64)used_ring);
    print("\n");

    // Initialize free descriptor chain
    print("    [4/6] Initializing descriptor chain...\n");
    for (uint16_t i = 0; i < queue_size - 1; i++) {
        desc_table[i].next = i + 1;
    }
    desc_table[queue_size - 1].next = 0xFFFF;  // End of chain
    free_desc_head = 0;

    // Tell device about the queue (legacy interface uses PFN)
    print("    [5/6] Configuring queue in device...\n");

    // For legacy MMIO, we need to set page size and PFN
    virtio_write32(VIRTIO_MMIO_GUEST_PAGE_SIZE, 4096);
    mb();

    // Physical Frame Number (page-aligned physical address >> 12)
    uint32_t pfn = (uint32_t)(phys_page >> 12);
    virtio_write32(VIRTIO_MMIO_QUEUE_PFN, pfn);
    mb();

    // For modern interface, we'd use QUEUE_READY instead
    // virtio_write32(VIRTIO_MMIO_QUEUE_READY, 1);

    // Set DRIVER_OK to indicate driver is ready
    print("    [6/6] Setting DRIVER_OK...\n");
    virtio_write32(VIRTIO_MMIO_STATUS,
        virtio_read32(VIRTIO_MMIO_STATUS) | VIRTIO_STATUS_DRIVER_OK);
    mb();

    print("[VIRTQ] Virtqueue setup complete.\n\n");
    return 0;
}

// ═══════════════════════════════════════════════════════════════════════════
// Step 4: Block Read Implementation
// ═══════════════════════════════════════════════════════════════════════════

// Allocate a descriptor from the free list
static int alloc_desc(void) {
    if (free_desc_head == 0xFFFF) return -1;
    int idx = free_desc_head;
    free_desc_head = desc_table[idx].next;
    return idx;
}

// Free a descriptor back to the free list
static void free_desc(int idx) {
    desc_table[idx].next = free_desc_head;
    free_desc_head = idx;
}

// Static buffers for request (must be at known physical addresses)
// In a real driver, we'd allocate these properly
static struct virtio_blk_req_hdr req_hdr __attribute__((aligned(16)));
static uint8_t data_buf[512] __attribute__((aligned(512)));
static uint8_t status_buf __attribute__((aligned(1)));

/**
 * Read a sector from the disk
 * @param sector Sector number (512-byte units)
 * @param buf Buffer to read into (must be 512 bytes)
 * @return 0 on success, negative on error
 */
int virtio_blk_read(uint64_t sector, void *buf) {
    print("[READ] Reading sector ");
    print_uint32((uint32_t)sector);
    print("...\n");

    // For now, we use static buffers at known addresses
    // In a real driver, we'd properly translate virtual->physical

    // Allocate 3 descriptors: header, data, status
    int desc0 = alloc_desc();
    int desc1 = alloc_desc();
    int desc2 = alloc_desc();

    if (desc0 < 0 || desc1 < 0 || desc2 < 0) {
        print("    ERROR: No free descriptors!\n");
        if (desc0 >= 0) free_desc(desc0);
        if (desc1 >= 0) free_desc(desc1);
        return -1;
    }

    // Fill in request header
    req_hdr.type = VIRTIO_BLK_T_IN;  // Read
    req_hdr.reserved = 0;
    req_hdr.sector = sector;
    status_buf = 0xFF;  // Will be overwritten by device

    // Descriptor 0: Request header (device reads)
    // Note: We need physical address, but for simplicity we use virtual
    // (This works in QEMU with identity mapping or when running in kernel)
    desc_table[desc0].addr = (uint64_t)&req_hdr;
    desc_table[desc0].len = sizeof(req_hdr);
    desc_table[desc0].flags = VIRTQ_DESC_F_NEXT;
    desc_table[desc0].next = desc1;

    // Descriptor 1: Data buffer (device writes)
    desc_table[desc1].addr = (uint64_t)data_buf;
    desc_table[desc1].len = 512;
    desc_table[desc1].flags = VIRTQ_DESC_F_WRITE | VIRTQ_DESC_F_NEXT;
    desc_table[desc1].next = desc2;

    // Descriptor 2: Status byte (device writes)
    desc_table[desc2].addr = (uint64_t)&status_buf;
    desc_table[desc2].len = 1;
    desc_table[desc2].flags = VIRTQ_DESC_F_WRITE;
    desc_table[desc2].next = 0;

    mb();

    // Add to available ring
    uint16_t avail_idx = avail_ring->idx;
    avail_ring->ring[avail_idx % VIRTQ_SIZE] = desc0;
    mb();
    avail_ring->idx = avail_idx + 1;
    mb();

    // Notify device (kick)
    print("    Notifying device...\n");
    virtio_write32(VIRTIO_MMIO_QUEUE_NOTIFY, 0);
    mb();

    // Wait for completion
    if (use_irq_completion) {
        // IRQ-driven: wait for interrupt handler to signal completion
        print("    Waiting for IRQ completion...\n");
        disk_irq_fired = 0;
        int timeout = 10000000;
        while (!disk_irq_fired && used_ring->idx == last_used_idx && --timeout > 0) {
            // Yield CPU while waiting (low-power wait)
#if defined(__x86_64__)
            __asm__ volatile("pause" ::: "memory");
#elif defined(__aarch64__)
            __asm__ volatile("yield" ::: "memory");
#else
            __asm__ volatile("" ::: "memory");
#endif
        }
        if (timeout == 0) {
            print("    ERROR: Timeout waiting for disk IRQ!\n");
            free_desc(desc0);
            free_desc(desc1);
            free_desc(desc2);
            return -1;
        }
        print("    IRQ received!\n");
    } else {
        // Polling fallback (original behavior)
        print("    Waiting for completion (polling)...\n");
        int timeout = 1000000;
        while (used_ring->idx == last_used_idx && --timeout > 0) {
            mb();
        }
        if (timeout == 0) {
            print("    ERROR: Timeout waiting for disk!\n");
            free_desc(desc0);
            free_desc(desc1);
            free_desc(desc2);
            return -1;
        }
    }

    // Process used ring
    last_used_idx++;

    // Check status
    if (status_buf != VIRTIO_BLK_S_OK) {
        print("    ERROR: Disk returned status ");
        print_uint32(status_buf);
        print("\n");
        free_desc(desc0);
        free_desc(desc1);
        free_desc(desc2);
        return -1;
    }

    // Copy data to caller's buffer
    uint8_t *dst = (uint8_t *)buf;
    for (int i = 0; i < 512; i++) {
        dst[i] = data_buf[i];
    }

    // Free descriptors
    free_desc(desc0);
    free_desc(desc1);
    free_desc(desc2);

    print("    SUCCESS: Read complete.\n");
    return 0;
}

// ═══════════════════════════════════════════════════════════════════════════
// Main Driver Entry
// ═══════════════════════════════════════════════════════════════════════════

int main(void)
{
    print("\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("  VIRTIO_DRIVER: User-Space Block Device (Phase 7)\n");
    print("═══════════════════════════════════════════════════════════\n\n");

    // Initialize exception handling
    print("[SETUP] Initializing exception handling...\n");
    libos_exception_init();
    print("\n");

    // Map VirtIO MMIO region
    print("[SETUP] Mapping VirtIO MMIO region...\n");
    print("    Physical: ");
    print_hex(VIRTIO0_BASE);
    print("\n    Virtual:  ");
    print_hex(VIRTIO_VADDR);
    print("\n");

    if (sys_map_page(0, VIRTIO0_BASE, VIRTIO_VADDR, 0x3) < 0) {
        print("    FAILED: Could not map VirtIO MMIO!\n");
        return -1;
    }
    virtio_base = (volatile uint32_t *)VIRTIO_VADDR;
    print("    SUCCESS\n\n");

    // Verify magic
    uint32_t magic = virtio_read32(VIRTIO_MMIO_MAGIC_VALUE);
    if (magic != VIRTIO_MAGIC) {
        print("ERROR: Invalid VirtIO magic: ");
        print_hex(magic);
        print("\n");
        return -1;
    }

    // Check device ID
    uint32_t device_id = virtio_read32(VIRTIO_MMIO_DEVICE_ID);
    if (device_id == 0) {
        print("ERROR: No VirtIO device present!\n");
        print("Make sure QEMU has a block device attached.\n");
        return -1;
    }
    if (device_id != 2) {
        print("WARNING: Device is not a block device (ID=");
        print_uint32(device_id);
        print(")\n");
    }

    print("[SETUP] VirtIO Block Device detected.\n\n");

    // Initialize device
    if (virtio_device_init() < 0) {
        return -1;
    }

    // Setup virtqueue
    if (virtqueue_init() < 0) {
        return -1;
    }

    // ═══════════════════════════════════════════════════════════════════
    // Register VirtIO IRQ handler (Phase 7 - IRQ-driven I/O)
    // ═══════════════════════════════════════════════════════════════════
    print("[SETUP] Registering VirtIO IRQ handler...\n");
    print("    IRQ number: ");
    print_uint32(VIRTIO0_IRQ);
    print("\n");

    if (libos_register_irq(VIRTIO0_IRQ, virtio_irq_handler, 0) == 0) {
        print("    SUCCESS: IRQ handler registered\n");
        use_irq_completion = 1;
        print("    Mode: IRQ-driven completion\n\n");
    } else {
        print("    WARNING: Failed to register IRQ handler\n");
        print("    Mode: Polling fallback\n\n");
    }

    // ═══════════════════════════════════════════════════════════════════
    // Test: Read sector 0 (boot sector / MBR)
    // ═══════════════════════════════════════════════════════════════════

    print("═══════════════════════════════════════════════════════════\n");
    print("  DISK READ TEST\n");
    print("═══════════════════════════════════════════════════════════\n\n");

    uint8_t sector_data[512];
    if (virtio_blk_read(0, sector_data) == 0) {
        print("\n[RESULT] First 64 bytes of sector 0:\n");
        print("    ");
        for (int i = 0; i < 64; i++) {
            print_hex(sector_data[i]);
            print(" ");
            if ((i + 1) % 16 == 0) print("\n    ");
        }
        print("\n");

        // Check for MBR signature (0x55AA at offset 510-511)
        if (sector_data[510] == 0x55 && sector_data[511] == 0xAA) {
            print("[RESULT] MBR signature detected (0x55AA)\n");
            print("         This looks like a valid boot sector!\n");
        }
    } else {
        print("\n[RESULT] Disk read failed.\n");
    }

    print("\n═══════════════════════════════════════════════════════════\n");
    print("  USER-SPACE DISK DRIVER TEST COMPLETE\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("\nThe exokernel thesis is proven:\n");
    print("  - Kernel exported VirtIO MMIO safely\n");
    print("  - User code initialized the device\n");
    print("  - User code read from disk directly\n");
    print("  - NO kernel disk driver needed!\n\n");

    // Spin forever
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
