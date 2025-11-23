/**
 * @file virtio.c
 * @brief User-Space VirtIO Block Driver Library (Phase 8)
 *
 * Extracted from user/virtio_driver.c for use as a library component.
 * Provides block-level I/O for the file system layer.
 */

#include "virtio.h"
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
extern void libos_exception_init(void);

// IRQ registration
typedef void (*irq_handler_t)(int irq, void *arg);
extern int libos_register_irq(int irq, irq_handler_t handler, void *arg);

// ═══════════════════════════════════════════════════════════════════════════
// VirtIO Driver State
// ═══════════════════════════════════════════════════════════════════════════

#define VIRTIO_VADDR        0x40000000ULL
#define VIRTQ_PAGES_VADDR   0x41000000ULL

static volatile uint32_t *virtio_base = 0;
static struct virtq_desc *desc_table = 0;
static struct virtq_avail *avail_ring = 0;
static struct virtq_used *used_ring = 0;
static uint16_t free_desc_head = 0;
static uint16_t last_used_idx = 0;

static volatile int disk_irq_fired = 0;
static int use_irq_completion = 0;
static int driver_initialized = 0;

// ═══════════════════════════════════════════════════════════════════════════
// Helper Functions
// ═══════════════════════════════════════════════════════════════════════════

static inline uint32_t virtio_read32(uint32_t offset) {
    return virtio_base[offset / 4];
}

static inline void virtio_write32(uint32_t offset, uint32_t val) {
    virtio_base[offset / 4] = val;
}

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
// IRQ Handler
// ═══════════════════════════════════════════════════════════════════════════

static void virtio_irq_handler(int irq, void *arg) {
    (void)arg;
    (void)irq;
    uint32_t status = virtio_read32(VIRTIO_MMIO_INTERRUPT_STATUS);
    virtio_write32(VIRTIO_MMIO_INTERRUPT_ACK, status);
    mb();
    disk_irq_fired = 1;
}

// ═══════════════════════════════════════════════════════════════════════════
// Device Initialization
// ═══════════════════════════════════════════════════════════════════════════

static int virtio_device_init(void) {
    // Reset
    virtio_write32(VIRTIO_MMIO_STATUS, 0);
    mb();

    // Acknowledge
    virtio_write32(VIRTIO_MMIO_STATUS, VIRTIO_STATUS_ACKNOWLEDGE);
    mb();

    // Driver
    virtio_write32(VIRTIO_MMIO_STATUS,
        virtio_read32(VIRTIO_MMIO_STATUS) | VIRTIO_STATUS_DRIVER);
    mb();

    // Features
    uint32_t features = virtio_read32(VIRTIO_MMIO_DEVICE_FEATURES);
    virtio_write32(VIRTIO_MMIO_DRIVER_FEATURES, features);
    mb();

    // Features OK
    virtio_write32(VIRTIO_MMIO_STATUS,
        virtio_read32(VIRTIO_MMIO_STATUS) | VIRTIO_STATUS_FEATURES_OK);
    mb();

    if (!(virtio_read32(VIRTIO_MMIO_STATUS) & VIRTIO_STATUS_FEATURES_OK)) {
        virtio_write32(VIRTIO_MMIO_STATUS, VIRTIO_STATUS_FAILED);
        return -1;
    }

    return 0;
}

static int virtqueue_init(void) {
    virtio_write32(VIRTIO_MMIO_QUEUE_SEL, 0);
    mb();

    uint32_t max_size = virtio_read32(VIRTIO_MMIO_QUEUE_NUM_MAX);
    if (max_size == 0) return -1;

    uint32_t queue_size = (max_size < VIRTQ_SIZE) ? max_size : VIRTQ_SIZE;
    virtio_write32(VIRTIO_MMIO_QUEUE_NUM, queue_size);
    mb();

    uint64 phys_page = sys_alloc_page();
    if (phys_page == 0 || phys_page == (uint64)-1) return -1;

    if (sys_map_page(0, phys_page, VIRTQ_PAGES_VADDR, 0x3) < 0) return -1;

    // Zero the page
    uint8_t *page = (uint8_t *)VIRTQ_PAGES_VADDR;
    for (int i = 0; i < 4096; i++) page[i] = 0;

    // Layout structures
    desc_table = (struct virtq_desc *)VIRTQ_PAGES_VADDR;
    uint64 avail_offset = queue_size * sizeof(struct virtq_desc);
    avail_ring = (struct virtq_avail *)(VIRTQ_PAGES_VADDR + avail_offset);
    uint64 used_offset = avail_offset + 4 + 2 * queue_size;
    used_offset = (used_offset + 3) & ~3;
    used_ring = (struct virtq_used *)(VIRTQ_PAGES_VADDR + used_offset);

    // Init free chain
    for (uint16_t i = 0; i < queue_size - 1; i++) {
        desc_table[i].next = i + 1;
    }
    desc_table[queue_size - 1].next = 0xFFFF;
    free_desc_head = 0;

    // Configure device
    virtio_write32(VIRTIO_MMIO_GUEST_PAGE_SIZE, 4096);
    mb();
    virtio_write32(VIRTIO_MMIO_QUEUE_PFN, (uint32_t)(phys_page >> 12));
    mb();

    // Driver OK
    virtio_write32(VIRTIO_MMIO_STATUS,
        virtio_read32(VIRTIO_MMIO_STATUS) | VIRTIO_STATUS_DRIVER_OK);
    mb();

    return 0;
}

// ═══════════════════════════════════════════════════════════════════════════
// Descriptor Management
// ═══════════════════════════════════════════════════════════════════════════

static int alloc_desc(void) {
    if (free_desc_head == 0xFFFF) return -1;
    int idx = free_desc_head;
    free_desc_head = desc_table[idx].next;
    return idx;
}

static void free_desc(int idx) {
    desc_table[idx].next = free_desc_head;
    free_desc_head = idx;
}

// ═══════════════════════════════════════════════════════════════════════════
// Block I/O (Static Buffers)
// ═══════════════════════════════════════════════════════════════════════════

static struct virtio_blk_req_hdr req_hdr __attribute__((aligned(16)));
static uint8_t sector_buf[512] __attribute__((aligned(512)));
static uint8_t status_buf __attribute__((aligned(1)));

static int do_disk_io(uint64_t sector, void *buf, int is_write) {
    if (!driver_initialized) return -1;

    int desc0 = alloc_desc();
    int desc1 = alloc_desc();
    int desc2 = alloc_desc();

    if (desc0 < 0 || desc1 < 0 || desc2 < 0) {
        if (desc0 >= 0) free_desc(desc0);
        if (desc1 >= 0) free_desc(desc1);
        return -1;
    }

    req_hdr.type = is_write ? VIRTIO_BLK_T_OUT : VIRTIO_BLK_T_IN;
    req_hdr.reserved = 0;
    req_hdr.sector = sector;
    status_buf = 0xFF;

    // If writing, copy data to sector_buf first
    if (is_write) {
        uint8_t *src = (uint8_t *)buf;
        for (int i = 0; i < 512; i++) sector_buf[i] = src[i];
    }

    // Descriptor 0: Header
    desc_table[desc0].addr = (uint64_t)&req_hdr;
    desc_table[desc0].len = sizeof(req_hdr);
    desc_table[desc0].flags = VIRTQ_DESC_F_NEXT;
    desc_table[desc0].next = desc1;

    // Descriptor 1: Data
    desc_table[desc1].addr = (uint64_t)sector_buf;
    desc_table[desc1].len = 512;
    desc_table[desc1].flags = (is_write ? 0 : VIRTQ_DESC_F_WRITE) | VIRTQ_DESC_F_NEXT;
    desc_table[desc1].next = desc2;

    // Descriptor 2: Status
    desc_table[desc2].addr = (uint64_t)&status_buf;
    desc_table[desc2].len = 1;
    desc_table[desc2].flags = VIRTQ_DESC_F_WRITE;
    desc_table[desc2].next = 0;

    mb();

    // Submit
    uint16_t avail_idx = avail_ring->idx;
    avail_ring->ring[avail_idx % VIRTQ_SIZE] = desc0;
    mb();
    avail_ring->idx = avail_idx + 1;
    mb();

    // Notify
    virtio_write32(VIRTIO_MMIO_QUEUE_NOTIFY, 0);
    mb();

    // Wait for completion
    if (use_irq_completion) {
        disk_irq_fired = 0;
        int timeout = 10000000;
        while (!disk_irq_fired && used_ring->idx == last_used_idx && --timeout > 0) {
#if defined(__x86_64__)
            __asm__ volatile("pause" ::: "memory");
#elif defined(__aarch64__)
            __asm__ volatile("yield" ::: "memory");
#else
            __asm__ volatile("" ::: "memory");
#endif
        }
        if (timeout == 0) {
            free_desc(desc0); free_desc(desc1); free_desc(desc2);
            return -1;
        }
    } else {
        int timeout = 1000000;
        while (used_ring->idx == last_used_idx && --timeout > 0) mb();
        if (timeout == 0) {
            free_desc(desc0); free_desc(desc1); free_desc(desc2);
            return -1;
        }
    }

    last_used_idx++;

    if (status_buf != VIRTIO_BLK_S_OK) {
        free_desc(desc0); free_desc(desc1); free_desc(desc2);
        return -1;
    }

    // If reading, copy data out
    if (!is_write) {
        uint8_t *dst = (uint8_t *)buf;
        for (int i = 0; i < 512; i++) dst[i] = sector_buf[i];
    }

    free_desc(desc0); free_desc(desc1); free_desc(desc2);
    return 0;
}

// ═══════════════════════════════════════════════════════════════════════════
// Public API
// ═══════════════════════════════════════════════════════════════════════════

int virtio_init(void) {
    if (driver_initialized) return 0;

    print("[VIRTIO] Initializing VirtIO block driver...\n");

    // Map MMIO
    if (sys_map_page(0, VIRTIO0_BASE, VIRTIO_VADDR, 0x3) < 0) {
        print("[VIRTIO] ERROR: Could not map MMIO!\n");
        return -1;
    }
    virtio_base = (volatile uint32_t *)VIRTIO_VADDR;

    // Verify magic
    uint32_t magic = virtio_read32(VIRTIO_MMIO_MAGIC_VALUE);
    if (magic != VIRTIO_MAGIC) {
        print("[VIRTIO] ERROR: Invalid magic!\n");
        return -1;
    }

    // Check device
    uint32_t device_id = virtio_read32(VIRTIO_MMIO_DEVICE_ID);
    if (device_id == 0) {
        print("[VIRTIO] ERROR: No device present!\n");
        return -1;
    }
    if (device_id != 2) {
        print("[VIRTIO] WARNING: Not a block device!\n");
    }

    // Initialize device
    if (virtio_device_init() < 0) {
        print("[VIRTIO] ERROR: Device init failed!\n");
        return -1;
    }

    // Setup virtqueue
    if (virtqueue_init() < 0) {
        print("[VIRTIO] ERROR: Virtqueue init failed!\n");
        return -1;
    }

    // Register IRQ
    if (libos_register_irq(VIRTIO0_IRQ, virtio_irq_handler, 0) == 0) {
        use_irq_completion = 1;
        print("[VIRTIO] IRQ-driven mode enabled\n");
    } else {
        print("[VIRTIO] Polling mode (IRQ failed)\n");
    }

    driver_initialized = 1;
    print("[VIRTIO] Driver ready.\n");
    return 0;
}

int virtio_is_ready(void) {
    return driver_initialized;
}

int virtio_read_sector(uint64_t sector, void *buf) {
    return do_disk_io(sector, buf, 0);
}

int virtio_write_sector(uint64_t sector, const void *buf) {
    return do_disk_io(sector, (void *)buf, 1);
}

int virtio_read_block(uint32_t blockno, void *buf) {
    // FS block = 1024 bytes = 2 sectors
    uint64_t sector = (uint64_t)blockno * 2;
    uint8_t *dst = (uint8_t *)buf;

    if (virtio_read_sector(sector, dst) < 0) return -1;
    if (virtio_read_sector(sector + 1, dst + 512) < 0) return -1;

    return 0;
}

int virtio_write_block(uint32_t blockno, const void *buf) {
    uint64_t sector = (uint64_t)blockno * 2;
    const uint8_t *src = (const uint8_t *)buf;

    if (virtio_write_sector(sector, src) < 0) return -1;
    if (virtio_write_sector(sector + 1, src + 512) < 0) return -1;

    return 0;
}
