/**
 * @file pipe.c
 * @brief ExoV6 Pipe Implementation (Phase 11.3)
 *
 * ╔═══════════════════════════════════════════════════════════════════════════╗
 * ║  LIONS' COMMENTARY FOR THE POST-MONOLITHIC AGE                            ║
 * ║                                                                           ║
 * ║  LESSON: Pipes are a LibOS abstraction built on shared memory.            ║
 * ║                                                                           ║
 * ║  In UNIX V6, pipes are kernel objects with kernel-managed buffers.        ║
 * ║  In ExoV6, pipes are user-space ring buffers in shared memory.            ║
 * ║                                                                           ║
 * ║  The kernel provides ONLY:                                                ║
 * ║    - Page allocation (sys_page_alloc)                                     ║
 * ║    - Page mapping (sys_page_map)                                          ║
 * ║                                                                           ║
 * ║  The LibOS provides:                                                      ║
 * ║    - Ring buffer data structure                                           ║
 * ║    - Read/write synchronization                                           ║
 * ║    - EOF detection (write end closed)                                     ║
 * ║                                                                           ║
 * ║  For shell pipelines (cmd1 | cmd2):                                       ║
 * ║    1. Shell creates pipe                                                  ║
 * ║    2. Shell spawns cmd1 with stdout → pipe write end                      ║
 * ║    3. Shell spawns cmd2 with stdin → pipe read end                        ║
 * ║    4. Both processes share the pipe buffer via mapped page                ║
 * ╚═══════════════════════════════════════════════════════════════════════════╝
 */

#include <stdint.h>
#include <types.h>

/* ═══════════════════════════════════════════════════════════════════════════
 * Configuration
 * ═══════════════════════════════════════════════════════════════════════════ */

#define MAX_PIPES       8           /* Maximum concurrent pipes */
#define PIPE_BUF_SIZE   4096        /* One page per pipe */
#define PIPE_DATA_SIZE  (PIPE_BUF_SIZE - sizeof(struct pipe_header))

/* ═══════════════════════════════════════════════════════════════════════════
 * External Dependencies
 * ═══════════════════════════════════════════════════════════════════════════ */

/* Page allocation */
extern uint64 sys_page_alloc_raw(void);
extern int sys_page_map_raw(int target_env, uint64 phys, uint64 virt, int perm);

/* Synchronization - yield CPU while waiting */
extern void sys_yield(void);

/* Debug */
extern void print(const char *s);
extern void print_hex(uint64 n);

/* Permission bits */
#define PERM_R  0x1
#define PERM_W  0x2

/* ═══════════════════════════════════════════════════════════════════════════
 * Memory Barriers for SMP Safety
 *
 * LESSON: On SMP systems, CPU caches and out-of-order execution can cause
 * data races even with volatile. Memory barriers ensure ordering.
 *
 * For a single-producer single-consumer ring buffer:
 *   - Write barrier after updating data, before updating head
 *   - Read barrier after reading tail, before reading data
 * ═══════════════════════════════════════════════════════════════════════════ */

#if defined(__x86_64__)
/* x86_64 has strong memory ordering, but we still need compiler barriers */
#define memory_barrier()    __asm__ volatile("mfence" ::: "memory")
#define write_barrier()     __asm__ volatile("sfence" ::: "memory")
#define read_barrier()      __asm__ volatile("lfence" ::: "memory")
#elif defined(__aarch64__)
/* ARM64 needs explicit barriers */
#define memory_barrier()    __asm__ volatile("dmb ish" ::: "memory")
#define write_barrier()     __asm__ volatile("dmb ishst" ::: "memory")
#define read_barrier()      __asm__ volatile("dmb ishld" ::: "memory")
#else
/* Compiler barrier only - sufficient for uniprocessor */
#define memory_barrier()    __asm__ volatile("" ::: "memory")
#define write_barrier()     __asm__ volatile("" ::: "memory")
#define read_barrier()      __asm__ volatile("" ::: "memory")
#endif

/* ═══════════════════════════════════════════════════════════════════════════
 * Pipe Buffer Structure
 *
 * LESSON: This is a lock-free single-producer single-consumer ring buffer.
 * No spinlocks needed because:
 *   - Only one writer (producer)
 *   - Only one reader (consumer)
 *   - Head/tail updates are atomic on aligned 32-bit values
 * ═══════════════════════════════════════════════════════════════════════════ */

struct pipe_header {
    volatile uint32_t head;         /* Write position (producer updates) */
    volatile uint32_t tail;         /* Read position (consumer updates) */
    volatile uint32_t write_closed; /* Write end closed (EOF signal) */
    volatile uint32_t read_closed;  /* Read end closed (broken pipe) */
    uint32_t capacity;              /* Buffer capacity */
    uint32_t _pad[3];               /* Align to 32 bytes */
};

/* ═══════════════════════════════════════════════════════════════════════════
 * Pipe Table (Per-Process)
 *
 * Each pipe is a page of shared memory with the ring buffer structure.
 * ═══════════════════════════════════════════════════════════════════════════ */

struct pipe_entry {
    int in_use;
    uint64 phys_addr;               /* Physical address of pipe buffer */
    void *buffer;                   /* Virtual address (mapped) */
    int is_read_end;                /* This process has read end */
    int is_write_end;               /* This process has write end */
};

static struct pipe_entry pipe_table[MAX_PIPES];
static int pipe_initialized = 0;

/* Base virtual address for pipe buffers */
#define PIPE_VA_BASE    0x70000000ULL

/* ═══════════════════════════════════════════════════════════════════════════
 * Initialization
 * ═══════════════════════════════════════════════════════════════════════════ */

static void pipe_init(void) {
    if (pipe_initialized) return;

    for (int i = 0; i < MAX_PIPES; i++) {
        pipe_table[i].in_use = 0;
        pipe_table[i].phys_addr = 0;
        pipe_table[i].buffer = 0;
        pipe_table[i].is_read_end = 0;
        pipe_table[i].is_write_end = 0;
    }

    pipe_initialized = 1;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * pipe_create() - Create a New Pipe
 *
 * Returns pipe index, or -1 on error.
 * After creation, call pipe_get_read_fd() and pipe_get_write_fd().
 *
 * LESSON: We allocate a physical page and map it. The page contains
 * the ring buffer header followed by the data buffer.
 * ═══════════════════════════════════════════════════════════════════════════ */

int pipe_create(void) {
    pipe_init();

    /* Find free slot */
    int slot = -1;
    for (int i = 0; i < MAX_PIPES; i++) {
        if (!pipe_table[i].in_use) {
            slot = i;
            break;
        }
    }

    if (slot < 0) {
        return -1;  /* No free pipes */
    }

    /* Allocate physical page */
    uint64 pa = sys_page_alloc_raw();
    if ((int64_t)pa < 0) {
        return -1;
    }

    /* Map into our address space */
    uint64 va = PIPE_VA_BASE + (slot * PIPE_BUF_SIZE);
    if (sys_page_map_raw(0, pa, va, PERM_R | PERM_W) < 0) {
        return -1;
    }

    /* Initialize ring buffer header */
    struct pipe_header *hdr = (struct pipe_header *)va;
    hdr->head = 0;
    hdr->tail = 0;
    hdr->write_closed = 0;
    hdr->read_closed = 0;
    hdr->capacity = PIPE_DATA_SIZE;

    /* Record in table */
    pipe_table[slot].in_use = 1;
    pipe_table[slot].phys_addr = pa;
    pipe_table[slot].buffer = (void *)va;
    pipe_table[slot].is_read_end = 1;   /* Creator has both ends initially */
    pipe_table[slot].is_write_end = 1;

    return slot;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * pipe_close_read() / pipe_close_write() - Close Pipe Ends
 *
 * LESSON: When write end closes, reader gets EOF.
 * When read end closes, writer gets SIGPIPE (broken pipe).
 * ═══════════════════════════════════════════════════════════════════════════ */

void pipe_close_read(int pipe_id) {
    if (pipe_id < 0 || pipe_id >= MAX_PIPES) return;
    if (!pipe_table[pipe_id].in_use) return;

    struct pipe_header *hdr = (struct pipe_header *)pipe_table[pipe_id].buffer;
    hdr->read_closed = 1;
    pipe_table[pipe_id].is_read_end = 0;

    /* If both ends closed, free the pipe */
    if (!pipe_table[pipe_id].is_read_end && !pipe_table[pipe_id].is_write_end) {
        pipe_table[pipe_id].in_use = 0;
    }
}

void pipe_close_write(int pipe_id) {
    if (pipe_id < 0 || pipe_id >= MAX_PIPES) return;
    if (!pipe_table[pipe_id].in_use) return;

    struct pipe_header *hdr = (struct pipe_header *)pipe_table[pipe_id].buffer;
    hdr->write_closed = 1;
    pipe_table[pipe_id].is_write_end = 0;

    /* If both ends closed, free the pipe */
    if (!pipe_table[pipe_id].is_read_end && !pipe_table[pipe_id].is_write_end) {
        pipe_table[pipe_id].in_use = 0;
    }
}

/* ═══════════════════════════════════════════════════════════════════════════
 * pipe_read() - Read from Pipe
 *
 * LESSON: Blocking read from ring buffer.
 * Returns bytes read, 0 on EOF, -1 on error.
 * ═══════════════════════════════════════════════════════════════════════════ */

int pipe_read(int pipe_id, void *buf, int n) {
    if (pipe_id < 0 || pipe_id >= MAX_PIPES) return -1;
    if (!pipe_table[pipe_id].in_use) return -1;
    if (n <= 0) return 0;

    struct pipe_header *hdr = (struct pipe_header *)pipe_table[pipe_id].buffer;
    char *data = (char *)pipe_table[pipe_id].buffer + sizeof(struct pipe_header);
    char *dst = (char *)buf;

    int total = 0;

    while (total < n) {
        /* Wait for data or EOF */
        while (hdr->head == hdr->tail) {
            if (hdr->write_closed) {
                return total;  /* EOF - return what we have */
            }
            sys_yield();  /* Spin-wait with yield */
        }

        /* Read available data */
        uint32_t head = hdr->head;
        uint32_t tail = hdr->tail;
        uint32_t available = head - tail;  /* Works due to modular arithmetic */

        if (available > (uint32_t)(n - total)) {
            available = n - total;
        }

        /* Read barrier - ensure we see producer's writes */
        read_barrier();

        /* Copy from ring buffer */
        for (uint32_t i = 0; i < available; i++) {
            dst[total++] = data[(tail + i) % hdr->capacity];
        }

        /* Update tail (consumer position) with barrier */
        write_barrier();
        hdr->tail = tail + available;
    }

    return total;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * pipe_write() - Write to Pipe
 *
 * LESSON: Blocking write to ring buffer.
 * Returns bytes written, -1 on error (broken pipe).
 * ═══════════════════════════════════════════════════════════════════════════ */

int pipe_write(int pipe_id, const void *buf, int n) {
    if (pipe_id < 0 || pipe_id >= MAX_PIPES) return -1;
    if (!pipe_table[pipe_id].in_use) return -1;
    if (n <= 0) return 0;

    struct pipe_header *hdr = (struct pipe_header *)pipe_table[pipe_id].buffer;
    char *data = (char *)pipe_table[pipe_id].buffer + sizeof(struct pipe_header);
    const char *src = (const char *)buf;

    int total = 0;

    while (total < n) {
        /* Check for broken pipe */
        if (hdr->read_closed) {
            return -1;  /* EPIPE - reader closed */
        }

        /* Wait for space */
        while ((hdr->head - hdr->tail) >= hdr->capacity) {
            if (hdr->read_closed) {
                return -1;  /* EPIPE */
            }
            sys_yield();  /* Spin-wait with yield */
        }

        /* Write available space */
        uint32_t head = hdr->head;
        uint32_t tail = hdr->tail;
        uint32_t space = hdr->capacity - (head - tail);

        if (space > (uint32_t)(n - total)) {
            space = n - total;
        }

        /* Copy to ring buffer */
        for (uint32_t i = 0; i < space; i++) {
            data[(head + i) % hdr->capacity] = src[total++];
        }

        /* Write barrier - ensure data is visible before updating head */
        write_barrier();

        /* Update head (producer position) */
        hdr->head = head + space;
    }

    return total;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * pipe_get_phys() - Get Physical Address of Pipe Buffer
 *
 * Used by spawn() to map pipe into child's address space.
 * ═══════════════════════════════════════════════════════════════════════════ */

uint64 pipe_get_phys(int pipe_id) {
    if (pipe_id < 0 || pipe_id >= MAX_PIPES) return 0;
    if (!pipe_table[pipe_id].in_use) return 0;
    return pipe_table[pipe_id].phys_addr;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * PEDAGOGICAL SUMMARY
 *
 * This pipe implementation demonstrates:
 *
 * 1. SHARED MEMORY IPC:
 *    Both ends of the pipe share a physical page. The kernel just maps it;
 *    the ring buffer protocol is entirely in user space.
 *
 * 2. LOCK-FREE SYNCHRONIZATION:
 *    Single-producer single-consumer ring buffer needs no locks.
 *    Head is written by producer, tail by consumer.
 *    Both are always increasing; modular arithmetic handles wrap.
 *
 * 3. BLOCKING VIA YIELD:
 *    Without kernel-managed blocking (like UNIX pipe sleep/wakeup),
 *    we spin-yield. This is inefficient but correct.
 *    A real implementation would use futex-like kernel support.
 *
 * COMPARISON TO UNIX V6:
 *   V6 pipe: Kernel buffer, kernel sleep/wakeup, kernel copy
 *   ExoV6 pipe: User buffer, user spin-yield, user copy
 *
 * The exokernel trade-off: More flexibility, potentially less efficiency.
 * But with kernel IPC support for blocking, we could have both!
 * ═══════════════════════════════════════════════════════════════════════════ */
