/*
 * hal.h - Unified C17 Hardware Abstraction Layer
 * 
 * Complete platform abstraction for x86_64 and AArch64
 * Pure C17 implementation with minimal assembly intrinsics
 * 
 * This HAL provides:
 * - CPU operations (context switch, interrupts, cache)
 * - Memory management (paging, TLB, barriers)
 * - I/O operations (port I/O, MMIO)
 * - Timer and clock operations
 * - Atomic operations (via stdatomic.h)
 */

#ifndef _HAL_H
#define _HAL_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdatomic.h>

/* Platform detection */
#if defined(__x86_64__)
    #define HAL_ARCH_X86_64 1
    #define HAL_ARCH_NAME "x86_64"
#elif defined(__aarch64__)
    #define HAL_ARCH_AARCH64 1
    #define HAL_ARCH_NAME "aarch64"
#else
    #error "Unsupported architecture"
#endif

/* ============================================================================
 * CPU Operations Interface
 * ============================================================================ */

typedef struct hal_cpu_context {
    _Alignas(64) uint64_t registers[32];  /* General purpose registers */
    uint64_t pc;                          /* Program counter */
    uint64_t sp;                          /* Stack pointer */
    uint64_t flags;                       /* CPU flags */
    uint64_t fp_state[64];                /* Floating point state */
} hal_cpu_context_t;

/* Static assertion for context alignment */
_Static_assert(sizeof(hal_cpu_context_t) % 64 == 0, "CPU context must be cache-aligned");

typedef struct hal_cpu_ops {
    /* Context switching */
    void (*context_save)(hal_cpu_context_t *ctx);
    void (*context_restore)(const hal_cpu_context_t *ctx);
    void (*context_switch)(hal_cpu_context_t *from, hal_cpu_context_t *to);
    
    /* Interrupt management */
    bool (*interrupts_enabled)(void);
    void (*interrupts_enable)(void);
    void (*interrupts_disable)(void);
    uint64_t (*interrupts_save)(void);
    void (*interrupts_restore)(uint64_t flags);
    
    /* CPU identification */
    uint32_t (*get_cpu_id)(void);
    uint32_t (*get_cpu_count)(void);
    void (*get_cpu_info)(char *buffer, size_t size);
    
    /* Cache operations */
    void (*cache_flush)(void *addr, size_t size);
    void (*cache_invalidate)(void *addr, size_t size);
    void (*cache_flush_all)(void);
    
    /* CPU control */
    void (*cpu_pause)(void);
    void (*cpu_halt)(void);
    void (*cpu_reset)(void);
    
    /* Time stamp counter */
    uint64_t (*read_timestamp)(void);
    uint64_t (*timestamp_frequency)(void);
} hal_cpu_ops_t;

/* ============================================================================
 * Memory Operations Interface
 * ============================================================================ */

/* Page size definitions */
#define HAL_PAGE_SIZE_4K    (4096UL)
#define HAL_PAGE_SIZE_2M    (2UL * 1024 * 1024)
#define HAL_PAGE_SIZE_1G    (1UL * 1024 * 1024 * 1024)

/* Page flags */
typedef enum {
    HAL_PAGE_PRESENT    = (1 << 0),
    HAL_PAGE_WRITABLE   = (1 << 1),
    HAL_PAGE_USER       = (1 << 2),
    HAL_PAGE_WRITE_THROUGH = (1 << 3),
    HAL_PAGE_CACHE_DISABLE = (1 << 4),
    HAL_PAGE_ACCESSED   = (1 << 5),
    HAL_PAGE_DIRTY      = (1 << 6),
    HAL_PAGE_HUGE       = (1 << 7),
    HAL_PAGE_GLOBAL     = (1 << 8),
    HAL_PAGE_NO_EXECUTE = (1 << 63)
} hal_page_flags_t;

typedef struct hal_memory_ops {
    /* Page table operations */
    void* (*page_table_create)(void);
    void (*page_table_destroy)(void *pt);
    int (*page_map)(void *pt, uint64_t vaddr, uint64_t paddr, 
                    size_t size, hal_page_flags_t flags);
    int (*page_unmap)(void *pt, uint64_t vaddr, size_t size);
    uint64_t (*page_translate)(void *pt, uint64_t vaddr);
    
    /* TLB operations */
    void (*tlb_flush_page)(uint64_t vaddr);
    void (*tlb_flush_range)(uint64_t start, uint64_t end);
    void (*tlb_flush_all)(void);
    
    /* Memory barriers */
    void (*memory_barrier)(void);
    void (*read_barrier)(void);
    void (*write_barrier)(void);
    
    /* Physical memory */
    uint64_t (*get_memory_size)(void);
    void (*get_memory_map)(void *buffer, size_t *size);
} hal_memory_ops_t;

/* ============================================================================
 * I/O Operations Interface
 * ============================================================================ */

typedef struct hal_io_ops {
    /* Port I/O (x86_64 specific) */
    uint8_t (*inb)(uint16_t port);
    uint16_t (*inw)(uint16_t port);
    uint32_t (*inl)(uint16_t port);
    void (*outb)(uint16_t port, uint8_t value);
    void (*outw)(uint16_t port, uint16_t value);
    void (*outl)(uint16_t port, uint32_t value);
    
    /* Memory-mapped I/O */
    uint8_t (*mmio_read8)(volatile void *addr);
    uint16_t (*mmio_read16)(volatile void *addr);
    uint32_t (*mmio_read32)(volatile void *addr);
    uint64_t (*mmio_read64)(volatile void *addr);
    void (*mmio_write8)(volatile void *addr, uint8_t value);
    void (*mmio_write16)(volatile void *addr, uint16_t value);
    void (*mmio_write32)(volatile void *addr, uint32_t value);
    void (*mmio_write64)(volatile void *addr, uint64_t value);
    
    /* DMA operations */
    void* (*dma_alloc)(size_t size, uint64_t *phys_addr);
    void (*dma_free)(void *addr, size_t size);
    void (*dma_sync)(void *addr, size_t size, int direction);
} hal_io_ops_t;

/* ============================================================================
 * Timer Operations Interface
 * ============================================================================ */

typedef struct hal_timer_ops {
    /* Timer initialization */
    void (*timer_init)(uint64_t frequency);
    void (*timer_start)(void);
    void (*timer_stop)(void);
    
    /* Timer queries */
    uint64_t (*timer_read)(void);
    uint64_t (*timer_frequency)(void);
    
    /* Delays */
    void (*delay_us)(uint32_t microseconds);
    void (*delay_ms)(uint32_t milliseconds);
    
    /* Periodic timer */
    void (*set_periodic)(uint64_t period_ns);
    void (*set_oneshot)(uint64_t delay_ns);
    void (*cancel)(void);
} hal_timer_ops_t;

/* ============================================================================
 * Interrupt Controller Interface
 * ============================================================================ */

typedef void (*hal_irq_handler_t)(uint32_t irq, void *data);

typedef struct hal_irq_ops {
    /* IRQ management */
    int (*irq_request)(uint32_t irq, hal_irq_handler_t handler, 
                       void *data, const char *name);
    void (*irq_free)(uint32_t irq);
    void (*irq_enable)(uint32_t irq);
    void (*irq_disable)(uint32_t irq);
    void (*irq_ack)(uint32_t irq);
    
    /* IRQ routing */
    void (*irq_set_affinity)(uint32_t irq, uint32_t cpu_mask);
    uint32_t (*irq_get_affinity)(uint32_t irq);
    
    /* Priority management */
    void (*irq_set_priority)(uint32_t irq, uint32_t priority);
    uint32_t (*irq_get_priority)(uint32_t irq);
} hal_irq_ops_t;

/* ============================================================================
 * HAL Instance Structure
 * ============================================================================ */

typedef struct hal {
    const char *name;
    const char *version;
    
    /* Operation tables */
    const hal_cpu_ops_t *cpu;
    const hal_memory_ops_t *memory;
    const hal_io_ops_t *io;
    const hal_timer_ops_t *timer;
    const hal_irq_ops_t *irq;
    
    /* Platform-specific data */
    void *platform_data;
} hal_t;

/* ============================================================================
 * Global HAL Instance
 * ============================================================================ */

extern const hal_t *hal_current;

/* ============================================================================
 * HAL Initialization
 * ============================================================================ */

/* Initialize HAL for current platform */
int hal_init(void);

/* Get HAL instance for specific platform */
const hal_t* hal_get_platform(const char *name);

/* Register platform HAL implementation */
int hal_register_platform(const hal_t *hal);

/* ============================================================================
 * Inline Helper Functions (C17)
 * ============================================================================ */

/* CPU operations helpers */
static inline void hal_cpu_pause(void) {
    if (hal_current && hal_current->cpu && hal_current->cpu->cpu_pause) {
        hal_current->cpu->cpu_pause();
    }
}

static inline uint64_t hal_read_timestamp(void) {
    if (hal_current && hal_current->cpu && hal_current->cpu->read_timestamp) {
        return hal_current->cpu->read_timestamp();
    }
    return 0;
}

static inline bool hal_interrupts_enabled(void) {
    if (hal_current && hal_current->cpu && hal_current->cpu->interrupts_enabled) {
        return hal_current->cpu->interrupts_enabled();
    }
    return false;
}

static inline void hal_interrupts_disable(void) {
    if (hal_current && hal_current->cpu && hal_current->cpu->interrupts_disable) {
        hal_current->cpu->interrupts_disable();
    }
}

static inline void hal_interrupts_enable(void) {
    if (hal_current && hal_current->cpu && hal_current->cpu->interrupts_enable) {
        hal_current->cpu->interrupts_enable();
    }
}

/* Memory barrier helpers */
static inline void hal_memory_barrier(void) {
    if (hal_current && hal_current->memory && hal_current->memory->memory_barrier) {
        hal_current->memory->memory_barrier();
    } else {
        atomic_thread_fence(memory_order_seq_cst);
    }
}

static inline void hal_read_barrier(void) {
    if (hal_current && hal_current->memory && hal_current->memory->read_barrier) {
        hal_current->memory->read_barrier();
    } else {
        atomic_thread_fence(memory_order_acquire);
    }
}

static inline void hal_write_barrier(void) {
    if (hal_current && hal_current->memory && hal_current->memory->write_barrier) {
        hal_current->memory->write_barrier();
    } else {
        atomic_thread_fence(memory_order_release);
    }
}

/* ============================================================================
 * Platform-Specific Includes
 * ============================================================================ */

#ifdef HAL_ARCH_X86_64
    #include "hal/x86_64/cpu.h"
    #include "hal/x86_64/memory.h"
    #include "hal/x86_64/io.h"
    #include "hal/x86_64/timer.h"
#endif

#ifdef HAL_ARCH_AARCH64
    #include "hal/aarch64/cpu.h"
    #include "hal/aarch64/memory.h"
    #include "hal/aarch64/io.h"
    #include "hal/aarch64/timer.h"
#endif

/* ============================================================================
 * Static Assertions
 * ============================================================================ */

_Static_assert(sizeof(void*) == 8, "64-bit architecture required");
_Static_assert(_Alignof(hal_cpu_context_t) >= 64, "CPU context must be cache-aligned");

#endif /* _HAL_H */