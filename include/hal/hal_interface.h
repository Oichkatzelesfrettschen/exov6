/* HAL Interface Definition - Hardware Abstraction Layer
 * Pure C17 implementation for hardware-agnostic operations
 */

#ifndef HAL_INTERFACE_H
#define HAL_INTERFACE_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

/* HAL Version and Capabilities */
#define HAL_VERSION_MAJOR 1
#define HAL_VERSION_MINOR 0
#define HAL_VERSION_PATCH 0

/* Architecture Detection */
#if defined(__x86_64__) || defined(_M_X64)
    #define HAL_ARCH_X86_64 1
    #define HAL_ARCH_NAME "x86_64"
#elif defined(__aarch64__) || defined(_M_ARM64)
    #define HAL_ARCH_AARCH64 1
    #define HAL_ARCH_NAME "aarch64"
#elif defined(__riscv) && (__riscv_xlen == 64)
    #define HAL_ARCH_RISCV64 1
    #define HAL_ARCH_NAME "riscv64"
#else
    #error "Unsupported architecture"
#endif

/* HAL Capability Flags */
typedef enum {
    HAL_CAP_SMP         = (1 << 0),  /* Symmetric multiprocessing */
    HAL_CAP_NUMA        = (1 << 1),  /* Non-uniform memory access */
    HAL_CAP_IOMMU       = (1 << 2),  /* I/O Memory Management Unit */
    HAL_CAP_CRYPTO      = (1 << 3),  /* Hardware cryptographic acceleration */
    HAL_CAP_VIRT        = (1 << 4),  /* Hardware virtualization */
    HAL_CAP_ATOMIC64    = (1 << 5),  /* 64-bit atomic operations */
    HAL_CAP_SIMD        = (1 << 6),  /* SIMD instruction support */
    HAL_CAP_PREFETCH    = (1 << 7),  /* Memory prefetch instructions */
} hal_capability_t;

/* Memory Management Interface */
typedef struct {
    void* (*alloc_pages)(size_t pages, uint32_t flags);
    void  (*free_pages)(void* addr, size_t pages);
    bool  (*map_pages)(void* virt, uint64_t phys, size_t pages, uint32_t flags);
    void  (*unmap_pages)(void* virt, size_t pages);
    void  (*flush_tlb)(void* addr, size_t size);
    void  (*invalidate_cache)(void* addr, size_t size);
} hal_memory_ops_t;

/* CPU Management Interface */
typedef struct {
    uint32_t (*get_cpu_count)(void);
    uint32_t (*get_current_cpu)(void);
    void     (*send_ipi)(uint32_t cpu, uint32_t vector);
    void     (*halt_cpu)(void);
    void     (*enable_interrupts)(void);
    void     (*disable_interrupts)(void);
    uint64_t (*read_timestamp)(void);
    void     (*cpu_relax)(void);
} hal_cpu_ops_t;

/* Interrupt Management Interface */
typedef struct {
    bool (*register_handler)(uint32_t vector, void (*handler)(void*), void* data);
    void (*unregister_handler)(uint32_t vector);
    void (*mask_interrupt)(uint32_t irq);
    void (*unmask_interrupt)(uint32_t irq);
    void (*eoi)(uint32_t vector);
} hal_interrupt_ops_t;

/* I/O Operations Interface */
typedef struct {
    uint8_t  (*inb)(uint16_t port);
    uint16_t (*inw)(uint16_t port);
    uint32_t (*inl)(uint16_t port);
    void     (*outb)(uint16_t port, uint8_t val);
    void     (*outw)(uint16_t port, uint16_t val);
    void     (*outl)(uint16_t port, uint32_t val);
    void*    (*map_io)(uint64_t phys_addr, size_t size);
    void     (*unmap_io)(void* virt_addr, size_t size);
} hal_io_ops_t;

/* Atomic Operations Interface */
typedef struct {
    uint32_t (*atomic_add32)(volatile uint32_t* ptr, uint32_t val);
    uint64_t (*atomic_add64)(volatile uint64_t* ptr, uint64_t val);
    bool     (*atomic_cas32)(volatile uint32_t* ptr, uint32_t expected, uint32_t desired);
    bool     (*atomic_cas64)(volatile uint64_t* ptr, uint64_t expected, uint64_t desired);
    void     (*memory_barrier)(void);
    void     (*read_barrier)(void);
    void     (*write_barrier)(void);
} hal_atomic_ops_t;

/* Timer Operations Interface */
typedef struct {
    uint64_t (*get_frequency)(void);
    uint64_t (*get_ticks)(void);
    void     (*set_oneshot)(uint64_t ticks, void (*callback)(void*), void* data);
    void     (*set_periodic)(uint64_t ticks, void (*callback)(void*), void* data);
    void     (*cancel_timer)(void);
} hal_timer_ops_t;

/* HAL Information Structure */
typedef struct {
    const char*           arch_name;
    uint32_t              version;
    hal_capability_t      capabilities;
    uint32_t              page_size;
    uint32_t              cache_line_size;
    uint32_t              cpu_count;
    uint64_t              memory_size;
} hal_info_t;

/* Main HAL Interface Structure */
typedef struct {
    hal_info_t            info;
    hal_memory_ops_t      memory;
    hal_cpu_ops_t         cpu;
    hal_interrupt_ops_t   interrupt;
    hal_io_ops_t          io;
    hal_atomic_ops_t      atomic;
    hal_timer_ops_t       timer;
} hal_interface_t;

/* Global HAL Interface */
extern const hal_interface_t* hal;

/* HAL Initialization */
bool hal_init(void);
void hal_shutdown(void);

/* HAL Capability Queries */
static inline bool hal_has_capability(hal_capability_t cap) {
    return (hal->info.capabilities & cap) != 0;
}

static inline const char* hal_get_arch_name(void) {
    return hal->info.arch_name;
}

static inline uint32_t hal_get_version(void) {
    return hal->info.version;
}

/* Convenience Macros for Common Operations */
#define HAL_PAGE_SIZE        (hal->info.page_size)
#define HAL_CACHE_LINE_SIZE  (hal->info.cache_line_size)
#define HAL_CPU_COUNT        (hal->info.cpu_count)
#define HAL_MEMORY_SIZE      (hal->info.memory_size)

#define hal_alloc_page()     hal->memory.alloc_pages(1, 0)
#define hal_free_page(addr)  hal->memory.free_pages(addr, 1)
#define hal_current_cpu()    hal->cpu.get_current_cpu()
#define hal_timestamp()      hal->cpu.read_timestamp()
#define hal_mb()             hal->atomic.memory_barrier()

#endif /* HAL_INTERFACE_H */