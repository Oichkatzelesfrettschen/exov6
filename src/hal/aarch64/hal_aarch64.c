/* AArch64 HAL Implementation
 * Hardware Abstraction Layer for ARM64 architecture
 * Pure C17 implementation with modern ARMv8 features
 */

#include <hal/hal_interface.h>
#include <stdatomic.h>
#include <stdbool.h>

/* AArch64 specific includes */
#include <arch/aarch64/cpu.h>
#include <arch/aarch64/mmu.h>
#include <arch/aarch64/gic.h>

/* AArch64 Memory Management Implementation */
static void* aarch64_alloc_pages(size_t pages, uint32_t flags) {
    return arch_alloc_pages(pages, flags);
}

static void aarch64_free_pages(void* addr, size_t pages) {
    arch_free_pages(addr, pages);
}

static bool aarch64_map_pages(void* virt, uint64_t phys, size_t pages, uint32_t flags) {
    return arch_map_pages(virt, phys, pages, flags);
}

static void aarch64_unmap_pages(void* virt, size_t pages) {
    arch_unmap_pages(virt, pages);
}

static void aarch64_flush_tlb(void* addr, size_t size) {
    if (addr == NULL) {
        /* Flush entire TLB */
        __asm__ volatile ("tlbi vmalle1is; dsb sy; isb" ::: "memory");
    } else {
        /* Flush specific pages */
        for (size_t i = 0; i < size; i += 4096) {
            uint64_t va = (uint64_t)((char*)addr + i) >> 12;
            __asm__ volatile ("tlbi vae1is, %0; dsb sy; isb" :: "r"(va) : "memory");
        }
    }
}

static void aarch64_invalidate_cache(void* addr, size_t size) {
    for (size_t i = 0; i < size; i += 64) {
        __asm__ volatile ("dc civac, %0" :: "r"((char*)addr + i) : "memory");
    }
    __asm__ volatile ("dsb sy" ::: "memory");
}

/* AArch64 CPU Management Implementation */
static uint32_t aarch64_get_cpu_count(void) {
    return arch_get_cpu_count();
}

static uint32_t aarch64_get_current_cpu(void) {
    uint64_t mpidr;
    __asm__ volatile ("mrs %0, mpidr_el1" : "=r"(mpidr));
    return (uint32_t)(mpidr & 0xFF);
}

static void aarch64_send_ipi(uint32_t cpu, uint32_t vector) {
    arch_send_ipi(cpu, vector);
}

static void aarch64_halt_cpu(void) {
    __asm__ volatile ("wfi");
}

static void aarch64_enable_interrupts(void) {
    __asm__ volatile ("msr daifclr, #2" ::: "memory");
}

static void aarch64_disable_interrupts(void) {
    __asm__ volatile ("msr daifset, #2" ::: "memory");
}

static uint64_t aarch64_read_timestamp(void) {
    uint64_t val;
    __asm__ volatile ("mrs %0, cntvct_el0" : "=r"(val));
    return val;
}

static void aarch64_cpu_relax(void) {
    __asm__ volatile ("yield" ::: "memory");
}

/* AArch64 Interrupt Management Implementation */
static bool aarch64_register_handler(uint32_t vector, void (*handler)(void*), void* data) {
    return arch_register_interrupt_handler(vector, handler, data);
}

static void aarch64_unregister_handler(uint32_t vector) {
    arch_unregister_interrupt_handler(vector);
}

static void aarch64_mask_interrupt(uint32_t irq) {
    arch_mask_interrupt(irq);
}

static void aarch64_unmask_interrupt(uint32_t irq) {
    arch_unmask_interrupt(irq);
}

static void aarch64_eoi(uint32_t vector) {
    arch_send_eoi(vector);
}

/* AArch64 I/O Operations Implementation (MMIO-based) */
static uint8_t aarch64_inb(uint16_t port) {
    /* AArch64 doesn't have port I/O, use MMIO mapping */
    volatile uint8_t* addr = arch_get_io_base() + port;
    return *addr;
}

static uint16_t aarch64_inw(uint16_t port) {
    volatile uint16_t* addr = (volatile uint16_t*)(arch_get_io_base() + port);
    return *addr;
}

static uint32_t aarch64_inl(uint16_t port) {
    volatile uint32_t* addr = (volatile uint32_t*)(arch_get_io_base() + port);
    return *addr;
}

static void aarch64_outb(uint16_t port, uint8_t val) {
    volatile uint8_t* addr = arch_get_io_base() + port;
    *addr = val;
}

static void aarch64_outw(uint16_t port, uint16_t val) {
    volatile uint16_t* addr = (volatile uint16_t*)(arch_get_io_base() + port);
    *addr = val;
}

static void aarch64_outl(uint16_t port, uint32_t val) {
    volatile uint32_t* addr = (volatile uint32_t*)(arch_get_io_base() + port);
    *addr = val;
}

static void* aarch64_map_io(uint64_t phys_addr, size_t size) {
    return arch_map_io_memory(phys_addr, size);
}

static void aarch64_unmap_io(void* virt_addr, size_t size) {
    arch_unmap_io_memory(virt_addr, size);
}

/* AArch64 Atomic Operations Implementation */
static uint32_t aarch64_atomic_add32(volatile uint32_t* ptr, uint32_t val) {
    return atomic_fetch_add((atomic_uint_least32_t*)ptr, val);
}

static uint64_t aarch64_atomic_add64(volatile uint64_t* ptr, uint64_t val) {
    return atomic_fetch_add((atomic_uint_least64_t*)ptr, val);
}

static bool aarch64_atomic_cas32(volatile uint32_t* ptr, uint32_t expected, uint32_t desired) {
    return atomic_compare_exchange_strong((atomic_uint_least32_t*)ptr, &expected, desired);
}

static bool aarch64_atomic_cas64(volatile uint64_t* ptr, uint64_t expected, uint64_t desired) {
    return atomic_compare_exchange_strong((atomic_uint_least64_t*)ptr, &expected, desired);
}

static void aarch64_memory_barrier(void) {
    __asm__ volatile ("dmb sy" ::: "memory");
}

static void aarch64_read_barrier(void) {
    __asm__ volatile ("dmb ld" ::: "memory");
}

static void aarch64_write_barrier(void) {
    __asm__ volatile ("dmb st" ::: "memory");
}

/* AArch64 Timer Operations Implementation */
static uint64_t aarch64_get_frequency(void) {
    uint64_t freq;
    __asm__ volatile ("mrs %0, cntfrq_el0" : "=r"(freq));
    return freq;
}

static uint64_t aarch64_get_ticks(void) {
    return aarch64_read_timestamp();
}

static void aarch64_set_oneshot(uint64_t ticks, void (*callback)(void*), void* data) {
    arch_set_oneshot_timer(ticks, callback, data);
}

static void aarch64_set_periodic(uint64_t ticks, void (*callback)(void*), void* data) {
    arch_set_periodic_timer(ticks, callback, data);
}

static void aarch64_cancel_timer(void) {
    arch_cancel_timer();
}

/* AArch64 HAL Interface Definition */
static const hal_interface_t aarch64_hal = {
    .info = {
        .arch_name = HAL_ARCH_NAME,
        .version = (HAL_VERSION_MAJOR << 16) | (HAL_VERSION_MINOR << 8) | HAL_VERSION_PATCH,
        .capabilities = HAL_CAP_SMP | HAL_CAP_NUMA | HAL_CAP_IOMMU | HAL_CAP_CRYPTO |
                       HAL_CAP_VIRT | HAL_CAP_ATOMIC64 | HAL_CAP_SIMD | HAL_CAP_PREFETCH,
        .page_size = 4096,
        .cache_line_size = 64,
        .cpu_count = 0,  /* Will be detected at runtime */
        .memory_size = 0, /* Will be detected at runtime */
    },
    .memory = {
        .alloc_pages = aarch64_alloc_pages,
        .free_pages = aarch64_free_pages,
        .map_pages = aarch64_map_pages,
        .unmap_pages = aarch64_unmap_pages,
        .flush_tlb = aarch64_flush_tlb,
        .invalidate_cache = aarch64_invalidate_cache,
    },
    .cpu = {
        .get_cpu_count = aarch64_get_cpu_count,
        .get_current_cpu = aarch64_get_current_cpu,
        .send_ipi = aarch64_send_ipi,
        .halt_cpu = aarch64_halt_cpu,
        .enable_interrupts = aarch64_enable_interrupts,
        .disable_interrupts = aarch64_disable_interrupts,
        .read_timestamp = aarch64_read_timestamp,
        .cpu_relax = aarch64_cpu_relax,
    },
    .interrupt = {
        .register_handler = aarch64_register_handler,
        .unregister_handler = aarch64_unregister_handler,
        .mask_interrupt = aarch64_mask_interrupt,
        .unmask_interrupt = aarch64_unmask_interrupt,
        .eoi = aarch64_eoi,
    },
    .io = {
        .inb = aarch64_inb,
        .inw = aarch64_inw,
        .inl = aarch64_inl,
        .outb = aarch64_outb,
        .outw = aarch64_outw,
        .outl = aarch64_outl,
        .map_io = aarch64_map_io,
        .unmap_io = aarch64_unmap_io,
    },
    .atomic = {
        .atomic_add32 = aarch64_atomic_add32,
        .atomic_add64 = aarch64_atomic_add64,
        .atomic_cas32 = aarch64_atomic_cas32,
        .atomic_cas64 = aarch64_atomic_cas64,
        .memory_barrier = aarch64_memory_barrier,
        .read_barrier = aarch64_read_barrier,
        .write_barrier = aarch64_write_barrier,
    },
    .timer = {
        .get_frequency = aarch64_get_frequency,
        .get_ticks = aarch64_get_ticks,
        .set_oneshot = aarch64_set_oneshot,
        .set_periodic = aarch64_set_periodic,
        .cancel_timer = aarch64_cancel_timer,
    },
};

/* Global HAL Interface Pointer */
const hal_interface_t* hal = &aarch64_hal;

/* HAL Initialization */
bool hal_init(void) {
    /* Initialize AArch64 specific components */
    if (!arch_init_cpu()) {
        return false;
    }
    
    if (!arch_init_memory()) {
        return false;
    }
    
    if (!arch_init_interrupts()) {
        return false;
    }
    
    /* Update runtime information */
    ((hal_interface_t*)hal)->info.cpu_count = aarch64_get_cpu_count();
    ((hal_interface_t*)hal)->info.memory_size = arch_get_memory_size();
    
    return true;
}

void hal_shutdown(void) {
    arch_shutdown_interrupts();
    arch_shutdown_memory();
    arch_shutdown_cpu();
}