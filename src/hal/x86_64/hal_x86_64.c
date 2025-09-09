/* x86_64 HAL Implementation
 * Hardware Abstraction Layer for x86_64 architecture
 * Pure C17 implementation with modern x86_64 features
 */

#include <hal/hal_interface.h>
#include <stdatomic.h>
#include <stdbool.h>

/* x86_64 specific includes */
#include <arch/x86_64/cpu.h>
#include <arch/x86_64/mmu.h>
#include <arch/x86_64/interrupt.h>

/* x86_64 Memory Management Implementation */
static void* x86_64_alloc_pages(size_t pages, uint32_t flags) {
    return arch_alloc_pages(pages, flags);
}

static void x86_64_free_pages(void* addr, size_t pages) {
    arch_free_pages(addr, pages);
}

static bool x86_64_map_pages(void* virt, uint64_t phys, size_t pages, uint32_t flags) {
    return arch_map_pages(virt, phys, pages, flags);
}

static void x86_64_unmap_pages(void* virt, size_t pages) {
    arch_unmap_pages(virt, pages);
}

static void x86_64_flush_tlb(void* addr, size_t size) {
    if (addr == NULL) {
        /* Flush entire TLB */
        __asm__ volatile ("mov %%cr3, %%rax; mov %%rax, %%cr3" ::: "rax", "memory");
    } else {
        /* Flush specific pages */
        for (size_t i = 0; i < size; i += 4096) {
            __asm__ volatile ("invlpg (%0)" :: "r"((char*)addr + i) : "memory");
        }
    }
}

static void x86_64_invalidate_cache(void* addr, size_t size) {
    for (size_t i = 0; i < size; i += 64) {
        __asm__ volatile ("clflush (%0)" :: "r"((char*)addr + i) : "memory");
    }
    __asm__ volatile ("mfence" ::: "memory");
}

/* x86_64 CPU Management Implementation */
static uint32_t x86_64_get_cpu_count(void) {
    return arch_get_cpu_count();
}

static uint32_t x86_64_get_current_cpu(void) {
    uint32_t apic_id;
    __asm__ volatile ("mov $1, %%eax; cpuid; shrl $24, %%ebx" 
                     : "=b"(apic_id) :: "eax", "ecx", "edx");
    return apic_id;
}

static void x86_64_send_ipi(uint32_t cpu, uint32_t vector) {
    arch_send_ipi(cpu, vector);
}

static void x86_64_halt_cpu(void) {
    __asm__ volatile ("hlt");
}

static void x86_64_enable_interrupts(void) {
    __asm__ volatile ("sti");
}

static void x86_64_disable_interrupts(void) {
    __asm__ volatile ("cli");
}

static uint64_t x86_64_read_timestamp(void) {
    uint32_t lo, hi;
    __asm__ volatile ("rdtsc" : "=a"(lo), "=d"(hi));
    return ((uint64_t)hi << 32) | lo;
}

static void x86_64_cpu_relax(void) {
    __asm__ volatile ("pause" ::: "memory");
}

/* x86_64 Interrupt Management Implementation */
static bool x86_64_register_handler(uint32_t vector, void (*handler)(void*), void* data) {
    return arch_register_interrupt_handler(vector, handler, data);
}

static void x86_64_unregister_handler(uint32_t vector) {
    arch_unregister_interrupt_handler(vector);
}

static void x86_64_mask_interrupt(uint32_t irq) {
    arch_mask_interrupt(irq);
}

static void x86_64_unmask_interrupt(uint32_t irq) {
    arch_unmask_interrupt(irq);
}

static void x86_64_eoi(uint32_t vector) {
    arch_send_eoi(vector);
}

/* x86_64 I/O Operations Implementation */
static uint8_t x86_64_inb(uint16_t port) {
    uint8_t val;
    __asm__ volatile ("inb %1, %0" : "=a"(val) : "Nd"(port));
    return val;
}

static uint16_t x86_64_inw(uint16_t port) {
    uint16_t val;
    __asm__ volatile ("inw %1, %0" : "=a"(val) : "Nd"(port));
    return val;
}

static uint32_t x86_64_inl(uint16_t port) {
    uint32_t val;
    __asm__ volatile ("inl %1, %0" : "=a"(val) : "Nd"(port));
    return val;
}

static void x86_64_outb(uint16_t port, uint8_t val) {
    __asm__ volatile ("outb %0, %1" :: "a"(val), "Nd"(port));
}

static void x86_64_outw(uint16_t port, uint16_t val) {
    __asm__ volatile ("outw %0, %1" :: "a"(val), "Nd"(port));
}

static void x86_64_outl(uint16_t port, uint32_t val) {
    __asm__ volatile ("outl %0, %1" :: "a"(val), "Nd"(port));
}

static void* x86_64_map_io(uint64_t phys_addr, size_t size) {
    return arch_map_io_memory(phys_addr, size);
}

static void x86_64_unmap_io(void* virt_addr, size_t size) {
    arch_unmap_io_memory(virt_addr, size);
}

/* x86_64 Atomic Operations Implementation */
static uint32_t x86_64_atomic_add32(volatile uint32_t* ptr, uint32_t val) {
    return atomic_fetch_add((atomic_uint_least32_t*)ptr, val);
}

static uint64_t x86_64_atomic_add64(volatile uint64_t* ptr, uint64_t val) {
    return atomic_fetch_add((atomic_uint_least64_t*)ptr, val);
}

static bool x86_64_atomic_cas32(volatile uint32_t* ptr, uint32_t expected, uint32_t desired) {
    return atomic_compare_exchange_strong((atomic_uint_least32_t*)ptr, &expected, desired);
}

static bool x86_64_atomic_cas64(volatile uint64_t* ptr, uint64_t expected, uint64_t desired) {
    return atomic_compare_exchange_strong((atomic_uint_least64_t*)ptr, &expected, desired);
}

static void x86_64_memory_barrier(void) {
    __asm__ volatile ("mfence" ::: "memory");
}

static void x86_64_read_barrier(void) {
    __asm__ volatile ("lfence" ::: "memory");
}

static void x86_64_write_barrier(void) {
    __asm__ volatile ("sfence" ::: "memory");
}

/* x86_64 Timer Operations Implementation */
static uint64_t x86_64_get_frequency(void) {
    return arch_get_timer_frequency();
}

static uint64_t x86_64_get_ticks(void) {
    return x86_64_read_timestamp();
}

static void x86_64_set_oneshot(uint64_t ticks, void (*callback)(void*), void* data) {
    arch_set_oneshot_timer(ticks, callback, data);
}

static void x86_64_set_periodic(uint64_t ticks, void (*callback)(void*), void* data) {
    arch_set_periodic_timer(ticks, callback, data);
}

static void x86_64_cancel_timer(void) {
    arch_cancel_timer();
}

/* x86_64 HAL Interface Definition */
static const hal_interface_t x86_64_hal = {
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
        .alloc_pages = x86_64_alloc_pages,
        .free_pages = x86_64_free_pages,
        .map_pages = x86_64_map_pages,
        .unmap_pages = x86_64_unmap_pages,
        .flush_tlb = x86_64_flush_tlb,
        .invalidate_cache = x86_64_invalidate_cache,
    },
    .cpu = {
        .get_cpu_count = x86_64_get_cpu_count,
        .get_current_cpu = x86_64_get_current_cpu,
        .send_ipi = x86_64_send_ipi,
        .halt_cpu = x86_64_halt_cpu,
        .enable_interrupts = x86_64_enable_interrupts,
        .disable_interrupts = x86_64_disable_interrupts,
        .read_timestamp = x86_64_read_timestamp,
        .cpu_relax = x86_64_cpu_relax,
    },
    .interrupt = {
        .register_handler = x86_64_register_handler,
        .unregister_handler = x86_64_unregister_handler,
        .mask_interrupt = x86_64_mask_interrupt,
        .unmask_interrupt = x86_64_unmask_interrupt,
        .eoi = x86_64_eoi,
    },
    .io = {
        .inb = x86_64_inb,
        .inw = x86_64_inw,
        .inl = x86_64_inl,
        .outb = x86_64_outb,
        .outw = x86_64_outw,
        .outl = x86_64_outl,
        .map_io = x86_64_map_io,
        .unmap_io = x86_64_unmap_io,
    },
    .atomic = {
        .atomic_add32 = x86_64_atomic_add32,
        .atomic_add64 = x86_64_atomic_add64,
        .atomic_cas32 = x86_64_atomic_cas32,
        .atomic_cas64 = x86_64_atomic_cas64,
        .memory_barrier = x86_64_memory_barrier,
        .read_barrier = x86_64_read_barrier,
        .write_barrier = x86_64_write_barrier,
    },
    .timer = {
        .get_frequency = x86_64_get_frequency,
        .get_ticks = x86_64_get_ticks,
        .set_oneshot = x86_64_set_oneshot,
        .set_periodic = x86_64_set_periodic,
        .cancel_timer = x86_64_cancel_timer,
    },
};

/* Global HAL Interface Pointer */
const hal_interface_t* hal = &x86_64_hal;

/* HAL Initialization */
bool hal_init(void) {
    /* Initialize x86_64 specific components */
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
    ((hal_interface_t*)hal)->info.cpu_count = x86_64_get_cpu_count();
    ((hal_interface_t*)hal)->info.memory_size = arch_get_memory_size();
    
    return true;
}

void hal_shutdown(void) {
    arch_shutdown_interrupts();
    arch_shutdown_memory();
    arch_shutdown_cpu();
}