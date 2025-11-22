/*
 * arch_ops.c - x86_64 Architecture Operations Implementation
 */

#include <hal/arch_ops.h>
#include <stdatomic.h>
#include <stdint.h>

// Structure definition matching arch_switch.S
struct arch_context {
    // Register array mapping (offsets 0-127):
    // [0]=RAX, [1]=RBX, [2]=RCX, [3]=RDX, [4]=RSI, [5]=RDI, [6]=RBP, [7]=RSP,
    // [8]=R8, [9]=R9, [10]=R10, [11]=R11, [12]=R12, [13]=R13, [14]=R14, [15]=R15
    uint64_t registers[16];
    uint64_t sp;            // 128: saved stack pointer for switching
    uint64_t pc;            // 136: return address
    uint64_t flags;         // 144: RFLAGS
};

// ----------------------------------------------------------------------------
// Interrupt Control
// ----------------------------------------------------------------------------

void arch_irq_enter(void) {
    // Placeholder for IRQ accounting
}

void arch_irq_exit(void) {
    // Placeholder for IRQ accounting
}

void arch_irq_enable(void) {
    __asm__ volatile("sti" ::: "memory");
}

void arch_irq_disable(void) {
    __asm__ volatile("cli" ::: "memory");
}

bool arch_irq_enabled(void) {
    uint64_t flags;
    __asm__ volatile(
        "pushfq\n\t"
        "popq %0"
        : "=r"(flags)
        :
        : "memory"
    );
    return (flags & (1 << 9)) != 0; // IF flag is bit 9
}

// arch_switch_to is implemented in arch_switch.S

// ----------------------------------------------------------------------------
// TLB Management
// ----------------------------------------------------------------------------

void arch_tlb_flush_all(void) {
    uint64_t cr3;
    __asm__ volatile (
        "mov %%cr3, %0\n\t"
        "mov %0, %%cr3"
        : "=r"(cr3)
        :
        : "memory"
    );
}

void arch_tlb_flush_range(void* start, size_t size) {
    uintptr_t addr = (uintptr_t)start;
    uintptr_t end = addr + size;

    // Align down to page boundary
    addr &= ~(4096UL - 1);

    for (; addr < end; addr += 4096) {
        __asm__ volatile ("invlpg (%0)" : : "r"(addr) : "memory");
    }
}

void arch_tlb_flush_page(void* addr) {
    __asm__ volatile ("invlpg (%0)" : : "r"(addr) : "memory");
}

// ----------------------------------------------------------------------------
// Timekeeping
// ----------------------------------------------------------------------------

uint64_t arch_get_cycles(void) {
    uint32_t lo, hi;
    __asm__ volatile ("rdtsc" : "=a"(lo), "=d"(hi));
    return ((uint64_t)hi << 32) | lo;
}

// ----------------------------------------------------------------------------
// Memory Barriers
// ----------------------------------------------------------------------------

void arch_barrier_full(void) {
    __asm__ volatile ("mfence" ::: "memory");
}

void arch_barrier_read(void) {
    __asm__ volatile ("lfence" ::: "memory");
}

void arch_barrier_write(void) {
    __asm__ volatile ("sfence" ::: "memory");
}

// ----------------------------------------------------------------------------
// CPU Management
// ----------------------------------------------------------------------------

uint32_t arch_cpu_id(void) {
    uint32_t ebx;
    uint32_t unused;
    // CPUID leaf 1 returns APIC ID in EBX[31:24]
    __asm__ volatile (
        "cpuid"
        : "=a"(unused), "=b"(ebx), "=c"(unused), "=d"(unused)
        : "a"(1)
        : "memory"
    );
    return ebx >> 24;
}

void arch_cpu_relax(void) {
    __asm__ volatile ("pause" ::: "memory");
}

void arch_cpu_halt(void) {
    __asm__ volatile ("hlt");
}
