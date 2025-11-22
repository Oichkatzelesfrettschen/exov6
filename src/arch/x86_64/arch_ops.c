/*
 * arch_ops.c - x86_64 Architecture Operations Implementation
 * POSIX-ish / Exokernel Low-Level Primitives
 */

#include <hal/arch_ops.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

// ----------------------------------------------------------------------------
// Context Management
// ----------------------------------------------------------------------------

/*
 * struct arch_context
 * Matches layout in arch_switch.S.
 * Only Callee-Saved registers are preserved.
 */
struct arch_context {
    uint64_t rbx;    // 0
    uint64_t rbp;    // 8
    uint64_t r12;    // 16
    uint64_t r13;    // 24
    uint64_t r14;    // 32
    uint64_t r15;    // 40
    uint64_t sp;     // 48 (RSP)
    uint64_t pc;     // 56 (RIP/Return Address)
    uint64_t flags;  // 64 (RFLAGS)
};

/*
 * Initialize a context for a new thread.
 * Sets up the stack so that 'arch_switch_to' can 'return' into the entry point.
 */
void arch_context_init(struct arch_context *ctx, void *stack_top, void (*entry)(void)) {
    // 1. Align stack to 16 bytes (ABI requirement)
    uintptr_t sp = (uintptr_t)stack_top;
    sp &= ~0xF; 
    
    // 2. Set instruction pointer to entry function
    ctx->pc = (uint64_t)entry;
    
    // 3. Set stack pointer
    // Note: When arch_switch_to performs 'ret', it pops RIP. 
    // We simulate the stack state as if 'entry' was called.
    ctx->sp = sp;

    // 4. Default RFLAGS: Interrupts enabled (IF=1), Reserved bit 1 must be 1
    ctx->flags = (1 << 9) | (1 << 1); 

    // 5. Clear callee-saved registers (optional, but good for debugging)
    ctx->rbx = 0;
    ctx->rbp = 0; // RBP 0 often indicates end of stack frame to debuggers
    ctx->r12 = 0;
    ctx->r13 = 0;
    ctx->r14 = 0;
    ctx->r15 = 0;
}

// arch_switch_to is implemented in arch_switch.S

// ----------------------------------------------------------------------------
// Interrupt Control
// ----------------------------------------------------------------------------

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

// ----------------------------------------------------------------------------
// TLB & Paging Management
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

void arch_tlb_flush_page(void* addr) {
    __asm__ volatile ("invlpg (%0)" : : "r"(addr) : "memory");
}

void arch_tlb_flush_range(void* start, size_t size) {
    // Heuristic: If flushing a large range, it's cheaper to flush the whole TLB
    // than to issue hundreds of invlpg instructions.
    // Threshold is typically around 32-64 pages depending on CPU uArch.
    const size_t THRESHOLD = 64 * 4096; 

    if (size > THRESHOLD) {
        arch_tlb_flush_all();
        return;
    }

    uintptr_t addr = (uintptr_t)start;
    uintptr_t end = addr + size;

    // Align down to page boundary
    addr &= ~(4096UL - 1);

    for (; addr < end; addr += 4096) {
        __asm__ volatile ("invlpg (%0)" : : "r"(addr) : "memory");
    }
}

uint64_t arch_read_cr2(void) {
    uint64_t cr2;
    __asm__ volatile ("mov %%cr2, %0" : "=r"(cr2));
    return cr2;
}

// ----------------------------------------------------------------------------
// Port I/O (Elevated Feature)
// ----------------------------------------------------------------------------

void arch_outb(uint16_t port, uint8_t val) {
    __asm__ volatile ("outb %0, %1" : : "a"(val), "Nd"(port));
}

uint8_t arch_inb(uint16_t port) {
    uint8_t val;
    __asm__ volatile ("inb %1, %0" : "=a"(val) : "Nd"(port));
    return val;
}

void arch_outl(uint16_t port, uint32_t val) {
    __asm__ volatile ("outl %0, %1" : : "a"(val), "Nd"(port));
}

uint32_t arch_inl(uint16_t port) {
    uint32_t val;
    __asm__ volatile ("inl %1, %0" : "=a"(val) : "Nd"(port));
    return val;
}

// ----------------------------------------------------------------------------
// MSR Access (Elevated Feature)
// ----------------------------------------------------------------------------

void arch_wrmsr(uint32_t msr, uint64_t val) {
    uint32_t lo = val & 0xFFFFFFFF;
    uint32_t hi = val >> 32;
    __asm__ volatile ("wrmsr" : : "c"(msr), "a"(lo), "d"(hi));
}

uint64_t arch_rdmsr(uint32_t msr) {
    uint32_t lo, hi;
    __asm__ volatile ("rdmsr" : "=a"(lo), "=d"(hi) : "c"(msr));
    return ((uint64_t)hi << 32) | lo;
}

// ----------------------------------------------------------------------------
// Timekeeping
// ----------------------------------------------------------------------------

uint64_t arch_get_cycles(void) {
    uint32_t lo, hi;
    // Use RDTSCP instead of RDTSC to prevent out-of-order execution 
    // from skewing timing measurements.
    // RCX is clobbered by RDTSCP (contains IA32_TSC_AUX).
    __asm__ volatile ("rdtscp" : "=a"(lo), "=d"(hi) : : "rcx", "memory");
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
    // Optimization: If the OS has set up IA32_TSC_AUX MSR (C000_0103h),
    // RDTSCP returns the CPU ID in ECX much faster than CPUID instruction.
    // However, as a fallback/default, we use CPUID leaf 1.
    
    uint32_t eax_out, ebx, ecx_out, edx_out;
    
    // CPUID leaf 1 returns APIC ID in EBX[31:24]
    __asm__ volatile (
        "cpuid"
        : "=a"(eax_out), "=b"(ebx), "=c"(ecx_out), "=d"(edx_out)
        : "a"(1)
        : "memory"
    );
    return ebx >> 24;
}

void arch_cpu_relax(void) {
    __asm__ volatile ("pause" ::: "memory");
}

void arch_cpu_halt(void) {
    // Enable interrupts before halting so we can wake up
    __asm__ volatile ("sti; hlt");
}