/**
 * @file cpu_flags.c
 * @brief CPU flags and control register operations
 * 
 * Pure C17 implementation of CPU flag manipulation and control register access.
 * Architecture-specific inline assembly wrapped in portable functions.
 */

#include <stdint.h>
#include <stdbool.h>
#include "types.h"

#ifdef __x86_64__

/**
 * Read RFLAGS register
 */
uint64_t read_flags(void) {
    uint64_t flags;
    __asm__ volatile(
        "pushfq\n\t"
        "popq %0"
        : "=r"(flags)
        :
        : "memory"
    );
    return flags;
}

/**
 * Write RFLAGS register
 */
void write_flags(uint64_t flags) {
    __asm__ volatile(
        "pushq %0\n\t"
        "popfq"
        :
        : "r"(flags)
        : "memory", "cc"
    );
}

/**
 * Read CR0 register
 */
uint64_t read_cr0(void) {
    uint64_t cr0;
    __asm__ volatile("movq %%cr0, %0" : "=r"(cr0));
    return cr0;
}

/**
 * Write CR0 register
 */
void write_cr0(uint64_t cr0) {
    __asm__ volatile("movq %0, %%cr0" : : "r"(cr0) : "memory");
}

/**
 * Read CR2 register (page fault address)
 */
uint64_t read_cr2(void) {
    uint64_t cr2;
    __asm__ volatile("movq %%cr2, %0" : "=r"(cr2));
    return cr2;
}

/**
 * Read CR3 register (page directory base)
 */
uint64_t read_cr3(void) {
    uint64_t cr3;
    __asm__ volatile("movq %%cr3, %0" : "=r"(cr3));
    return cr3;
}

/**
 * Write CR3 register (page directory base)
 */
void write_cr3(uint64_t cr3) {
    __asm__ volatile("movq %0, %%cr3" : : "r"(cr3) : "memory");
}

/**
 * Read CR4 register
 */
uint64_t read_cr4(void) {
    uint64_t cr4;
    __asm__ volatile("movq %%cr4, %0" : "=r"(cr4));
    return cr4;
}

/**
 * Write CR4 register
 */
void write_cr4(uint64_t cr4) {
    __asm__ volatile("movq %0, %%cr4" : : "r"(cr4) : "memory");
}

/**
 * Read Model Specific Register (MSR)
 */
uint64_t read_msr(uint32_t msr) {
    uint32_t low, high;
    __asm__ volatile("rdmsr" : "=a"(low), "=d"(high) : "c"(msr));
    return ((uint64_t)high << 32) | low;
}

/**
 * Write Model Specific Register (MSR)
 */
void write_msr(uint32_t msr, uint64_t value) {
    uint32_t low = value & 0xFFFFFFFF;
    uint32_t high = value >> 32;
    __asm__ volatile("wrmsr" : : "c"(msr), "a"(low), "d"(high) : "memory");
}

/**
 * CPU identification
 */
void cpuid(uint32_t leaf, uint32_t *eax, uint32_t *ebx, uint32_t *ecx, uint32_t *edx) {
    __asm__ volatile(
        "cpuid"
        : "=a"(*eax), "=b"(*ebx), "=c"(*ecx), "=d"(*edx)
        : "a"(leaf)
    );
}

/**
 * Extended CPUID
 */
void cpuid_ex(uint32_t leaf, uint32_t subleaf, 
              uint32_t *eax, uint32_t *ebx, uint32_t *ecx, uint32_t *edx) {
    __asm__ volatile(
        "cpuid"
        : "=a"(*eax), "=b"(*ebx), "=c"(*ecx), "=d"(*edx)
        : "a"(leaf), "c"(subleaf)
    );
}

/**
 * Pause instruction for spin loops
 */
void cpu_pause(void) {
    __asm__ volatile("pause" : : : "memory");
}

/**
 * Memory fence
 */
void cpu_mfence(void) {
    __asm__ volatile("mfence" : : : "memory");
}

/**
 * Load fence
 */
void cpu_lfence(void) {
    __asm__ volatile("lfence" : : : "memory");
}

/**
 * Store fence
 */
void cpu_sfence(void) {
    __asm__ volatile("sfence" : : : "memory");
}

/**
 * Flush cache line
 */
void cpu_clflush(void *addr) {
    __asm__ volatile("clflush (%0)" : : "r"(addr) : "memory");
}

/**
 * Invalidate page in TLB
 */
void cpu_invlpg(void *addr) {
    __asm__ volatile("invlpg (%0)" : : "r"(addr) : "memory");
}

/**
 * Halt CPU
 */
void cpu_halt(void) {
    __asm__ volatile("hlt" : : : "memory");
}

/**
 * No operation
 */
void cpu_nop(void) {
    __asm__ volatile("nop");
}

/**
 * Read Time Stamp Counter
 */
uint64_t read_tsc(void) {
    uint32_t low, high;
    __asm__ volatile("rdtsc" : "=a"(low), "=d"(high));
    return ((uint64_t)high << 32) | low;
}

/**
 * Read Time Stamp Counter and Processor ID
 */
uint64_t read_tscp(uint32_t *cpu_id) {
    uint32_t low, high, aux;
    __asm__ volatile("rdtscp" : "=a"(low), "=d"(high), "=c"(aux));
    if (cpu_id) {
        *cpu_id = aux;
    }
    return ((uint64_t)high << 32) | low;
}

#elif defined(__i386__)

/**
 * Read EFLAGS register (32-bit)
 */
uint32_t read_flags(void) {
    uint32_t flags;
    __asm__ volatile(
        "pushfl\n\t"
        "popl %0"
        : "=r"(flags)
        :
        : "memory"
    );
    return flags;
}

/**
 * Write EFLAGS register (32-bit)
 */
void write_flags(uint32_t flags) {
    __asm__ volatile(
        "pushl %0\n\t"
        "popfl"
        :
        : "r"(flags)
        : "memory", "cc"
    );
}

// Similar implementations for 32-bit...

#elif defined(__aarch64__)

/**
 * Read processor state (ARM64)
 */
uint64_t read_flags(void) {
    uint64_t daif;
    __asm__ volatile("mrs %0, DAIF" : "=r"(daif));
    return daif;
}

/**
 * Write processor state (ARM64)
 */
void write_flags(uint64_t flags) {
    __asm__ volatile("msr DAIF, %0" : : "r"(flags) : "memory");
}

/**
 * Data synchronization barrier
 */
void cpu_dsb(void) {
    __asm__ volatile("dsb sy" : : : "memory");
}

/**
 * Data memory barrier
 */
void cpu_dmb(void) {
    __asm__ volatile("dmb sy" : : : "memory");
}

/**
 * Instruction synchronization barrier
 */
void cpu_isb(void) {
    __asm__ volatile("isb" : : : "memory");
}

/**
 * Wait for interrupt
 */
void cpu_wfi(void) {
    __asm__ volatile("wfi" : : : "memory");
}

/**
 * Wait for event
 */
void cpu_wfe(void) {
    __asm__ volatile("wfe" : : : "memory");
}

/**
 * Send event
 */
void cpu_sev(void) {
    __asm__ volatile("sev" : : : "memory");
}

#else

// Generic stubs for unsupported architectures
uint64_t read_flags(void) { return 0; }
void write_flags(uint64_t flags) { (void)flags; }
void cpu_halt(void) { while(1); }
void cpu_pause(void) { }
void cpu_nop(void) { }

#endif

/**
 * Check if interrupts are enabled
 */
bool interrupts_enabled(void) {
#ifdef __x86_64__
    return (read_flags() & 0x200) != 0; // IF flag is bit 9
#elif defined(__i386__)
    return (read_flags() & 0x200) != 0;
#elif defined(__aarch64__)
    return (read_flags() & 0x80) == 0; // I bit, inverted logic
#else
    return false;
#endif
}

/**
 * Enable interrupts
 */
void enable_interrupts(void) {
#ifdef __x86_64__
    __asm__ volatile("sti" : : : "memory");
#elif defined(__i386__)
    __asm__ volatile("sti" : : : "memory");
#elif defined(__aarch64__)
    __asm__ volatile("msr DAIFClr, #2" : : : "memory");
#endif
}

/**
 * Disable interrupts
 */
void disable_interrupts(void) {
#ifdef __x86_64__
    __asm__ volatile("cli" : : : "memory");
#elif defined(__i386__)
    __asm__ volatile("cli" : : : "memory");
#elif defined(__aarch64__)
    __asm__ volatile("msr DAIFSet, #2" : : : "memory");
#endif
}

/**
 * Save interrupt state and disable
 */
uint64_t save_and_disable_interrupts(void) {
    uint64_t flags = read_flags();
    disable_interrupts();
    return flags;
}

/**
 * Restore interrupt state
 */
void restore_interrupts(uint64_t flags) {
    if (interrupts_enabled()) {
        enable_interrupts();
    }
}

// Export initialization
void cpu_flags_init(void) {
    // Any initialization if needed
}