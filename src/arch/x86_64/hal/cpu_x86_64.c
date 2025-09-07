/**
 * @file cpu_x86_64.c
 * @brief x86_64 implementation of HAL CPU interface
 * 
 * Pure C17 implementation for x86_64 architecture.
 */

#include "hal/cpu.h"
#include <stdatomic.h>
#include <string.h>

// x86_64 specific context structure
struct hal_context {
    uint64_t r15;
    uint64_t r14;
    uint64_t r13;
    uint64_t r12;
    uint64_t rbx;
    uint64_t rbp;
    uint64_t rip;
};

// x86_64 trap frame
struct hal_trapframe {
    // Pushed by entry code
    uint64_t r15, r14, r13, r12, r11, r10, r9, r8;
    uint64_t rdi, rsi, rbp, rbx, rdx, rcx, rax;
    
    // Interrupt number and error code
    uint64_t int_no;
    uint64_t err_code;
    
    // Pushed by CPU
    uint64_t rip;
    uint64_t cs;
    uint64_t rflags;
    uint64_t rsp;
    uint64_t ss;
};

// CPU information array
#define MAX_CPUS 256
static hal_cpu_info_t cpu_info[MAX_CPUS];
static _Atomic uint32_t cpu_count = 0;

// Per-CPU current info pointer (would use GS segment in real implementation)
static _Thread_local const hal_cpu_info_t* current_cpu_info = NULL;

int32_t hal_cpu_init(void) {
    // Initialize BSP (bootstrap processor)
    cpu_info[0] = (hal_cpu_info_t){
        .id = 0,
        .arch_id = 0,  // Would read from APIC
        .is_bsp = true,
        .online = true
    };
    
    atomic_store(&cpu_count, 1);
    current_cpu_info = &cpu_info[0];
    
    return 0;
}

const hal_cpu_info_t* hal_cpu_current(void) {
    return current_cpu_info;
}

uint32_t hal_cpu_id(void) {
    // In real implementation, would read from APIC or use GS segment
    return current_cpu_info ? current_cpu_info->id : 0;
}

void hal_context_switch(hal_context_t** old, hal_context_t* new) {
    // This would be implemented in assembly
    // For now, just a placeholder
    __asm__ volatile(
        "// Context switch placeholder\n"
        : : "D"(old), "S"(new) : "memory"
    );
}

void hal_interrupts_enable(void) {
    __asm__ volatile("sti" ::: "memory");
}

void hal_interrupts_disable(void) {
    __asm__ volatile("cli" ::: "memory");
}

uint64_t hal_interrupts_save_disable(void) {
    uint64_t flags;
    __asm__ volatile(
        "pushfq\n"
        "pop %0\n"
        "cli"
        : "=r"(flags) : : "memory"
    );
    return flags;
}

void hal_interrupts_restore(uint64_t state) {
    __asm__ volatile(
        "push %0\n"
        "popfq"
        : : "r"(state) : "memory", "cc"
    );
}

bool hal_interrupts_enabled(void) {
    uint64_t flags;
    __asm__ volatile(
        "pushfq\n"
        "pop %0"
        : "=r"(flags)
    );
    return (flags & 0x200) != 0;  // IF flag is bit 9
}

void hal_cpu_halt(void) {
    __asm__ volatile("hlt");
}

void hal_cpu_pause(void) {
    __asm__ volatile("pause" ::: "memory");
}

void hal_memory_barrier(void) {
    __asm__ volatile("mfence" ::: "memory");
}

void hal_read_barrier(void) {
    __asm__ volatile("lfence" ::: "memory");
}

void hal_write_barrier(void) {
    __asm__ volatile("sfence" ::: "memory");
}

void hal_tlb_invalidate(void* addr) {
    __asm__ volatile("invlpg (%0)" : : "r"(addr) : "memory");
}

void hal_tlb_flush_all(void) {
    // Reload CR3 to flush entire TLB
    uint64_t cr3;
    __asm__ volatile(
        "mov %%cr3, %0\n"
        "mov %0, %%cr3"
        : "=r"(cr3) : : "memory"
    );
}

uint64_t hal_read_timestamp(void) {
    uint32_t low, high;
    __asm__ volatile("rdtsc" : "=a"(low), "=d"(high));
    return ((uint64_t)high << 32) | low;
}

// Compile-time assertions
_Static_assert(sizeof(struct hal_context) == 56, "Context size mismatch");
_Static_assert(sizeof(struct hal_trapframe) <= 256, "Trap frame too large");