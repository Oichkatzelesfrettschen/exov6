/**
 * @file context_switch.c
 * @brief Modern C17 Context Switch Implementation
 * 
 * Implements context switching with minimal inline assembly,
 * maximizing C17 code while maintaining performance.
 */

#include <stdint.h>
#include <stdbool.h>
#include "types.h"
#include "proc.h"

/**
 * Modern context switch using C17 with minimal inline assembly
 * 
 * This function saves the current CPU context and switches to a new one.
 * We use GNU C inline assembly with explicit constraints for maximum
 * compiler optimization opportunity.
 * 
 * @param old Pointer to save current context
 * @param new Context to switch to
 */
void swtch(struct context64 **old, struct context64 *new) {
    /* 
     * Context switching requires direct register manipulation which
     * cannot be done in pure C. However, we can use extended inline
     * assembly with proper constraints to let the compiler optimize
     * around this critical code.
     */
    
    __asm__ volatile(
        /* Save callee-saved registers per x86_64 ABI */
        "pushq %%rbp\n\t"
        "pushq %%rbx\n\t"
        "pushq %%r12\n\t"
        "pushq %%r13\n\t"
        "pushq %%r14\n\t"
        "pushq %%r15\n\t"
        
        /* Save current stack pointer to *old */
        "movq %%rsp, (%0)\n\t"
        
        /* Switch to new stack */
        "movq %1, %%rsp\n\t"
        
        /* Restore callee-saved registers */
        "popq %%r15\n\t"
        "popq %%r14\n\t"
        "popq %%r13\n\t"
        "popq %%r12\n\t"
        "popq %%rbx\n\t"
        "popq %%rbp\n\t"
        
        : /* no outputs */
        : "r" (old), "r" (new)  /* inputs: old in any register, new in any register */
        : "memory"              /* clobbers: memory barrier for safety */
    );
}

/**
 * Initialize a new context for a process
 * Pure C17 implementation
 */
void context_init(struct context64 *ctx, void (*entry)(void), void *stack_top) {
    /* Zero out the context */
    ctx->r15 = 0;
    ctx->r14 = 0;
    ctx->r13 = 0;
    ctx->r12 = 0;
    ctx->rbx = 0;
    ctx->rbp = 0;
    
    /* Set the return address to the entry point */
    ctx->rip = (uint64_t)entry;
    
    /* Stack grows down, so stack_top is the highest address */
    /* We need to account for the saved registers */
    uint64_t *stack = (uint64_t*)stack_top;
    stack -= 7;  /* Space for saved registers and return address */
    
    /* Place return address on stack */
    stack[6] = (uint64_t)entry;
}

/**
 * Get current context - pure C17
 */
struct context64* context_current(void) {
    struct context64 *ctx;
    
    /* Get current stack pointer and derive context from it */
    __asm__ volatile(
        "movq %%rsp, %0"
        : "=r" (ctx)
        :
        : "memory"
    );
    
    return ctx;
}

/**
 * Context comparison for debugging - pure C17
 */
bool context_equal(const struct context64 *a, const struct context64 *b) {
    return a->r15 == b->r15 &&
           a->r14 == b->r14 &&
           a->r13 == b->r13 &&
           a->r12 == b->r12 &&
           a->rbx == b->rbx &&
           a->rbp == b->rbp &&
           a->rip == b->rip;
}

/**
 * Validate context integrity - pure C17
 */
bool context_valid(const struct context64 *ctx) {
    /* Basic sanity checks */
    if (!ctx) return false;
    
    /* Check if instruction pointer is in reasonable range */
    /* Kernel text typically starts at 0x80000000 or higher */
    if (ctx->rip < 0x80000000 || ctx->rip > 0xFFFFFFFFFFFFFFFF) {
        return false;
    }
    
    /* Stack pointer should be aligned */
    if (ctx->rbp & 0x7) {
        return false;
    }
    
    return true;
}

/**
 * Performance monitoring for context switches - pure C17
 */
static _Atomic uint64_t switch_count = 0;
static _Atomic uint64_t switch_cycles = 0;

void context_switch_stats(uint64_t *count, uint64_t *cycles) {
    if (count) *count = switch_count;
    if (cycles) *cycles = switch_cycles;
}

/**
 * Enhanced context switch with performance monitoring
 */
void swtch_monitored(struct context64 **old, struct context64 *new) {
    uint64_t start_cycles, end_cycles;
    
    /* Read TSC before switch */
    __asm__ volatile(
        "rdtsc\n\t"
        "shlq $32, %%rdx\n\t"
        "orq %%rdx, %%rax"
        : "=a" (start_cycles)
        :
        : "rdx"
    );
    
    /* Perform the actual switch */
    swtch(old, new);
    
    /* Read TSC after switch */
    __asm__ volatile(
        "rdtsc\n\t"
        "shlq $32, %%rdx\n\t"
        "orq %%rdx, %%rax"
        : "=a" (end_cycles)
        :
        : "rdx"
    );
    
    /* Update statistics atomically */
    switch_count++;
    switch_cycles += (end_cycles - start_cycles);
}
