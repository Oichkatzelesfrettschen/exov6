/**
 * @file exception.c
 * @brief LibOS Exception Handler (Phase 4)
 *
 * This file implements the C-level exception handling for the LibOS.
 * When the kernel dispatches an exception to user space, the assembly
 * landing pad (exception.S) calls this handler.
 *
 * The handler can:
 * 1. Handle the exception (e.g., demand paging)
 * 2. Modify the trapframe and resume
 * 3. Return NULL to terminate the process
 */

#include <stdint.h>
#include <types.h>
#include <exov6_interface.h>

// Forward declarations
extern void print(const char *s);
extern void print_hex(uint64 n);
extern uint64 sys_alloc_page(void);
extern int sys_map_page(int target_env, uint64 phys, uint64 virt, int perm);

// Scheduler hooks (Phase 6)
extern void thread_preempt(void) __attribute__((weak));
extern void scheduler_init(void) __attribute__((weak));

// Exception handler callback (can be set by application)
static struct ExoTrapFrame* (*user_exception_handler)(struct ExoTrapFrame *tf) = 0;

/**
 * Register a custom exception handler
 * @param handler Function pointer to custom handler
 */
void libos_set_exception_handler(struct ExoTrapFrame* (*handler)(struct ExoTrapFrame*)) {
    user_exception_handler = handler;
}

// Memory layout constants for validation
#define USER_HEAP_START   0x10000000ULL   // Start of valid heap region
#define USER_HEAP_END     0x80000000ULL   // End of valid heap region
#define USER_STACK_TOP    0xF0000000ULL   // Top of user stack region
#define NULL_GUARD_SIZE   0x1000ULL       // First page is always invalid (NULL guard)

/**
 * Check if an address is in a valid mappable region
 */
static int
is_valid_fault_address(uint64 addr)
{
    // NULL pointer guard - first page is NEVER valid
    if (addr < NULL_GUARD_SIZE) {
        return 0;
    }

    // Check if in heap region
    if (addr >= USER_HEAP_START && addr < USER_HEAP_END) {
        return 1;
    }

    // Check if in stack region (grows down from USER_STACK_TOP)
    if (addr >= (USER_STACK_TOP - 0x100000) && addr < USER_STACK_TOP) {
        return 1;
    }

    // Address outside valid regions
    return 0;
}

/**
 * Default page fault handler - implements simple demand paging
 * @param tf Trap frame with fault information
 * @return Modified trapframe to resume, or NULL to terminate
 */
static struct ExoTrapFrame*
default_pagefault_handler(struct ExoTrapFrame *tf)
{
    uint64 fault_addr = tf->addr;
    uint64 page_addr = fault_addr & ~0xFFFULL;  // Page-align

    print("LibOS: Page fault at ");
    print_hex(fault_addr);
    print(" (page ");
    print_hex(page_addr);
    print(")\n");

    // ═══════════════════════════════════════════════════════════════════
    // POLICY CHECK: Is this a valid address to map?
    // ═══════════════════════════════════════════════════════════════════
    if (!is_valid_fault_address(fault_addr)) {
        print("LibOS: INVALID ADDRESS - ");
        if (fault_addr < NULL_GUARD_SIZE) {
            print("NULL POINTER DEREFERENCE\n");
        } else {
            print("address outside valid region\n");
        }
        print("LibOS: Terminating process (SIGSEGV equivalent)\n");
        return 0;  // KILL - don't try to map invalid addresses
    }

    // Try to allocate and map a page
    uint64 phys = sys_alloc_page();
    if (phys == 0 || phys == (uint64)-1) {
        print("LibOS: Failed to allocate page for fault (out of memory)\n");
        return 0;  // Cannot handle - terminate
    }

    // Map with RW permissions
    if (sys_map_page(0, phys, page_addr, 0x3) < 0) {
        print("LibOS: Failed to map page for fault\n");
        return 0;  // Cannot handle - terminate
    }

    print("LibOS: Demand paging: mapped page, resuming...\n");

    // Resume at the faulting instruction (it will retry the access)
    return tf;
}

/**
 * Main exception handler - called from assembly landing pad
 * @param tf Pointer to ExoTrapFrame on exception stack
 * @return Trapframe to resume with, or NULL to exit
 */
struct ExoTrapFrame*
libos_exception_handler(struct ExoTrapFrame *tf)
{
    print("\n═══════════════════════════════════════════════════════\n");
    print("LibOS EXCEPTION HANDLER\n");
    print("═══════════════════════════════════════════════════════\n");
    print("  Trap:    ");
    print_hex(tf->trapno);
    print("\n  Error:   ");
    print_hex(tf->err);
    print("\n  Address: ");
    print_hex(tf->addr);
    print("\n  RIP:     ");
    print_hex(tf->rip);
    print("\n  RSP:     ");
    print_hex(tf->rsp);
    print("\n═══════════════════════════════════════════════════════\n");

    // If user registered a custom handler, call it first
    if (user_exception_handler) {
        struct ExoTrapFrame *result = user_exception_handler(tf);
        if (result)
            return result;
        // Custom handler declined, fall through to defaults
    }

    // Handle specific exceptions
    switch (tf->trapno) {
    case EXO_TRAP_PGFLT:  // Page fault (14)
        return default_pagefault_handler(tf);

    case EXO_TRAP_GPFLT:  // General protection fault (13)
        print("LibOS: General protection fault - cannot handle\n");
        return 0;

    case EXO_TRAP_DIVIDE:  // Divide by zero (0)
        print("LibOS: Divide by zero - cannot handle\n");
        return 0;

    case EXO_TRAP_ILLOP:  // Invalid opcode (6)
        print("LibOS: Invalid opcode - cannot handle\n");
        return 0;

    default:
        // Check if it's an IRQ we should handle
        if (tf->trapno >= EXO_IRQ_BASE) {
            uint64 irq = tf->trapno - EXO_IRQ_BASE;

            // Timer IRQ (IRQ 0) - preemptive scheduling
            if (irq == 0 && thread_preempt) {
                // Don't print for timer - too noisy
                thread_preempt();
                return tf;
            }

            // Other IRQs - just note and resume
            print("LibOS: IRQ ");
            print_hex(irq);
            print(" - no handler registered\n");
            return tf;
        }

        print("LibOS: Unhandled exception ");
        print_hex(tf->trapno);
        print("\n");
        return 0;  // Terminate
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Exception Stack Setup
// ═══════════════════════════════════════════════════════════════════════════

// Exception stack (separate from normal stack)
#define EXCEPTION_STACK_SIZE (4096 * 4)  // 16KB
static char exception_stack[EXCEPTION_STACK_SIZE] __attribute__((aligned(16)));

// Forward declaration of entry point
extern void upcall_entry(struct ExoTrapFrame *tf);

/**
 * Initialize exception handling
 * Call this early in LibOS initialization.
 */
void libos_exception_init(void) {
    // Calculate stack top (grows down)
    uint64 stack_top = (uint64)&exception_stack[EXCEPTION_STACK_SIZE];

    // Register with kernel
    extern int sys_env_set_handler(uint64 handler_va, uint64 stack_va);
    if (sys_env_set_handler((uint64)upcall_entry, stack_top) < 0) {
        print("LibOS: WARNING - Failed to register exception handler\n");
    } else {
        print("LibOS: Exception handler registered\n");
        print("  Handler: ");
        print_hex((uint64)upcall_entry);
        print("\n  Stack:   ");
        print_hex(stack_top);
        print("\n");
    }
}
