# lib/thread_switch.S - User-Space Context Switch
#
# This implements cooperative multitasking inside the LibOS.
# The kernel is NOT involved in switching between LibOS threads.
#
# void thread_switch(uint64 *old_sp, uint64 *new_sp);
#   - Saves callee-saved registers to old stack
#   - Switches stack pointer
#   - Restores callee-saved registers from new stack
#   - Returns to new thread's saved return address

#if defined(__x86_64__)

.text
.global _thread_switch
.global thread_switch

# x86_64 calling convention:
#   %rdi = old_sp (pointer to save current SP)
#   %rsi = new_sp (pointer to load new SP from)

_thread_switch:
thread_switch:
    # ═══════════════════════════════════════════════════════════════════
    # 1. SAVE OLD CONTEXT
    # ═══════════════════════════════════════════════════════════════════
    # Push callee-saved registers (System V AMD64 ABI)
    pushq %rbx
    pushq %rbp
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15

    # Save current stack pointer to *old_sp
    movq %rsp, (%rdi)

    # ═══════════════════════════════════════════════════════════════════
    # 2. LOAD NEW CONTEXT
    # ═══════════════════════════════════════════════════════════════════
    # Load new stack pointer from *new_sp
    movq (%rsi), %rsp

    # Restore callee-saved registers
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    popq %rbp
    popq %rbx

    # Return to saved address (now on new thread's stack)
    ret

#elif defined(__aarch64__)

.text
.global _thread_switch
.global thread_switch

// ARM64 calling convention:
//   x0 = old_sp (pointer to save current SP)
//   x1 = new_sp (pointer to load new SP from)

_thread_switch:
thread_switch:
    // ═══════════════════════════════════════════════════════════════════
    // 1. SAVE OLD CONTEXT
    // ═══════════════════════════════════════════════════════════════════
    // Save callee-saved registers and link register
    stp x19, x20, [sp, #-16]!
    stp x21, x22, [sp, #-16]!
    stp x23, x24, [sp, #-16]!
    stp x25, x26, [sp, #-16]!
    stp x27, x28, [sp, #-16]!
    stp x29, x30, [sp, #-16]!    // x29=fp, x30=lr

    // Save current stack pointer to *old_sp
    mov x9, sp
    str x9, [x0]

    // ═══════════════════════════════════════════════════════════════════
    // 2. LOAD NEW CONTEXT
    // ═══════════════════════════════════════════════════════════════════
    // Load new stack pointer from *new_sp
    ldr x9, [x1]
    mov sp, x9

    // Restore callee-saved registers
    ldp x29, x30, [sp], #16
    ldp x27, x28, [sp], #16
    ldp x25, x26, [sp], #16
    ldp x23, x24, [sp], #16
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16

    // Return to saved address (x30/lr was restored)
    ret

#else
#error "Unsupported architecture for thread_switch"
#endif
