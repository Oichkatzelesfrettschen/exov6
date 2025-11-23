# lib/exception.S - Exokernel Upcall Landing Pad
#
# This is the entry point for user-space exception handling.
# When the kernel dispatches an exception to user space, it jumps here.
# The ExoTrapFrame pointer is passed in the first argument register.

#if defined(__x86_64__)

.text
.global _upcall_entry
.global upcall_entry
.type _upcall_entry, @function
.type upcall_entry, @function

# x86_64 ABI: First argument in %rdi
# On entry:
#   - %rdi = pointer to ExoTrapFrame on exception stack
#   - %rsp = exception stack (below ExoTrapFrame)

_upcall_entry:
upcall_entry:
    # Stack is already set up by kernel, ExoTrapFrame at (%rdi)
    # Save callee-saved registers (C calling convention)
    pushq %rbp
    movq %rsp, %rbp
    pushq %rbx
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15

    # Call C handler: libos_exception_handler(struct ExoTrapFrame *tf)
    # %rdi already contains the trapframe pointer
#ifdef __APPLE__
    call _libos_exception_handler
#else
    call libos_exception_handler
#endif

    # C handler returns the (possibly modified) trapframe pointer in %rax
    # If handler returns 0, we should exit
    testq %rax, %rax
    jz .Lupcall_exit

    # Restore callee-saved registers
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    popq %rbx
    popq %rbp

    # Call sys_env_resume to restore context
    # Argument: pointer to ExoTrapFrame (in %rax from handler)
    movq %rax, %rdi
    movq $14, %rax          # SYS_env_resume = 14
    syscall

    # If we get here, resume failed - fall through to exit

.Lupcall_exit:
    # Clean up and exit
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    popq %rbx
    popq %rbp

    # Exit process
    movq $3, %rax           # SYS_env_destroy = 3
    syscall

    # Should not reach here
    ud2

#elif defined(__aarch64__)

.text
.global _upcall_entry
.global upcall_entry

// ARM64 ABI: First argument in x0
// On entry:
//   - x0 = pointer to ExoTrapFrame on exception stack
//   - sp = exception stack

_upcall_entry:
upcall_entry:
    // Save frame pointer and link register
    stp x29, x30, [sp, #-16]!
    mov x29, sp

    // Save callee-saved registers
    stp x19, x20, [sp, #-16]!
    stp x21, x22, [sp, #-16]!
    stp x23, x24, [sp, #-16]!
    stp x25, x26, [sp, #-16]!
    stp x27, x28, [sp, #-16]!

    // Call C handler: libos_exception_handler(struct ExoTrapFrame *tf)
    // x0 already contains the trapframe pointer
#ifdef __APPLE__
    bl _libos_exception_handler
#else
    bl libos_exception_handler
#endif

    // Check return value
    cbz x0, Lupcall_exit_arm

    // Call sys_env_resume to restore context
    mov x8, #14             // SYS_env_resume = 14
    svc #0

    // If we get here, resume failed

Lupcall_exit_arm:
    // Restore callee-saved registers
    ldp x27, x28, [sp], #16
    ldp x25, x26, [sp], #16
    ldp x23, x24, [sp], #16
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16

    // Exit process
    mov x8, #3              // SYS_env_destroy = 3
    svc #0

    // Should not reach here
    brk #0

#else
#error "Unsupported architecture for exception handling"
#endif
