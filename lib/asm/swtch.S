# -------------------------------------------------------------------
# Exokernel LibOS Context Switch
# Architecture: x86_64 (System V AMD64 ABI)
# -------------------------------------------------------------------

.global thread_switch

# void thread_switch(uint64 *old_sp_ptr, uint64 *new_sp_ptr);
#
# Arguments (System V ABI):
#   %rdi = old_sp_ptr (Pointer to the memory location where we save the old RSP)
#   %rsi = new_sp_ptr (Pointer to the memory location where we read the new RSP)

thread_switch:
    # ---------------------------------------------------------------
    # 1. Save Callee-Saved Registers
    # ---------------------------------------------------------------
    # The ABI dictates these registers must be preserved across calls.
    # Caller-saved registers (rax, rcx, rdx, etc.) are assumed lost.
    pushq %rbx
    pushq %rbp
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15

    # ---------------------------------------------------------------
    # 2. Switch Stacks
    # ---------------------------------------------------------------
    # Save the current stack pointer (RSP) into the address provided by RDI
    movq %rsp, (%rdi)

    # Load the new stack pointer (RSP) from the address provided by RSI
    movq (%rsi), %rsp

    # ---------------------------------------------------------------
    # 3. Restore Callee-Saved Registers (LIFO Order)
    # ---------------------------------------------------------------
    # We are now on the NEW stack. These pops restore the state
    # of the new thread.
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    popq %rbp
    popq %rbx

    # ---------------------------------------------------------------
    # 4. Return to New Context
    # ---------------------------------------------------------------
    # The 'ret' instruction pops the return address from the NEW stack.
    # If this is a new thread, this jumps to 'thread_entry_stub'.
    ret