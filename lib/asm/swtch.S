# For x86_64
.global swtch
swtch:
    # rdi = old_context_ptr (context_t **)
    # rsi = new_context_ptr (context_t *)

    # 1. Save Old Callee-Saved Registers
    # Stack layout must match struct context64:
    # R15 (low), R14, R13, R12, RBX, RBP, RIP (high)
    # RIP is already on the stack from the call.
    # We must push RBP, then RBX, etc.
    pushq %rbp
    pushq %rbx
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15

    # 2. Save Old Stack Pointer
    movq %rsp, (%rdi)

    # 3. Load New Stack Pointer
    # rsi holds the address of the new context structure
    movq %rsi, %rsp

    # 4. Restore New Registers
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    popq %rbx
    popq %rbp

    ret
