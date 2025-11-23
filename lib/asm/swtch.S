# For x86_64
.global swtch
swtch:
    # rdi = old_context_ptr
    # rsi = new_context_ptr

    # 1. Save Old Callee-Saved Registers
    pushq %rbp
    pushq %rbx
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15

    # 2. Save Old Stack Pointer
    movq %rsp, (%rdi)

    # 3. Load New Stack Pointer
    movq (%rsi), %rsp

    # 4. Restore New Registers
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    popq %rbx
    popq %rbp

    ret
