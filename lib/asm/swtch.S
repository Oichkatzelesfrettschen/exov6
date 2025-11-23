# For x86_64
.global thread_switch
thread_switch:
    # rdi = old_context_ptr
    # rsi = new_context_ptr

    # 1. Save Old Callee-Saved Registers
    pushq %rbx
    pushq %rbp
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
    popq %rbp
    popq %rbx

    ret
