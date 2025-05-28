# Context switch for x86_64
#
#   void swtch(struct context64 **old, struct context64 *new);
#
# Save the current registers on the stack, creating a struct context64
# and save its address in *old. Switch stacks to new and restore
# previously saved registers.
# Scheduler lock state is preserved across context switches.

.globl swtch
swtch:
    movq %rdi, %rax      # old
    movq %rsi, %rdx      # new

    # Save old callee-saved registers
    pushq %rbp
    pushq %rbx
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15

    # Switch stacks
    movq %rsp, (%rax)
    movq %rdx, %rsp

    # Load new callee-saved registers
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    popq %rbx
    popq %rbp
    ret
