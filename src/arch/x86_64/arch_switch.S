/*
 * arch_switch.S - x86_64 Context Switch
 */

.global arch_switch_to
.type arch_switch_to, @function
arch_switch_to:
    /*
     * void arch_switch_to(struct arch_context* prev, struct arch_context* next);
     * RDI = prev
     * RSI = next
     *
     * struct arch_context layout (16 registers + sp + pc + flags):
     *   0: RAX, 8: RBX, 16: RCX, 24: RDX, 32: RSI, 40: RDI, 48: RBP, 56: RSP
     *   64: R8, 72: R9, 80: R10, 88: R11, 96: R12, 104: R13, 112: R14, 120: R15
     *   128: sp (saved stack pointer for switching)
     *   136: pc (return address)
     *   144: flags (RFLAGS)
     */

    /* Save all registers to prev (RDI) */
    movq %rax, 0(%rdi)
    movq %rbx, 8(%rdi)
    movq %rcx, 16(%rdi)
    movq %rdx, 24(%rdi)
    movq %rsi, 32(%rdi)
    movq %rdi, 40(%rdi)
    movq %rbp, 48(%rdi)
    movq %rsp, 56(%rdi) /* Save RSP value */
    movq %r8,  64(%rdi)
    movq %r9,  72(%rdi)
    movq %r10, 80(%rdi)
    movq %r11, 88(%rdi)
    movq %r12, 96(%rdi)
    movq %r13, 104(%rdi)
    movq %r14, 112(%rdi)
    movq %r15, 120(%rdi)

    /* Save RFLAGS */
    pushfq
    popq %rax
    movq %rax, 144(%rdi)

    /* Save SP for switching */
    movq %rsp, 128(%rdi)

    /* Save PC (return address on stack) */
    movq (%rsp), %rax
    movq %rax, 136(%rdi)

    /* ----------------- SWITCH ----------------- */

    /* Load next SP */
    movq 128(%rsi), %rsp

    /* ----------------- RESTORE ----------------- */

    /* Restore RFLAGS */
    movq 144(%rsi), %rax
    pushq %rax
    popfq

    /* Prepare to restore registers using the stack to handle RSI/RDI
       RSI holds 'next' pointer. We need it until the end.
       We push values of RSI and RDI to the stack, then restore others, then pop.
    */

    /* Push next->RDI (offset 40) */
    pushq 40(%rsi)

    /* Push next->RSI (offset 32) */
    pushq 32(%rsi)

    /* Restore other registers */
    movq 0(%rsi), %rax
    movq 8(%rsi), %rbx
    movq 16(%rsi), %rcx
    movq 24(%rsi), %rdx
    movq 48(%rsi), %rbp
    /* RSP is already restored via stack switch */
    movq 64(%rsi), %r8
    movq 72(%rsi), %r9
    movq 80(%rsi), %r10
    movq 88(%rsi), %r11
    movq 96(%rsi), %r12
    movq 104(%rsi), %r13
    movq 112(%rsi), %r14
    movq 120(%rsi), %r15

    /* Pop RSI (last pushed was RSI value) */
    popq %rsi

    /* Pop RDI (first pushed was RDI value) */
    popq %rdi

    /* Return to next->pc (which should be on stack) */
    ret
