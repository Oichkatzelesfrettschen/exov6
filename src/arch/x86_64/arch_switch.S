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
     * struct arch_context layout:
     *   0-127:  r0-r15 (registers[16])
     *   128:    sp
     *   136:    pc
     *   144:    flags
     */

    /* Save callee-saved registers */
    movq %rbx, 8(%rdi)
    movq %rbp, 48(%rdi)
    movq %r12, 88(%rdi)
    movq %r13, 96(%rdi)
    movq %r14, 104(%rdi)
    movq %r15, 112(%rdi)

    /* Save RFLAGS */
    pushfq
    popq %rax
    movq %rax, 144(%rdi)

    /* Save SP */
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

    /* Restore callee-saved registers */
    movq 8(%rsi), %rbx
    movq 48(%rsi), %rbp
    movq 88(%rsi), %r12
    movq 96(%rsi), %r13
    movq 104(%rsi), %r14
    movq 112(%rsi), %r15

    /* Return to next->pc (which should be on stack) */
    ret
