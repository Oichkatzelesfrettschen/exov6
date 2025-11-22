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
     *   0:   rbx
     *   8:   rbp
     *   16:  r12
     *   24:  r13
     *   32:  r14
     *   40:  r15
     *   48:  sp
     *   56:  pc
     *   64:  flags
     *
     * Only callee-saved registers are preserved. Caller-saved registers
     * (rax, rcx, rdx, rsi, rdi, r8-r11) are the compiler's responsibility.
     */

    /* Save callee-saved registers */
    movq %rbx, 0(%rdi)
    movq %rbp, 8(%rdi)
    movq %r12, 16(%rdi)
    movq %r13, 24(%rdi)
    movq %r14, 32(%rdi)
    movq %r15, 40(%rdi)

    /* Save SP */
    movq %rsp, 48(%rdi)

    /* Save PC (return address on stack) */
    movq (%rsp), %rax
    movq %rax, 56(%rdi)

    /* Save RFLAGS */
    pushfq
    popq %rax
    movq %rax, 64(%rdi)

    /* ----------------- SWITCH ----------------- */

    /* Load next SP */
    movq 48(%rsi), %rsp

    /* ----------------- RESTORE ----------------- */

    /* Restore RFLAGS */
    movq 64(%rsi), %rax
    pushq %rax
    popfq

    /* Restore callee-saved registers */
    movq 0(%rsi), %rbx
    movq 8(%rsi), %rbp
    movq 16(%rsi), %r12
    movq 24(%rsi), %r13
    movq 32(%rsi), %r14
    movq 40(%rsi), %r15

    /* Return to next->pc (which should be on stack) */
    ret
