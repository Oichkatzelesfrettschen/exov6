/*
 * arch_switch.S - x86_64 Context Switch
 * POSIX.1-2024 / System V AMD64 ABI compliant implementation
 * for FeuerBird exokernel.
 */

.global arch_switch_to
.type arch_switch_to, @function

/*
 * void arch_switch_to(struct arch_context* prev, struct arch_context* next);
 *
 * RDI = prev (pointer to struct to save current state into)
 * RSI = next (pointer to struct to restore state from)
 *
 * struct arch_context layout:
 * 0:  rbx
 * 8:  rbp
 * 16: r12
 * 24: r13
 * 32: r14
 * 40: r15
 * 48: rsp  (Stack Pointer)
 * 56: rip  (Instruction Pointer / Return Address)
 * 64: rflags
 *
 * Note: We only save Callee-Saved registers. Caller-saved registers
 * (rax, rcx, rdx, rsi, rdi, r8-r11) are saved by the compiler on the
 * stack if needed before this function is called.
 */

arch_switch_to:
    .cfi_startproc
    
    /* ----------------- SAVE STATE (prev) ----------------- */

    /* Save callee-saved registers */
    movq %rbx, 0(%rdi)
    movq %rbp, 8(%rdi)
    movq %r12, 16(%rdi)
    movq %r13, 24(%rdi)
    movq %r14, 32(%rdi)
    movq %r15, 40(%rdi)

    /* Save CPU Flags (RFLAGS) */
    /* Essential to preserve Interrupt Flag (IF) state */
    pushfq
    popq %rax
    movq %rax, 64(%rdi)

    /* Save Return Address (RIP) */
    /* The return address was pushed onto the stack by the 'call' instruction.
       It is currently at (%rsp). We save it to the struct for debugging/introspection,
       though the actual switch relies on the stack content. */
    movq (%rsp), %rax
    movq %rax, 56(%rdi)

    /* Save Stack Pointer */
    /* We save the RSP *after* the return address was pushed. 
       When we restore this RSP, the 'ret' instruction will pop that return address. */
    movq %rsp, 48(%rdi)

    /* ----------------- SWITCH STACKS ----------------- */

    /* Load next SP */
    /* This is the pivotal point of the context switch. 
       After this instruction, we are running on the 'next' thread's stack. */
    movq 48(%rsi), %rsp

    /* ----------------- RESTORE STATE (next) ----------------- */

    /* Restore RFLAGS */
    /* We use RAX as a scratch register (allowed by ABI) to move flags */
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

    /* Return to next->pc */
    /* The 'ret' instruction pops the return address from the top of the 
       newly restored stack (next->rsp). */
    ret

    .cfi_endproc