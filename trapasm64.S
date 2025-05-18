#include "mmu.h"

.globl alltraps
alltraps:
    pushq %rax
    movzwq %ds, %rax
    pushq %rax
    movzwq %es, %rax
    pushq %rax
    movzwq %fs, %rax
    pushq %rax
    movzwq %gs, %rax
    pushq %rax

    pushq %rcx
    pushq %rdx
    pushq %rbx
    pushq %rbp
    pushq %rsi
    pushq %rdi
    pushq %r8
    pushq %r9
    pushq %r10
    pushq %r11
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15

    mov $ (SEG_KDATA<<3), %ax
    mov %ax, %ds
    mov %ax, %es

    mov %rsp, %rdi
    call trap

.globl trapret
trapret:
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    popq %r11
    popq %r10
    popq %r9
    popq %r8
    popq %rdi
    popq %rsi
    popq %rbp
    popq %rbx
    popq %rdx
    popq %rcx
    popq %rax
    mov %ax, %gs
    popq %rax
    mov %ax, %fs
    popq %rax
    mov %ax, %es
    popq %rax
    mov %ax, %ds
    addq $16, %rsp
    iretq
