# x86-64 trap handling assembly
# Handles all interrupts and system calls

#include "mmu.h"
#include "memlayout.h"

.text
.code64

# vectors.S sends all traps here
.globl alltraps
alltraps:
    # Build trap frame
    push %r15
    push %r14
    push %r13
    push %r12
    push %r11
    push %r10
    push %r9
    push %r8
    push %rdi
    push %rsi
    push %rbp
    push %rdx
    push %rcx
    push %rbx
    push %rax
    
    # Set up data segments
    mov $SEG_KDATA, %ax
    mov %ax, %ds
    mov %ax, %es
    
    # Call trap(tf), where tf=%rsp
    mov %rsp, %rdi
    call trap
    
    # Return falls through to trapret

.globl trapret
trapret:
    # Pop registers
    pop %rax
    pop %rbx
    pop %rcx
    pop %rdx
    pop %rbp
    pop %rsi
    pop %rdi
    pop %r8
    pop %r9
    pop %r10
    pop %r11
    pop %r12
    pop %r13
    pop %r14
    pop %r15
    
    # Discard trapno and errorcode
    add $16, %rsp
    
    # Return from interrupt
    iretq