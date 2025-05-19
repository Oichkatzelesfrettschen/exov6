#include "asm.h"
#include "memlayout.h"
#include "mmu.h"

#define CR4_PAE 0x00000020

# Segments for protected mode (32-bit) and long mode (64-bit)

# 64-bit segment descriptor helper provided by asm.h

.code16
.globl start
start:
    cli
    xorw %ax,%ax
    movw %ax,%ds
    movw %ax,%es
    movw %ax,%ss

# Enable A20
seta20.1:
    inb $0x64,%al
    testb $0x2,%al
    jnz seta20.1
    movb $0xd1,%al
    outb %al,$0x64
seta20.2:
    inb $0x64,%al
    testb $0x2,%al
    jnz seta20.2
    movb $0xdf,%al
    outb %al,$0x60

    lgdt gdtdesc32
    movl %cr0,%eax
    orl $CR0_PE,%eax
    movl %eax,%cr0
    ljmp $(1<<3), $prot32

.code32
prot32:
    movw $(2<<3), %ax
    movw %ax,%ds
    movw %ax,%es
    movw %ax,%ss
    movw $0,%ax
    movw %ax,%fs
    movw %ax,%gs

    lgdt gdtdesc64

    movl %cr4,%eax
    orl $CR4_PAE,%eax
    movl %eax,%cr4

    movl $pml4,%eax
    movl %eax,%cr3

    movl $0xC0000080,%ecx
    rdmsr
    orl $0x00000100,%eax
    wrmsr

    movl %cr0,%eax
    orl $(CR0_PE|CR0_PG|CR0_WP),%eax
    movl %eax,%cr0

    ljmp $(3<<3), $longmode

.code64
longmode:
    mov $start,%rsp
    call bootmain
1:  jmp 1b

# GDTs
.p2align 2
gdt32:
    SEG_NULLASM
    SEG_ASM(STA_X|STA_R,0,0xffffffff)
    SEG_ASM(STA_W,0,0xffffffff)

gdtdesc32:
    .word (gdtdesc32 - gdt32 - 1)
    .long gdt32

.p2align 2
gdt64:
    SEG_NULLASM
    SEG_ASM64(STA_X|STA_R,0,0xffffffff)
    SEG_ASM64(STA_W,0,0xffffffff)

gdtdesc64:
    .word (gdtdesc64 - gdt64 - 1)
    .long gdt64
    .long 0

# Minimal identity-mapped page tables
.p2align 12
pml4:
    .quad pdpt + 0x3
.p2align 12
pdpt:
    .quad pd + 0x3
.p2align 12
pd:
    .quad 0x00000000 + 0x83  # 2MB page
