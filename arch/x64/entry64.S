#include "asm.h"
#include "memlayout.h"
#include "mmu.h"
#include "param.h"

# Build a 64-bit segment descriptor
.macro SEG_ASM64 type base lim
    .word (((\lim) >> 12) & 0xffff), ((\base) & 0xffff)
    .byte (((\base) >> 16) & 0xff), (0x90 | (\type))
    .byte (0xA0 | (((\lim) >> 28) & 0xf)), (((\base) >> 24) & 0xff)
.endm

.p2align 2
.globl _start
_start = V2P_WO(entry64)

.globl entry64
entry64:
    lgdt gdtdesc
    movw $(2<<3), %ax
    movw %ax, %ds
    movw %ax, %es
    movw %ax, %ss
    movw %ax, %fs
    movw %ax, %gs

    mov $stack64 + KSTACKSIZE, %rsp
    mov $main64, %rax
    jmp *%rax

.comm stack64, KSTACKSIZE

# 64-bit GDT for the kernel
.p2align 2
gdt:
    SEG_NULLASM
    SEG_ASM64(STA_X|STA_R,0,0xffffffff)  # code
    SEG_ASM64(STA_W,0,0xffffffff)        # data

gdtdesc:
    .word (gdtdesc - gdt - 1)
    .long gdt
    .long 0
