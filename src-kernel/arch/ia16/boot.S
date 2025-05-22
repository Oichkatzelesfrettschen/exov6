#include "asm.h"
#include "memlayout.h"

.code16
.globl start
start:
  cli
  xorw %ax, %ax
  movw %ax, %ds
  movw %ax, %es
  movw %ax, %ss
  movw $start, %sp
  call bootmain
1:
  jmp 1b
