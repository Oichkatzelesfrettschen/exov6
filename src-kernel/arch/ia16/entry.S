#include "asm.h"
#include "memlayout.h"
#include "param.h"

.code16
.globl entry16
entry16:
  movw $(stack16 + KSTACKSIZE), %sp
  call main
1:
  jmp 1b

.comm stack16, KSTACKSIZE
