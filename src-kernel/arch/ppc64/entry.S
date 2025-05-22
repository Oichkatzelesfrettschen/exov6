#include "param.h"
.section .text
.globl _start
_start:
    bl main64
1:
    b 1b
.section .bss
    .align 3
.globl stack0
stack0:
    .space KSTACKSIZE
