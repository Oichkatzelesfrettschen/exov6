#include "param.h"
.section .text
.globl _start
_start:
    ldr r0, =stack0 + KSTACKSIZE
    mov sp, r0
    bl main
1:
    wfi
    b 1b
.section .bss
    .align 3
.globl stack0
stack0:
    .space KSTACKSIZE
