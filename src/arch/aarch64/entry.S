#include "param.h"

.section .text
.globl _start
_start:
    ldr x0, =stack0 + KSTACKSIZE
    mov sp, x0
    bl main64
1:
    wfi
    b 1b

.section .bss
    .align 3
.globl stack0
stack0:
    .skip KSTACKSIZE
