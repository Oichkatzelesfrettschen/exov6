.section .text
.globl _start
_start:
    bl bootmain
1:
    wfi
    b 1b
