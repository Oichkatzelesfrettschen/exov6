.section .text
.globl _start
_start:
    bl bootmain
1:
    b 1b
