.section .text
.globl vectors
vectors:
    .rept 256
        b alltraps
    .endr
