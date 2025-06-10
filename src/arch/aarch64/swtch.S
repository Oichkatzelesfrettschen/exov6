# Context switch for AArch64
# void swtch(struct context64 **old, struct context64 *new);
# Scheduler lock state is preserved across context switches.

.globl swtch
swtch:
    mov x9, x0      # old
    mov x10, x1     # new
    stp x29, x30, [sp, #-16]!
    stp x19, x20, [sp, #-16]!
    stp x21, x22, [sp, #-16]!
    stp x23, x24, [sp, #-16]!
    stp x25, x26, [sp, #-16]!
    stp x27, x28, [sp, #-16]!
    mov x11, sp
    str x11, [x9]
    mov sp, x10
    ldp x27, x28, [sp], #16
    ldp x25, x26, [sp], #16
    ldp x23, x24, [sp], #16
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret
