.code16
.section .boot, "ax"
.global _start

_start:
    # Clear interrupts
    cli
    
    # Set up segments
    xor %ax, %ax
    mov %ax, %ds
    mov %ax, %es
    mov %ax, %ss
    mov $0x7c00, %sp
    
    # Print message
    mov $msg, %si
    call print_string
    
    # Halt
    hlt
    
print_string:
    lodsb
    test %al, %al
    jz .done
    mov $0x0e, %ah
    int $0x10
    jmp print_string
.done:
    ret
    
msg:
    .asciz "FeuerBird OS booting...\r\n"
    
    # Pad to 510 bytes and add boot signature
    .org 510
    .word 0xaa55