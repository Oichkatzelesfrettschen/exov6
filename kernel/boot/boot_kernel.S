# Minimal boot kernel for ExoKernel v6
.code16
.global _start
_start:
    # Print boot message
    mov $0x0e, %ah
    mov $'E', %al
    int $0x10
    mov $'X', %al
    int $0x10
    mov $'O', %al
    int $0x10
    
    # Jump to kernel main
    ljmp $0x0, $kernel_main

kernel_main:
    # Set up segments
    xor %ax, %ax
    mov %ax, %ds
    mov %ax, %es
    mov %ax, %ss
    mov $0x7c00, %sp
    
    # Print POSIX message
    mov $msg, %si
print_loop:
    lodsb
    or %al, %al
    jz done
    mov $0x0e, %ah
    int $0x10
    jmp print_loop
    
done:
    # Halt
    hlt
    jmp done

msg:
    .asciz " POSIX-2024 READY\r\n"

# Boot signature
.org 510
.word 0xaa55
