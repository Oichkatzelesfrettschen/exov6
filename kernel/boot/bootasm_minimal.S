# Minimal bootloader for ExoKernel v6
# This replaces the complex boot system with a simple one that works

# Boot sector - loaded by BIOS at 0x7C00
.code16                     # Start in 16-bit mode
.globl start
start:
    cli                     # Disable interrupts
    cld                     # Clear direction flag
    
    # Set up segments
    xorw %ax, %ax           # Clear AX
    movw %ax, %ds           # Data segment = 0
    movw %ax, %es           # Extra segment = 0
    movw %ax, %ss           # Stack segment = 0
    movw $0x7C00, %sp       # Stack pointer below bootloader

    # Print loading message
    movw $loading_msg, %si
    call print_string

    # Load kernel from disk
    # Load 20 sectors starting from sector 2
    movw $0x1000, %ax       # ES = 0x1000 (load kernel at 0x10000)
    movw %ax, %es
    xorw %bx, %bx           # BX = 0 (offset within segment)
    
    movb $0x02, %ah         # BIOS read sectors function
    movb $20, %al           # Number of sectors to read  
    movb $0x80, %dl         # Drive number (0x80 = first hard disk)
    movb $0, %dh            # Head 0
    movw $2, %cx            # Sector 2, cylinder 0
    int $0x13               # Call BIOS
    
    jc load_error           # Jump if carry flag set (error)

    # Print loaded message
    movw $loaded_msg, %si
    call print_string

    # Switch to protected mode
    lgdt gdtdesc            # Load Global Descriptor Table
    
    movl %cr0, %eax         # Get CR0
    orl $0x1, %eax          # Set PE bit (Protection Enable)
    movl %eax, %cr0         # Enter protected mode
    
    # Far jump to 32-bit code
    ljmp $0x08, $protected_mode

load_error:
    movw $error_msg, %si
    call print_string
    jmp halt

# Print string function (16-bit mode)
print_string:
    lodsb                   # Load byte from [SI] into AL, increment SI
    orb %al, %al            # Test if byte is zero
    jz print_done           # If zero, we're done
    movb $0x0e, %ah         # BIOS teletype function
    int $0x10               # Call BIOS
    jmp print_string        # Continue with next character
print_done:
    ret

halt:
    hlt                     # Halt processor
    jmp halt                # Loop forever

# Messages
loading_msg: .asciz "Loading ExoKernel v6...\r\n"
loaded_msg:  .asciz "Kernel loaded, switching to protected mode...\r\n"  
error_msg:   .asciz "Boot error!\r\n"

# Global Descriptor Table
.align 4
gdt:
    # Null descriptor
    .word 0, 0
    .byte 0, 0, 0, 0
    
    # Code segment descriptor
    .word 0xFFFF, 0         # Limit 0-15, Base 0-15
    .byte 0, 0x9A, 0xCF, 0  # Base 16-23, Access, Granularity, Base 24-31
    
    # Data segment descriptor  
    .word 0xFFFF, 0         # Limit 0-15, Base 0-15
    .byte 0, 0x92, 0xCF, 0  # Base 16-23, Access, Granularity, Base 24-31

gdtdesc:
    .word gdtdesc - gdt - 1 # GDT limit
    .long gdt               # GDT base

# 32-bit protected mode code
.code32
protected_mode:
    # Set up data segments
    movw $0x10, %ax         # Data segment selector
    movw %ax, %ds           # Data segment
    movw %ax, %es           # Extra segment
    movw %ax, %fs           # FS segment
    movw %ax, %gs           # GS segment
    movw %ax, %ss           # Stack segment
    
    # Set up stack
    movl $0x90000, %esp     # Stack at 0x90000
    
    # Jump to kernel main
    movl $0x10000, %eax     # Kernel loaded at 0x10000
    jmp *%eax               # Jump to kernel
    
    # Should never reach here
    hlt

# Boot signature (required at end of boot sector)
.org 510
.word 0xAA55