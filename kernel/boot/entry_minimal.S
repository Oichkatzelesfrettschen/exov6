# Minimal kernel entry point for ExoKernel v6
# This is where the bootloader jumps after loading the kernel

.globl _start
.globl kmain

# Kernel entry point
.section .text
_start:
    # Set up basic environment
    cli                     # Disable interrupts
    cld                     # Clear direction flag
    
    # Set up stack
    movl $stack_top, %esp   # Set stack pointer
    
    # Clear EFLAGS
    pushl $0
    popfl
    
    # Call kernel main function
    call kmain
    
    # If kmain returns (it shouldn't), halt
halt_loop:
    hlt
    jmp halt_loop

# Kernel stack (4KB)
.section .bss
.align 16
stack_bottom:
.skip 4096                  # 4KB stack
stack_top: