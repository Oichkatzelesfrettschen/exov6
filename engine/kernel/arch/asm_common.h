#pragma once

// Common assembly macros for boot/entry code

// Enable the A20 line so the CPU can access >1MB memory
#define ENABLE_A20 \
1: inb $0x64, %al; testb $0x2, %al; jnz 1b; \
   movb $0xd1, %al; outb %al, $0x64; \
2: inb $0x64, %al; testb $0x2, %al; jnz 2b; \
   movb $0xdf, %al; outb %al, $0x60

// Load GDT and enable protected mode, then jump to the given label
#define SETUP_PROT_MODE(gdt, sel, label) \
    lgdt gdt; \
    movl %cr0, %eax; \
    orl $CR0_PE, %eax; \
    movl %eax, %cr0; \
    ljmp $(sel), $label

// Initialize data segment registers after entering protected mode
#define INIT_PROT_MODE_DATA(sel) \
    movw $(sel), %ax; \
    movw %ax, %ds; \
    movw %ax, %es; \
    movw %ax, %ss; \
    movw $0, %ax; \
    movw %ax, %fs; \
    movw %ax, %gs


