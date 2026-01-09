/*
 * multiboot2.S - Multiboot2 Header and 32-to-64-bit Boot Trampoline
 *
 * This file provides:
 * 1. Multiboot2 header for QEMU -kernel boot
 * 2. 32-bit protected mode entry (called by bootloader)
 * 3. Page table setup for identity mapping + high-half mapping
 * 4. Transition to 64-bit long mode
 * 5. Jump to kernel main (main64)
 *
 * Memory Layout:
 * - Boot sections (.boot, .boot_text, .boot_data, .boot_bss) at 0x100000
 * - Kernel sections (.text, .data, .bss) at 0xFFFFFFFF80100000+
 */

#include "asm.h"

/* Multiboot2 constants */
#define MULTIBOOT2_HEADER_MAGIC     0xe85250d6
#define MULTIBOOT2_ARCHITECTURE_I386 0
#define MULTIBOOT2_HEADER_TAG_END   0
#define MULTIBOOT2_HEADER_TAG_ENTRY 3
#define MULTIBOOT2_HEADER_TAG_FLAGS 4

/* CR0 bits */
#define CR0_PE  0x00000001  /* Protected Enable */
#define CR0_PG  0x80000000  /* Paging */
#define CR0_WP  0x00010000  /* Write Protect */

/* CR4 bits */
#define CR4_PAE 0x00000020  /* Physical Address Extension */

/* EFER MSR */
#define MSR_EFER 0xC0000080
#define EFER_LME 0x00000100 /* Long Mode Enable */

/* Page table flags */
#define PTE_P   0x001  /* Present */
#define PTE_W   0x002  /* Writable */
#define PTE_PS  0x080  /* Page Size (2MB) */

/* High-half kernel base (must match linker script) */
#define KERNEL_VIRT_BASE 0xFFFFFFFF80000000

/* Serial port for boot diagnostics */
#define COM1_PORT 0x3F8

/* PVH (Para-Virtualized Hardware) ELF note constants */
#define XEN_ELFNOTE_PHYS32_ENTRY 18

/* ============================================================================
 * PVH ELF Note (for QEMU x86_64 -kernel direct boot)
 * QEMU's x86_64 kernel loader requires PVH note for 64-bit ELF
 * This note specifies the 32-bit physical entry point
 * ============================================================================ */

.section .note.Xen, "a", @note
.align 4
pvh_note:
    .long 4                         /* namesz: "Xen\0" = 4 bytes */
    .long 4                         /* descsz: 32-bit address = 4 bytes */
    .long XEN_ELFNOTE_PHYS32_ENTRY  /* type: XEN_ELFNOTE_PHYS32_ENTRY */
    .asciz "Xen"                    /* name: "Xen" with null terminator */
    .long multiboot2_entry          /* desc: 32-bit physical entry point */

/* ============================================================================
 * Multiboot2 Header (must be in first 32KB of kernel)
 * Placed in .multiboot section -> .boot in linker script
 * ============================================================================ */

.section .multiboot, "ax"
.align 8
multiboot2_header:
    .long MULTIBOOT2_HEADER_MAGIC
    .long MULTIBOOT2_ARCHITECTURE_I386
    .long (multiboot2_header_end - multiboot2_header)  /* header length */
    /* checksum: -(magic + arch + length) */
    .long -(MULTIBOOT2_HEADER_MAGIC + MULTIBOOT2_ARCHITECTURE_I386 + (multiboot2_header_end - multiboot2_header))

    /* Entry address tag - specifies 32-bit entry point */
    .align 8
    .word MULTIBOOT2_HEADER_TAG_ENTRY
    .word 0  /* flags */
    .long 12 /* size */
    .long multiboot2_entry  /* entry point (physical address) */

    /* End tag */
    .align 8
    .word MULTIBOOT2_HEADER_TAG_END
    .word 0
    .long 8
multiboot2_header_end:

/* ============================================================================
 * 32-bit Protected Mode Entry Point
 * Called by multiboot2-compliant bootloader (GRUB2, QEMU -kernel)
 * EAX = multiboot2 magic (0x36d76289)
 * EBX = physical address of multiboot2 info structure
 *
 * Placed in .boot_text section - stays at low physical address
 * ============================================================================ */

.section .boot_text, "ax"
.code32

/* Serial output helper - outputs character in AL */
serial_putc:
    movw $COM1_PORT, %dx
    addw $5, %dx         /* Line status register */
1:  inb %dx, %al
    testb $0x20, %al     /* TX ready? */
    jz 1b
    movw $COM1_PORT, %dx
    movb %bl, %al        /* Character to send */
    outb %al, %dx
    ret

.globl multiboot2_entry
multiboot2_entry:
    /* Save multiboot info pointer FIRST (before using %bl for serial) */
    movl %ebx, (multiboot_info_ptr)

    /* Output 'M' - Multiboot entry reached */
    movb $'M', %bl
    call serial_putc

    /* Disable interrupts */
    cli

    /* Clear segment registers */
    xorl %ecx, %ecx
    movw %cx, %ds
    movw %cx, %es
    movw %cx, %fs
    movw %cx, %gs
    movw %cx, %ss

    /* -----------------------------------------------------------------------
     * Set up page tables for:
     * 1. Identity mapping: 0x00000000 -> 0x00000000 (first 1GB)
     * 2. High-half mapping: 0xFFFFFFFF80000000 -> 0x00000000
     * ----------------------------------------------------------------------- */

    /* Clear page table area (4 pages = 16KB) */
    movl $boot_pml4, %edi
    xorl %eax, %eax
    movl $4096, %ecx  /* 4 pages * 4096 / 4 = 4096 dwords */
    rep stosl

    /* PML4[0] -> PDPT (identity mapping, first 512GB) */
    movl $boot_pml4, %edi
    movl $boot_pdpt, %eax
    orl $(PTE_P | PTE_W), %eax
    movl %eax, (%edi)

    /* PML4[511] -> PDPT (high-half mapping, last 512GB) */
    movl $boot_pml4, %edi
    addl $(511 * 8), %edi
    movl $boot_pdpt_high, %eax
    orl $(PTE_P | PTE_W), %eax
    movl %eax, (%edi)

    /* PDPT[0] -> PD (identity: maps 0x00000000-0x3FFFFFFF) */
    movl $boot_pdpt, %edi
    movl $boot_pd, %eax
    orl $(PTE_P | PTE_W), %eax
    movl %eax, (%edi)

    /* PDPT_high[510] -> PD (high-half: maps -2GB = 0xFFFFFFFF80000000) */
    movl $boot_pdpt_high, %edi
    addl $(510 * 8), %edi
    movl $boot_pd, %eax
    orl $(PTE_P | PTE_W), %eax
    movl %eax, (%edi)

    /* PD entries: map first 1GB using 2MB pages */
    movl $boot_pd, %edi
    movl $(PTE_P | PTE_W | PTE_PS), %eax  /* 2MB page at 0x00000000 */
    movl $512, %ecx  /* 512 entries * 2MB = 1GB */
1:
    movl %eax, (%edi)
    movl $0, 4(%edi)  /* Clear upper 32 bits */
    addl $0x200000, %eax  /* Next 2MB */
    addl $8, %edi
    loop 1b

    /* Output 'T' - Page Tables set up */
    movb $'T', %bl
    call serial_putc

    /* Enable PAE */
    movl %cr4, %eax
    orl $CR4_PAE, %eax
    movl %eax, %cr4

    /* Load PML4 into CR3 */
    movl $boot_pml4, %eax
    movl %eax, %cr3

    /* Enable long mode in EFER MSR */
    movl $MSR_EFER, %ecx
    rdmsr
    orl $EFER_LME, %eax
    wrmsr

    /* Output 'P' - About to enable Paging */
    movb $'P', %bl
    call serial_putc

    /* Enable paging (this activates long mode) */
    movl %cr0, %eax
    orl $(CR0_PE | CR0_PG | CR0_WP), %eax
    movl %eax, %cr0

    /* Load 64-bit GDT */
    lgdt (boot_gdt64_ptr)

    /* Far jump to 64-bit code segment
     * This jumps to the high-half address of long_mode_entry */
    ljmp $0x08, $long_mode_entry

/* ============================================================================
 * 64-bit Long Mode Entry
 * Now running with paging enabled, can use high-half addresses
 * ============================================================================ */

.code64
.globl long_mode_entry
long_mode_entry:
    /* Set up data segments */
    movw $0x10, %ax
    movw %ax, %ds
    movw %ax, %es
    movw %ax, %fs
    movw %ax, %gs
    movw %ax, %ss

    /* Set up initial stack (in boot BSS, identity mapped) */
    movq $boot_stack_top, %rsp

    /* Output 'L' - Long mode entered (inline serial output) */
    movw $COM1_PORT + 5, %dx
1:  inb %dx, %al
    testb $0x20, %al
    jz 1b
    movw $COM1_PORT, %dx
    movb $'L', %al
    outb %al, %dx

    /* Output newline for readability */
    movw $COM1_PORT + 5, %dx
2:  inb %dx, %al
    testb $0x20, %al
    jz 2b
    movw $COM1_PORT, %dx
    movb $'\n', %al
    outb %al, %dx

    /* Pass multiboot info pointer to kernel (zero-extend to 64-bit) */
    movl (multiboot_info_ptr), %edi

    /* Jump to kernel main64 (high-half address) */
    movabsq $main64, %rax
    jmp *%rax

    /* Should not return, but hang if it does */
1:  hlt
    jmp 1b

/* ============================================================================
 * Boot Data Structures
 * Placed in .boot_data section - stays at low physical address
 * ============================================================================ */

.section .boot_data, "aw"
.align 4
multiboot_info_ptr:
    .long 0

/* 64-bit GDT */
.align 16
boot_gdt64:
    SEG_NULLASM                         /* 0x00: null descriptor */
    SEG_ASM64(STA_X|STA_R, 0, 0xfffff)  /* 0x08: 64-bit code segment */
    SEG_ASM64(STA_W, 0, 0xfffff)        /* 0x10: 64-bit data segment */
boot_gdt64_end:

.align 4
boot_gdt64_ptr:
    .word boot_gdt64_end - boot_gdt64 - 1  /* limit */
    .quad boot_gdt64                        /* base (physical address) */

/* ============================================================================
 * Boot BSS - Page Tables and Stack
 * Placed in .boot_bss section - stays at low physical address
 * Must be aligned to 4KB for page tables
 * ============================================================================ */

.section .boot_bss, "aw", @nobits
.align 4096

/* Page Map Level 4 (PML4) - top level page table */
boot_pml4:
    .space 4096

/* Page Directory Pointer Table (PDPT) - for identity mapping */
boot_pdpt:
    .space 4096

/* Page Directory Pointer Table (PDPT) - for high-half mapping */
boot_pdpt_high:
    .space 4096

/* Page Directory (PD) - shared between identity and high-half */
boot_pd:
    .space 4096

/* Boot stack (16KB) */
.align 16
boot_stack_bottom:
    .space 16384
boot_stack_top:

/* ============================================================================
 * External symbol references
 * ============================================================================ */

.extern main64
