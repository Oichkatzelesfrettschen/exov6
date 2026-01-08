/*
 * multiboot2.S - Multiboot2 Header and 32-to-64-bit Boot Trampoline
 *
 * This file provides:
 * 1. Multiboot2 header for QEMU -kernel boot
 * 2. 32-bit protected mode entry (called by bootloader)
 * 3. Page table setup for identity mapping
 * 4. Transition to 64-bit long mode
 * 5. Jump to kernel main (main64)
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

/* ============================================================================
 * Multiboot2 Header (must be in first 32KB of kernel)
 * ============================================================================ */

.section .multiboot, "ax"
.align 8
multiboot2_header:
    .long MULTIBOOT2_HEADER_MAGIC
    .long MULTIBOOT2_ARCHITECTURE_I386
    .long (multiboot2_header_end - multiboot2_header)  /* header length */
    /* checksum: -(magic + arch + length) */
    .long -(MULTIBOOT2_HEADER_MAGIC + MULTIBOOT2_ARCHITECTURE_I386 + (multiboot2_header_end - multiboot2_header))

    /* Entry address tag (optional, use if not using ELF entry) */
    .align 8
    .word MULTIBOOT2_HEADER_TAG_ENTRY
    .word 0  /* flags */
    .long 12 /* size */
    .long multiboot2_entry  /* entry point */

    /* End tag */
    .align 8
    .word MULTIBOOT2_HEADER_TAG_END
    .word 0
    .long 8
multiboot2_header_end:

/* ============================================================================
 * 32-bit Protected Mode Entry Point
 * Called by multiboot2-compliant bootloader
 * EAX = multiboot2 magic (0x36d76289)
 * EBX = physical address of multiboot2 info structure
 * ============================================================================ */

.section .text
.code32
.globl multiboot2_entry
multiboot2_entry:
    /* Save multiboot info pointer */
    movl %ebx, multiboot_info_ptr

    /* Disable interrupts */
    cli

    /* Clear segment registers */
    xorl %ecx, %ecx
    movw %cx, %ds
    movw %cx, %es
    movw %cx, %fs
    movw %cx, %gs
    movw %cx, %ss

    /* Set up minimal page tables for identity mapping */
    /* Clear page table area */
    movl $boot_pml4, %edi
    xorl %eax, %eax
    movl $4096, %ecx  /* 4 pages * 4096 / 4 = 4096 dwords */
    rep stosl

    /* PML4[0] -> PDPT */
    movl $boot_pml4, %edi
    movl $boot_pdpt, %eax
    orl $(PTE_P | PTE_W), %eax
    movl %eax, (%edi)

    /* PDPT[0] -> PD */
    movl $boot_pdpt, %edi
    movl $boot_pd, %eax
    orl $(PTE_P | PTE_W), %eax
    movl %eax, (%edi)

    /* PD entries: identity map first 4GB using 2MB pages */
    movl $boot_pd, %edi
    movl $(PTE_P | PTE_W | PTE_PS), %eax  /* 2MB page at 0x00000000 */
    movl $512, %ecx  /* 512 entries * 2MB = 1GB */
1:
    movl %eax, (%edi)
    addl $0x200000, %eax  /* Next 2MB */
    addl $8, %edi
    loop 1b

    /* Also map kernel high-half (0xFFFFFFFF80000000) */
    /* This requires additional page table entries for virtual addresses */

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

    /* Enable paging and protected mode */
    movl %cr0, %eax
    orl $(CR0_PE | CR0_PG | CR0_WP), %eax
    movl %eax, %cr0

    /* Load 64-bit GDT */
    lgdt boot_gdt64_ptr

    /* Far jump to 64-bit code segment */
    ljmp $0x08, $long_mode_entry

/* ============================================================================
 * 64-bit Long Mode Entry
 * ============================================================================ */

.code64
long_mode_entry:
    /* Set up data segments */
    movw $0x10, %ax
    movw %ax, %ds
    movw %ax, %es
    movw %ax, %fs
    movw %ax, %gs
    movw %ax, %ss

    /* Set up initial stack */
    movq $boot_stack_top, %rsp

    /* Clear BSS (optional, depends on linker script) */

    /* Pass multiboot info pointer to kernel */
    movl multiboot_info_ptr(%rip), %edi

    /* Jump to kernel main */
    movq $main64, %rax
    jmp *%rax

    /* Should not return, but hang if it does */
1:  hlt
    jmp 1b

/* ============================================================================
 * Data Structures
 * ============================================================================ */

.section .data
.align 4
multiboot_info_ptr:
    .long 0

/* 64-bit GDT */
.align 16
boot_gdt64:
    SEG_NULLASM                         /* 0x00: null */
    SEG_ASM64(STA_X|STA_R, 0, 0xfffff)  /* 0x08: code */
    SEG_ASM64(STA_W, 0, 0xfffff)        /* 0x10: data */
boot_gdt64_end:

boot_gdt64_ptr:
    .word boot_gdt64_end - boot_gdt64 - 1
    .quad boot_gdt64

/* ============================================================================
 * Page Tables (identity mapped, aligned to 4KB)
 * ============================================================================ */

.section .bss
.align 4096
boot_pml4:
    .space 4096
boot_pdpt:
    .space 4096
boot_pd:
    .space 4096
boot_pt:
    .space 4096

/* Boot stack */
.align 16
boot_stack_bottom:
    .space 16384  /* 16KB stack */
boot_stack_top:

/* ============================================================================
 * External symbol references
 * ============================================================================ */

.extern main64
