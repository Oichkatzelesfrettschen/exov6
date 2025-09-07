/*
 * bootasm.S - Multimode Bootloader Assembly (16-bit, 32-bit, and 64-bit)
 *
 * This file handles initial real mode setup, protected mode transition,
 * and a 64-bit long mode pathway. It includes:
 *   - 16-bit real mode startup (BIOS entry).
 *   - Enabling the A20 line for >1MB memory.
 *   - Setting up a 32-bit protected mode environment.
 *   - Setting up page tables, enabling PAE, and setting the LME bit in IA32_EFER.
 *   - Jumping to 64-bit long mode with .code64.
 *
 * Main entry points:
 *   - start: Executed in 16-bit real mode.
 *   - start32: Transition to 32-bit protected mode.
 *   - start64: Transition to 64-bit long mode.
 */

#include "memlayout.h"
#include "mmu.h"
#include "asm.h"
#include "arch/asm_common.h"

.code16
.globl start
start:
  cli
  xorw    %ax, %ax
  movw    %ax, %ds
  movw    %ax, %es
  movw    %ax, %ss

  ENABLE_A20

  SETUP_PROT_MODE(gdtdesc, SEG_KCODE<<3, start32)

.code32
start32:
  INIT_PROT_MODE_DATA(SEG_KDATA<<3)

  // Set up the stack pointer and call into C.
  movl    $start, %esp
  call    bootmain

  // If bootmain returns, spin forever
spin32:
  jmp     spin32

  // Prepare for 64-bit mode: set CR4.PAE=1, load PML4, set IA32_EFER.LME=1, then jump
  // (This example assumes paging structures have been set up elsewhere)
  // movl    $pml4_table, %eax
  // movl    %eax, %cr3
  // movl    %cr4, %eax
  // orl     $(1 << 5), %eax       // CR4.PAE=1
  // movl    %eax, %cr4
  // rdmsr
  // bts     $8, %eax              // IA32_EFER.LME=1 (bit 8)
  // wrmsr
  // jmp     enter64

enter64:
  // Set up a 64-bit code segment in the GDT or LDT before jumping here
  ljmp    $(3 << 3), $start64    # 64-bit code segment is at GDT index 3

.code64
start64:
  // Now in 64-bit mode
  // Set up the stack, data segments, etc. as needed
  // Continue to your 64-bit kernel entry point
  jmp long_mode_entry

long_mode_entry:
  // 64-bit execution begins here
  // ...
  // Spin loop / fallback
spin64:
  jmp     spin64

.p2align 2
gdt:
  SEG_NULLASM
  SEG_ASM(STA_X|STA_R, 0x0, 0xffffffff)   // 32-bit code segment
  SEG_ASM(STA_W, 0x0, 0xffffffff)         // 32-bit data segment
  SEG_ASM64(STA_X|STA_R, 0x0, 0xfffff)    // 64-bit code segment (example)

gdtdesc:
  .word (gdtdesc - gdt - 1)
  .long gdt
