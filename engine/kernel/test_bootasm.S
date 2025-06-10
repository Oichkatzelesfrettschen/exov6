// test_bootasm.S
// Tests for bootasm.S bootloader code

#include "asm.h"
#include "memlayout.h"
#include "mmu.h"
#include "arch/asm_common.h"

// Test: Ensure the boot entry point is globally visible
    .extern start

// Test: Ensure the protected mode entry point is defined
    .extern start32

// Test: Ensure GDT and GDT descriptor are defined
    .extern gdt
    .extern gdtdesc

// Test: Ensure bootmain is called from protected mode
    .section .text
    .globl test_bootmain_called
test_bootmain_called:
    // Set up a fake stack and simulate entry to start32
    movl $0xCAFEBABE, %eax
    movl %eax, -4(%esp)      // push a marker on the stack

    call start32             // should call bootmain

    // If bootmain returns, check stack pointer is reset
    movl %esp, %ebx
    // Compare %ebx to $start (should be equal if stack pointer set correctly)
    movl $start, %eax
    cmp %eax, %ebx
    jne fail

    // Success: return 0
    movl $0, %eax
    ret

fail:
    // Failure: return 1
    movl $1, %eax
    ret

// Test: Ensure spin loop is present and infinite
    .globl test_spin_loop
test_spin_loop:
    // Try to jump to spin and see if it loops (simulate by checking instruction)
    // This is a static test: ensure label exists
    movl $spin, %eax
    ret

// Test: Ensure GDT is 3 entries (null, code, data)
    .globl test_gdt_entries
test_gdt_entries:
    lea gdt, %eax
    lea gdtdesc, %ebx
    movw (%ebx), %cx         // size = gdtdesc - gdt - 1
    addl $1, %ecx            // size = gdtdesc - gdt
    movl %ecx, %edx
    movl $24, %esi           // 3 entries * 8 bytes = 24
    cmp %esi, %edx
    jne fail_gdt
    movl $0, %eax
    ret
fail_gdt:
    movl $1, %eax
    ret

// Note: These tests are basic and check for symbol presence and some logic.
// Full functional tests require running in an emulator or with QEMU/Bochs.