#pragma once

// x86_64 Architecture Synthesis Layer - Clean, Non-Conflicting Implementation
// This file provides the complete x86_64 architecture interface without conflicts

#ifdef __x86_64__

#include <stdint.h>
#include <stdbool.h>
#include "memlayout.h"  // For PGSIZE and memory constants

// Register types
typedef uint64_t arch_reg_t;
typedef uint64_t pde_t;
typedef uint64_t pte_t;
typedef uint64_t pml4e_t;

// Memory constants defined in memlayout.h

// Segment selectors
#define SEG_KCODE 1
#define SEG_KDATA 2
#define SEG_UCODE 3
#define SEG_UDATA 4
#define SEG_TSS   5
#define DPL_USER  0x3

// RFLAGS register bits
#define FL_IF 0x00000200  // Interrupt Enable

// Context for kernel thread switching (matches swtch.S)
#ifndef CONTEXT64_DEFINED
#define CONTEXT64_DEFINED
struct context64 {
  uint64_t r15;
  uint64_t r14;
  uint64_t r13;
  uint64_t r12;
  uint64_t rbx;
  uint64_t rbp;
  uint64_t rip;
};
#endif

// Trap frame for interrupts and system calls
#ifndef TRAPFRAME_DEFINED
#define TRAPFRAME_DEFINED
struct trapframe {
  // Pushed by entry code
  uint64_t r15, r14, r13, r12, r11, r10, r9, r8;
  uint64_t rdi, rsi, rbp, rbx, rdx, rcx, rax;
  
  // Trap information
  uint64_t trapno;
  uint64_t err;
  
  // Hardware-pushed frame
  uint64_t rip;
  uint64_t cs;
  uint64_t rflags;
  uint64_t rsp;
  uint64_t ss;
} __attribute__((packed));
#endif

// I/O port operations - only define if not already defined
#ifndef _ARCH_IO_FUNCTIONS_DEFINED
#define _ARCH_IO_FUNCTIONS_DEFINED

static inline uint8_t inb(uint16_t port) {
  uint8_t data;
  __asm__ volatile("inb %w1, %b0" : "=a"(data) : "Nd"(port));
  return data;
}

static inline void outb(uint16_t port, uint8_t data) {
  __asm__ volatile("outb %b0, %w1" : : "a"(data), "Nd"(port));
}

static inline uint16_t inw(uint16_t port) {
  uint16_t data;
  __asm__ volatile("inw %w1, %w0" : "=a"(data) : "Nd"(port));
  return data;
}

static inline void outw(uint16_t port, uint16_t data) {
  __asm__ volatile("outw %w0, %w1" : : "a"(data), "Nd"(port));
}

static inline uint32_t inl(uint16_t port) {
  uint32_t data;
  __asm__ volatile("inl %w1, %0" : "=a"(data) : "Nd"(port));
  return data;
}

static inline void outl(uint16_t port, uint32_t data) {
  __asm__ volatile("outl %0, %w1" : : "a"(data), "Nd"(port));
}

// Bulk I/O operations
static inline void insl(int port, void *addr, int cnt) {
  __asm__ volatile("cld; rep insl"
                   : "=D"(addr), "=c"(cnt)
                   : "d"(port), "0"(addr), "1"(cnt)
                   : "memory", "cc");
}

static inline void outsl(int port, const void *addr, int cnt) {
  __asm__ volatile("cld; rep outsl"
                   : "=S"(addr), "=c"(cnt)
                   : "d"(port), "0"(addr), "1"(cnt)
                   : "cc");
}

// Guard functions that may conflict with x86.h
#ifndef _ARCH_X86_ADDITIONAL_DEFINED
#define _ARCH_X86_ADDITIONAL_DEFINED

// Interrupt control
static inline void cli(void) {
  __asm__ volatile("cli" ::: "memory");
}

static inline void sti(void) {
  __asm__ volatile("sti" ::: "memory");
}

static inline void hlt(void) {
  __asm__ volatile("hlt");
}

static inline void pause(void) {
  __asm__ volatile("pause");
}

// Flags register access
static inline uint64_t read_rflags(void) {
  uint64_t flags;
  __asm__ volatile("pushfq; popq %0" : "=r"(flags) : : "memory");
  return flags;
}

static inline void write_rflags(uint64_t flags) {
  __asm__ volatile("pushq %0; popfq" : : "r"(flags) : "memory", "cc");
}

// Control register access
static inline uint64_t read_cr0(void) {
  uint64_t val;
  __asm__ volatile("movq %%cr0, %0" : "=r"(val));
  return val;
}

static inline void write_cr0(uint64_t val) {
  __asm__ volatile("movq %0, %%cr0" : : "r"(val) : "memory");
}

static inline uint64_t read_cr2(void) {
  uint64_t val;
  __asm__ volatile("movq %%cr2, %0" : "=r"(val));
  return val;
}

static inline uint64_t read_cr3(void) {
  uint64_t val;
  __asm__ volatile("movq %%cr3, %0" : "=r"(val));
  return val;
}

static inline void write_cr3(uint64_t val) {
  __asm__ volatile("movq %0, %%cr3" : : "r"(val) : "memory");
}

static inline uint64_t read_cr4(void) {
  uint64_t val;
  __asm__ volatile("movq %%cr4, %0" : "=r"(val));
  return val;
}

static inline void write_cr4(uint64_t val) {
  __asm__ volatile("movq %0, %%cr4" : : "r"(val) : "memory");
}

// TLB management
static inline void invlpg(const void *addr) {
  __asm__ volatile("invlpg (%0)" : : "r"(addr) : "memory");
}

// Memory barriers
static inline void mfence(void) {
  __asm__ volatile("mfence" ::: "memory");
}

static inline void lfence(void) {
  __asm__ volatile("lfence" ::: "memory");
}

static inline void sfence(void) {
  __asm__ volatile("sfence" ::: "memory");
}

// Atomic operations
static inline uint64_t xchg64(volatile uint64_t *ptr, uint64_t val) {
  __asm__ volatile("xchgq %0, %1"
                   : "+m"(*ptr), "+r"(val)
                   :
                   : "memory");
  return val;
}

static inline uint32_t xchg(volatile uint32_t *ptr, uint32_t val) {
  __asm__ volatile("xchgl %0, %1"
                   : "+m"(*ptr), "+r"(val)
                   :
                   : "memory");
  return val;
}

#endif /* _ARCH_X86_ADDITIONAL_DEFINED */

// String operations
static inline void stosb(void *addr, int data, int cnt) {
  __asm__ volatile("cld; rep stosb"
                   : "=D"(addr), "=c"(cnt)
                   : "0"(addr), "1"(cnt), "a"(data)
                   : "memory", "cc");
}

static inline void stosl(void *addr, int data, int cnt) {
  __asm__ volatile("cld; rep stosl"
                   : "=D"(addr), "=c"(cnt)
                   : "0"(addr), "1"(cnt), "a"(data)
                   : "memory", "cc");
}

static inline void stosq(void *addr, uint64_t data, int cnt) {
  __asm__ volatile("cld; rep stosq"
                   : "=D"(addr), "=c"(cnt)
                   : "0"(addr), "1"(cnt), "a"(data)
                   : "memory", "cc");
}

#endif /* _ARCH_IO_FUNCTIONS_DEFINED */

// CPUID instruction (named x86_cpuid to avoid conflict with kernel cpuid())
static inline void x86_cpuid(uint32_t leaf, uint32_t *eax, uint32_t *ebx,
                             uint32_t *ecx, uint32_t *edx) {
  __asm__ volatile("cpuid"
                   : "=a"(*eax), "=b"(*ebx), "=c"(*ecx), "=d"(*edx)
                   : "a"(leaf));
}

// MSR access
static inline uint64_t rdmsr(uint32_t msr) {
  uint32_t low, high;
  __asm__ volatile("rdmsr" : "=a"(low), "=d"(high) : "c"(msr));
  return ((uint64_t)high << 32) | low;
}

static inline void wrmsr(uint32_t msr, uint64_t val) {
  uint32_t low = val & 0xFFFFFFFF;
  uint32_t high = val >> 32;
  __asm__ volatile("wrmsr" : : "a"(low), "d"(high), "c"(msr));
}

// GDT/IDT operations - 2-argument form (guarded to prevent conflict with arch.h)
#ifndef _ARCH_GDT_IDT_DEFINED
#define _ARCH_GDT_IDT_DEFINED
static inline void lgdt(void *p, int size) {
  struct {
    uint16_t limit;
    uint64_t base;
  } __attribute__((packed)) gdtr;
  gdtr.limit = size - 1;
  gdtr.base = (uint64_t)p;
  __asm__ volatile("lgdt %0" : : "m"(gdtr) : "memory");
}

static inline void lidt(void *p, int size) {
  struct {
    uint16_t limit;
    uint64_t base;
  } __attribute__((packed)) idtr;
  idtr.limit = size - 1;
  idtr.base = (uint64_t)p;
  __asm__ volatile("lidt %0" : : "m"(idtr) : "memory");
}

static inline void ltr(uint16_t sel) {
  __asm__ volatile("ltr %w0" : : "r"(sel) : "memory");
}
#endif /* _ARCH_GDT_IDT_DEFINED */

// Fast system call support
static inline void swapgs(void) {
  __asm__ volatile("swapgs");
}

// Compatibility aliases
#define readeflags() read_rflags()
#define read_flags() read_rflags()
#define lcr3(val) write_cr3(val)
#define rcr3() read_cr3()
#define rcr2() read_cr2()

// ============================================================================
// 64-bit IDT Gate Descriptors
// ============================================================================

// Gate types for 64-bit mode
#define STS_IG64 0xE  // 64-bit Interrupt Gate
#define STS_TG64 0xF  // 64-bit Trap Gate

// 64-bit gate descriptor (16 bytes per entry)
struct gatedesc64 {
    uint16_t off_15_0;    // Offset bits 0-15
    uint16_t cs;          // Code segment selector
    uint8_t  ist : 3;     // Interrupt Stack Table offset
    uint8_t  rsv0 : 5;    // Reserved (must be 0)
    uint8_t  type : 4;    // Gate type (IG64 or TG64)
    uint8_t  s : 1;       // Must be 0 for system segment
    uint8_t  dpl : 2;     // Descriptor privilege level
    uint8_t  p : 1;       // Present
    uint16_t off_31_16;   // Offset bits 16-31
    uint32_t off_63_32;   // Offset bits 32-63
    uint32_t rsv1;        // Reserved (must be 0)
} __attribute__((packed));

// Set up a 64-bit interrupt/trap gate descriptor
// istrap: 1 for trap gate, 0 for interrupt gate (clears IF)
// sel: code segment selector
// off: 64-bit handler address
// d: descriptor privilege level
#define SETGATE64(gate, istrap, sel, off, d)                              \
    do {                                                                   \
        uint64_t _off = (uint64_t)(off);                                  \
        (gate).off_15_0 = _off & 0xFFFF;                                  \
        (gate).cs = (sel);                                                \
        (gate).ist = 0;                                                   \
        (gate).rsv0 = 0;                                                  \
        (gate).type = (istrap) ? STS_TG64 : STS_IG64;                     \
        (gate).s = 0;                                                     \
        (gate).dpl = (d);                                                 \
        (gate).p = 1;                                                     \
        (gate).off_31_16 = (_off >> 16) & 0xFFFF;                         \
        (gate).off_63_32 = _off >> 32;                                    \
        (gate).rsv1 = 0;                                                  \
    } while (0)

// External vectors array (defined in vectors64.S)
extern uint64_t vectors[];

#endif // __x86_64__