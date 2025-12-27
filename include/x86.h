#pragma once

#include <stdint.h>
#include <stddef.h>

// Type definitions for compatibility
// Removed redundant typedef for uchar. Use unsigned char directly.
typedef unsigned short ushort;
typedef unsigned int uint;
// Removed typedef for uint64 to align with standard naming conventions
typedef uintptr_t uintptr;

// Architecture detection and sizing
#ifdef __x86_64__
#define ARCH_BITS 64
#define WORD_SIZE 8
typedef uint64_t arch_word_t;
typedef uint64_t arch_reg_t;
#define PUSH_INSTR "pushq"
#define POP_INSTR "popq"
#define MOV_INSTR "movq"
#define REG_PREFIX "%%r"
#define ADDR_CONSTRAINT "r"
#elif defined(__i386__)
#define ARCH_BITS 32
#define WORD_SIZE 4
typedef uint32_t arch_word_t;
typedef uint32_t arch_reg_t;
#define PUSH_INSTR "pushl"
#define POP_INSTR "popl"
#define MOV_INSTR "movl"
#define REG_PREFIX "%%e"
#define ADDR_CONSTRAINT "r"
#else
// Default to 64-bit for unknown architectures
#define ARCH_BITS 64
#define WORD_SIZE 8
typedef uint64_t arch_word_t;
typedef uint64_t arch_reg_t;
#define PUSH_INSTR "pushq"
#define POP_INSTR "popq"
#define MOV_INSTR "movq"
#define REG_PREFIX "%%r"
#define ADDR_CONSTRAINT "r"
#endif

// =============================================================================
// I/O PORT OPERATIONS MODULE
// =============================================================================

// Guard against redefinition when included with arch.h
#ifndef _ARCH_IO_FUNCTIONS_DEFINED
#define _ARCH_IO_FUNCTIONS_DEFINED

static inline unsigned char inb(ushort port) {
  unsigned char data;
  __asm__ volatile("inb %w1, %b0" : "=a"(data) : "Nd"(port) : "memory");
  return data;
}

static inline ushort inw(ushort port) {
  ushort data;
  __asm__ volatile("inw %w1, %w0" : "=a"(data) : "Nd"(port) : "memory");
  return data;
}

static inline uint inl(ushort port) {
  uint data;
  __asm__ volatile("inl %w1, %0" : "=a"(data) : "Nd"(port) : "memory");
  return data;
}

static inline void outb(ushort port, unsigned char data) {
  __asm__ volatile("outb %b0, %w1" : : "a"(data), "Nd"(port) : "memory");
}

static inline void outw(ushort port, ushort data) {
  __asm__ volatile("outw %w0, %w1" : : "a"(data), "Nd"(port) : "memory");
}

static inline void outl(ushort port, uint data) {
  __asm__ volatile("outl %0, %w1" : : "a"(data), "Nd"(port) : "memory");
}

// =============================================================================
// BULK DATA TRANSFER MODULE
// =============================================================================

static inline void insl(int port, void *addr, int cnt) {
  __asm__ volatile("cld\n\t"
                   "rep insl"
                   : "=D"(addr), "=c"(cnt)
                   : "d"(port), "0"(addr), "1"(cnt)
                   : "memory", "cc");
}

static inline void outsw(int port, const void *addr, int cnt) {
  __asm__ volatile("cld\n\t"
                   "rep outsw"
                   : "=S"(addr), "=c"(cnt)
                   : "d"(port), "0"(addr), "1"(cnt)
                   : "cc");
}

static inline void outsl(int port, const void *addr, int cnt) {
  __asm__ volatile("cld\n\t"
                   "rep outsl"
                   : "=S"(addr), "=c"(cnt)
                   : "d"(port), "0"(addr), "1"(cnt)
                   : "cc");
}

// =============================================================================
// MEMORY OPERATIONS MODULE
// =============================================================================

static inline void stosb(void *addr, int data, int cnt) {
  __asm__ volatile("cld\n\t"
                   "rep stosb"
                   : "=D"(addr), "=c"(cnt)
                   : "0"(addr), "1"(cnt), "a"(data)
                   : "memory", "cc");
}
static inline void stosl(void *addr, int data, int cnt) {
  __asm__ volatile("cld\n\t"
                   "rep stosl"
                   : "=D"(addr), "=c"(cnt)
                   : "0"(addr), "1"(cnt), "a"(data)
                   : "memory", "cc");
}

#endif /* _ARCH_IO_FUNCTIONS_DEFINED */

static inline void memcpy_fast(void *dst, const void *src, size_t cnt) {
#ifdef __x86_64__
  __asm__ volatile("cld\n\t"
                   "rep movsq"
                   : "=D"(dst), "=S"(src), "=c"(cnt)
                   : "0"(dst), "1"(src), "2"(cnt / 8)
                   : "memory", "cc");
  if (cnt % 8) {
    __asm__ volatile("rep movsb"
                     : "=D"(dst), "=S"(src), "=c"(cnt)
                     : "0"(dst), "1"(src), "2"(cnt % 8)
                     : "memory", "cc");
  }
#else
  __asm__ volatile("cld\n\t"
                   "rep movsb"
                   : "=D"(dst), "=S"(src), "=c"(cnt)
                   : "0"(dst), "1"(src), "2"(cnt)
                   : "memory", "cc");
#endif
}

// =============================================================================
// DESCRIPTOR TABLE OPERATIONS MODULE
// =============================================================================

// Forward declarations
struct segdesc;
struct gatedesc;

// Guard against redefinition when included with arch.h
#ifndef _ARCH_GDT_IDT_DEFINED
#define _ARCH_GDT_IDT_DEFINED

static inline void lgdt(struct segdesc *p, int size) {
  struct {
    uint16_t limit;
    arch_word_t base;
  } __attribute__((packed)) gdtr;

  gdtr.limit = size - 1;
  gdtr.base = (arch_word_t)(uintptr_t)p;

  __asm__ volatile("lgdt %0" : : "m"(gdtr) : "memory");
}

static inline void lidt(struct gatedesc *p, int size) {
  struct {
    uint16_t limit;
    arch_word_t base;
  } __attribute__((packed)) idtr;

  idtr.limit = size - 1;
  idtr.base = (arch_word_t)(uintptr_t)p;

  __asm__ volatile("lidt %0" : : "m"(idtr) : "memory");
}

static inline void ltr(ushort sel) {
  __asm__ volatile("ltr %w0" : : "r"(sel) : "memory");
}

#endif /* _ARCH_GDT_IDT_DEFINED */

// =============================================================================
// TIMESTAMP AND PERFORMANCE MODULE (Always included, not guarded)
// =============================================================================
#ifndef _RDTSC_FUNCTIONS_DEFINED
#define _RDTSC_FUNCTIONS_DEFINED
static inline uint64_t rdtscp(uint32_t *aux) {
  uint32_t low, high;
  if (aux) {
    __asm__ volatile("rdtscp" : "=a"(low), "=d"(high), "=c"(*aux) : : "memory");
  } else {
    __asm__ volatile("rdtscp" : "=a"(low), "=d"(high) : : "memory");
  }
  return ((uint64_t)high << 32) | low;
}

static inline uint64_t rdtsc(void) {
  uint32_t low, high;
  __asm__ volatile("rdtsc" : "=a"(low), "=d"(high) : : "memory");
  return ((uint64_t)high << 32) | low;
}
#endif /* _RDTSC_FUNCTIONS_DEFINED */

// Guard additional x86 functions that may be defined in arch_x86_64.h
#ifndef _ARCH_X86_ADDITIONAL_DEFINED
#define _ARCH_X86_ADDITIONAL_DEFINED

// Skip read_flags if arch_x86_64.h already defined it as a macro
#ifndef read_flags
static inline arch_reg_t read_flags(void) {
  arch_reg_t flags;
#ifdef __x86_64__
  __asm__ volatile(PUSH_INSTR " %%rflags\n\t" POP_INSTR " %0"
                   : "=r"(flags)
                   :
                   : "memory");
#else
  __asm__ volatile(PUSH_INSTR " %%eflags\n\t" POP_INSTR " %0"
                   : "=r"(flags)
                   :
                   : "memory");
#endif
  return flags;
}
#endif /* read_flags macro guard */

static inline void write_flags(arch_reg_t flags) {
#if ARCH_BITS == 64
  __asm__ volatile(PUSH_INSTR " %0\n\t"
                              "popfq"
                   :
                   : "r"(flags)
                   : "memory", "cc");
#elif ARCH_BITS == 32
  __asm__ volatile(PUSH_INSTR " %0\n\t"
                              "popfd"
                   :
                   : "r"(flags)
                   : "memory", "cc");
#endif
}

static inline void cli(void) { __asm__ volatile("cli" ::: "memory"); }

static inline void sti(void) { __asm__ volatile("sti" ::: "memory"); }

static inline void hlt(void) { __asm__ volatile("hlt" ::: "memory"); }

static inline void pause(void) { __asm__ volatile("pause" ::: "memory"); }

// =============================================================================
// SEGMENT REGISTER OPERATIONS MODULE
// =============================================================================

static inline void load_gs(ushort v) {
  __asm__ volatile("movw %w0, %%gs" : : "q"(v) : "memory");
}

static inline void load_fs(ushort v) {
  __asm__ volatile("movw %w0, %%fs" : : "q"(v) : "memory");
}

static inline ushort read_cs(void) {
  ushort cs;
  __asm__ volatile("movw %%cs, %w0" : "=q"(cs) : : "memory");
  return cs;
}

// Note: The `xchg` function assumes that the memory address is aligned.
// Non-aligned memory addresses may not ensure atomicity and can lead to
// undefined behavior.
static inline uint xchg(volatile uint *addr, uint newval) {
  uint result;
  __asm__ volatile("lock xchgl %0, %1"
                   : "+m"(*addr), "=a"(result)
                   : "1"(newval)
                   : "cc", "memory");
  return result;
}

static inline arch_word_t xchg_ptr(volatile arch_word_t *addr,
                                   arch_word_t newval) {
  arch_word_t result;
  __asm__ volatile("lock " MOV_INSTR " %0, %1"
                   : "+m"(*addr), "=a"(result)
                   : "1"(newval)
                   : "cc", "memory");
  return result;
}

static inline uint cmpxchg(volatile uint *addr, uint oldval, uint newval) {
  uint result;
  __asm__ volatile("lock cmpxchgl %2, %1"
                   : "=a"(result), "+m"(*addr)
                   : "r"(newval), "0"(oldval)
                   : "cc", "memory");
  return result;
}

// =============================================================================
// CONTROL REGISTER OPERATIONS MODULE
// =============================================================================

static inline arch_word_t read_cr0(void) {
  arch_word_t val;
  __asm__ volatile(MOV_INSTR " %%cr0, %0" : "=r"(val) : : "memory");
  return val;
}

static inline void write_cr0(arch_word_t val) {
  __asm__ volatile(MOV_INSTR " %0, %%cr0" : : "r"(val) : "memory");
}

static inline arch_word_t read_cr2(void) {
  arch_word_t val;
  __asm__ volatile(MOV_INSTR " %%cr2, %0" : "=r"(val) : : "memory");
  return val;
}

static inline arch_word_t read_cr3(void) {
  arch_word_t val;
  __asm__ volatile(MOV_INSTR " %%cr3, %0" : "=r"(val) : : "memory");
  return val;
}

static inline void write_cr3(arch_word_t val) {
  __asm__ volatile(MOV_INSTR " %0, %%cr3" : : "r"(val) : "memory");
}

static inline arch_word_t read_cr4(void) {
  arch_word_t val;
  __asm__ volatile(MOV_INSTR " %%cr4, %0" : "=r"(val) : : "memory");
  return val;
}

static inline void write_cr4(arch_word_t val) {
  __asm__ volatile(MOV_INSTR " %0, %%cr4" : : "r"(val) : "memory");
}

// =============================================================================
// MEMORY MANAGEMENT MODULE
// =============================================================================

// The `addr` parameter must be a valid memory address aligned to page
// boundaries. Passing an invalid or unaligned address may result in undefined
// behavior.
static inline void invlpg(const void *addr) {
  __asm__ volatile("invlpg (%0)" : : "r"(addr) : "memory");
}

static inline void flush_tlb(void) { write_cr3(read_cr3()); }

// The `cpuid` function retrieves information about the CPU based on the `leaf`
// parameter.
// - `leaf`: Specifies the information to retrieve (e.g., 0 for vendor ID, 1 for
// feature flags).
// - `eax`, `ebx`, `ecx`, `edx`: Output registers containing the requested
// information.
static inline void cpuid(uint leaf, uint *eax, uint *ebx, uint *ecx,
                         uint *edx) {
  __asm__ volatile("cpuid"
                   : "=a"(*eax), "=b"(*ebx), "=c"(*ecx), "=d"(*edx)
                   : "a"(leaf)
                   : "memory");
}

// =============================================================================
// TRAP FRAME STRUCTURES
// =============================================================================

#ifdef __x86_64__
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
#else
struct trapframe {
  // Pushed by pusha
  uint32_t edi, esi, ebp, oesp;
  uint32_t ebx, edx, ecx, eax;

  // Segment registers
  uint16_t gs, padding1;
  uint16_t fs, padding2;
  uint16_t es, padding3;
  uint16_t ds, padding4;

  // Trap information
  uint32_t trapno;

  // Hardware-pushed frame
  uint32_t err;
  uint32_t eip;
  uint16_t cs, padding5;
  uint32_t eflags;

  // Ring transition
  uint32_t esp;
  uint16_t ss, padding6;
} __attribute__((packed));
#endif
// Legacy compatibility aliases for
// register operations. These
// aliases are provided for backward
// compatibility with older
// codebases. `rcr3()` reads the
// value of the CR3 register (page
// directory base register).
#define rcr3() read_cr3()

// `rcr2()` reads the value of the
// CR2 register (page fault linear
// address).
#define rcr2() read_cr2()

// `loadgs(v)` loads the value `v`
// into the GS segment register.
#define loadgs(v) load_gs(v)

#endif /* _ARCH_X86_ADDITIONAL_DEFINED */
