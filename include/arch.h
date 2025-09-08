#pragma once

// Architecture-specific definitions with ARM64 compatibility
// Replaces x86-specific code with portable implementations

#include <stdint.h>
#include <stdbool.h>

#ifdef __aarch64__
// ARM64 definitions
typedef uint64_t arch_word_t;
typedef uint64_t reg_t;

// ARM64 stubs for x86 assembly functions
static inline void cli(void) { /* ARM64 equivalent: MSR DAIFSET, #2 */ }
static inline void sti(void) { /* ARM64 equivalent: MSR DAIFCLR, #2 */ }
static inline uint8_t inb(uint16_t port) { (void)port; return 0; }
static inline void outb(uint16_t port, uint8_t data) { (void)port; (void)data; }
static inline uint16_t inw(uint16_t port) { (void)port; return 0; }
static inline void outw(uint16_t port, uint16_t data) { (void)port; (void)data; }
static inline uint32_t inl(uint16_t port) { (void)port; return 0; }
static inline void outl(uint16_t port, uint32_t data) { (void)port; (void)data; }

// Memory barriers
static inline void mfence(void) { __asm__ volatile("dmb sy" ::: "memory"); }
static inline void lfence(void) { __asm__ volatile("dmb ld" ::: "memory"); }
static inline void sfence(void) { __asm__ volatile("dmb st" ::: "memory"); }

// Bulk transfer stubs
static inline void insl(int port, void *addr, int cnt) { 
    (void)port; (void)addr; (void)cnt; 
}
static inline void outsl(int port, const void *addr, int cnt) { 
    (void)port; (void)addr; (void)cnt; 
}
static inline void insw(int port, void *addr, int cnt) { 
    (void)port; (void)addr; (void)cnt; 
}
static inline void outsw(int port, const void *addr, int cnt) { 
    (void)port; (void)addr; (void)cnt; 
}

#elif defined(__x86_64__) || defined(__i386__)
// x86/x86_64 definitions
typedef uint64_t arch_word_t;
typedef uint64_t reg_t;

// I/O port operations
static inline uint8_t inb(uint16_t port) {
    uint8_t data;
    __asm__ volatile("inb %1,%0" : "=a"(data) : "d"(port) : "memory");
    return data;
}

static inline void outb(uint16_t port, uint8_t data) {
    __asm__ volatile("outb %0,%1" : : "a"(data), "d"(port) : "memory");
}

static inline uint16_t inw(uint16_t port) {
    uint16_t data;
    __asm__ volatile("inw %1,%0" : "=a"(data) : "d"(port) : "memory");
    return data;
}

static inline void outw(uint16_t port, uint16_t data) {
    __asm__ volatile("outw %0,%1" : : "a"(data), "d"(port) : "memory");
}

static inline uint32_t inl(uint16_t port) {
    uint32_t data;
    __asm__ volatile("inl %1,%0" : "=a"(data) : "d"(port) : "memory");
    return data;
}

static inline void outl(uint16_t port, uint32_t data) {
    __asm__ volatile("outl %0,%1" : : "a"(data), "d"(port) : "memory");
}

// Interrupt control
static inline void cli(void) {
    __asm__ volatile("cli" : : : "memory");
}

static inline void sti(void) {
    __asm__ volatile("sti" : : : "memory");
}

// Memory barriers
static inline void mfence(void) {
    __asm__ volatile("mfence" : : : "memory");
}

static inline void lfence(void) {
    __asm__ volatile("lfence" : : : "memory");
}

static inline void sfence(void) {
    __asm__ volatile("sfence" : : : "memory");
}

// Atomic exchange
static inline uint32_t xchg(volatile uint32_t *ptr, uint32_t val) {
    __asm__ volatile("xchgl %0, %1"
                     : "=r"(val)
                     : "m"(*ptr), "0"(val)
                     : "memory");
    return val;
}

// Invalidate TLB entry
static inline void invlpg(void *va) {
    __asm__ volatile("invlpg (%0)" : : "r"(va) : "memory");
}

// Load GDT - needs both pointer and size
static inline void lgdt(void *p, int size) {
    struct {
        uint16_t limit;
        uintptr_t base;
    } __attribute__((packed)) gdtr;
    
    gdtr.limit = size - 1;
    gdtr.base = (uintptr_t)p;
    
    __asm__ volatile("lgdt %0" : : "m"(gdtr) : "memory");
}

// Load IDT - needs both pointer and size
static inline void lidt(void *p, int size) {
    struct {
        uint16_t limit;
        uintptr_t base;
    } __attribute__((packed)) idtr;
    
    idtr.limit = size - 1;
    idtr.base = (uintptr_t)p;
    
    __asm__ volatile("lidt %0" : : "m"(idtr) : "memory");
}

// Load CR3 (page directory base)
#ifdef __x86_64__
static inline void lcr3(uint64_t val) {
    __asm__ volatile("movq %0, %%cr3" : : "r"(val));
}
#else
static inline void lcr3(uint32_t val) {
    __asm__ volatile("movl %0, %%cr3" : : "r"(val));
}
#endif

// Load task register
static inline void ltr(uint16_t sel) {
    __asm__ volatile("ltr %0" : : "r"(sel));
}

// Bulk data transfer
static inline void insl(int port, void *addr, int cnt) {
    __asm__ volatile("cld\n\t"
                     "rep insl"
                     : "=D"(addr), "=c"(cnt)
                     : "d"(port), "0"(addr), "1"(cnt)
                     : "memory", "cc");
}

static inline void outsl(int port, const void *addr, int cnt) {
    __asm__ volatile("cld\n\t"
                     "rep outsl"
                     : "=S"(addr), "=c"(cnt)
                     : "d"(port), "0"(addr), "1"(cnt)
                     : "memory", "cc");
}

static inline void insw(int port, void *addr, int cnt) {
    __asm__ volatile("cld\n\t"
                     "rep insw"
                     : "=D"(addr), "=c"(cnt)
                     : "d"(port), "0"(addr), "1"(cnt)
                     : "memory", "cc");
}

static inline void outsw(int port, const void *addr, int cnt) {
    __asm__ volatile("cld\n\t"
                     "rep outsw"
                     : "=S"(addr), "=c"(cnt)
                     : "d"(port), "0"(addr), "1"(cnt)
                     : "memory", "cc");
}

// String operations
static inline void stosb(void *addr, int data, int cnt) {
    __asm__ volatile("cld\n\t"
                     "rep stosb"
                     : "=D"(addr), "=c"(cnt)
                     : "a"(data), "0"(addr), "1"(cnt)
                     : "memory", "cc");
}

static inline void stosw(void *addr, int data, int cnt) {
    __asm__ volatile("cld\n\t"
                     "rep stosw"
                     : "=D"(addr), "=c"(cnt)
                     : "a"(data), "0"(addr), "1"(cnt)
                     : "memory", "cc");
}

static inline void stosl(void *addr, int data, int cnt) {
    __asm__ volatile("cld\n\t"
                     "rep stosl"
                     : "=D"(addr), "=c"(cnt)
                     : "a"(data), "0"(addr), "1"(cnt)
                     : "memory", "cc");
}

#else
// Generic/unknown architecture - all stubs
typedef uint64_t arch_word_t;
typedef uint64_t reg_t;

static inline void cli(void) { }
static inline void sti(void) { }
static inline uint8_t inb(uint16_t port) { (void)port; return 0; }
static inline void outb(uint16_t port, uint8_t data) { (void)port; (void)data; }
static inline uint16_t inw(uint16_t port) { (void)port; return 0; }
static inline void outw(uint16_t port, uint16_t data) { (void)port; (void)data; }
static inline uint32_t inl(uint16_t port) { (void)port; return 0; }
static inline void outl(uint16_t port, uint32_t data) { (void)port; (void)data; }
static inline void mfence(void) { }
static inline void lfence(void) { }
static inline void sfence(void) { }
static inline void insl(int port, void *addr, int cnt) { (void)port; (void)addr; (void)cnt; }
static inline void outsl(int port, const void *addr, int cnt) { (void)port; (void)addr; (void)cnt; }
static inline void insw(int port, void *addr, int cnt) { (void)port; (void)addr; (void)cnt; }
static inline void outsw(int port, const void *addr, int cnt) { (void)port; (void)addr; (void)cnt; }
static inline void stosb(void *addr, int data, int cnt) { (void)addr; (void)data; (void)cnt; }
static inline void stosw(void *addr, int data, int cnt) { (void)addr; (void)data; (void)cnt; }
static inline void stosl(void *addr, int data, int cnt) { (void)addr; (void)data; (void)cnt; }

#endif

// Common definitions across all architectures
#define ARCH_PAGE_SIZE 4096
#define ARCH_CACHE_LINE_SIZE 64