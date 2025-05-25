#pragma once


#include <stddef.h>

struct ticketlock {
  _Atomic unsigned short head;
  _Atomic unsigned short tail;
};

struct cpu; // forward declaration

struct spinlock {
  struct ticketlock ticket;
  char *name;
  struct cpu *cpu;
  unsigned int pcs[10];
};
static inline void initlock(struct spinlock *l, const char *name) { (void)l; (void)name; }
static inline void acquire(struct spinlock *l) { (void)l; }
static inline void release(struct spinlock *l) { (void)l; }
#ifdef SPINLOCK_NO_STUBS
static inline size_t spinlock_optimal_alignment(void) {
#if defined(__i386__) || defined(__x86_64__)
    unsigned int eax = 1, ebx, ecx, edx;
    __asm__ volatile("cpuid" : "=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx) : "a"(eax));
    size_t sz = ((ebx >> 8) & 0xff) * 8u;
#else
    size_t sz = 0;
#endif
    size_t base = __alignof__(struct spinlock);
    return sz > base ? sz : base;
}
#else
static inline size_t spinlock_optimal_alignment(void) { return __alignof__(struct spinlock); }
#endif
