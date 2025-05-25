#pragma once

#include <stddef.h>

// Ticket-based mutual exclusion lock.
struct ticketlock {
  _Atomic uint16_t head;
  _Atomic uint16_t tail;
};

struct spinlock {
  struct ticketlock ticket; // Ticket lock implementation

  // For debugging:
  char *name;        // Name of lock.
  struct cpu *cpu;   // The cpu holding the lock.
  uint pcs[10];      // The call stack (an array of program counters)
                     // that locked the lock.
};

#ifndef SPINLOCK_NO_STUBS
extern size_t spinlock_cache_line_size;
static inline size_t
spinlock_optimal_alignment(void)
{
  size_t base = __alignof__(struct spinlock);
  return spinlock_cache_line_size > base ? spinlock_cache_line_size : base;
}
#else
static inline size_t
spinlock_optimal_alignment(void)
{
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
#endif

