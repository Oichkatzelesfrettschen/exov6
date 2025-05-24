#pragma once

#include <stdint.h>
#include "types.h"

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
static inline void initlock(struct spinlock *l, char *name) { (void)l; (void)name; }
static inline void acquire(struct spinlock *l) { (void)l; }
static inline void release(struct spinlock *l) { (void)l; }
#else
static inline void initlock(struct spinlock *l, char *name);
static inline void acquire(struct spinlock *l);
static inline void release(struct spinlock *l);
#endif
