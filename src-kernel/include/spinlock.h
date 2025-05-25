#pragma once

#include <stddef.h>
#include <stdint.h>
#include <config.h>

// Ticket-based mutual exclusion lock.
struct ticketlock {
  _Atomic uint16_t head;
  _Atomic uint16_t tail;
};

struct spinlock {
  struct ticketlock ticket; // Ticket lock implementation

  // For debugging:
  char *name;      // Name of lock.
  struct cpu *cpu; // The cpu holding the lock.
  uint pcs[10];    // The call stack (an array of program counters)
                   // that locked the lock.
};

#if CONFIG_SMP
void initlock(struct spinlock *lk, char *name);
void acquire(struct spinlock *lk);
void release(struct spinlock *lk);
int holding(struct spinlock *lk);
#else
static inline void initlock(struct spinlock *lk, char *name) {
  (void)lk;
  (void)name;
}
static inline void acquire(struct spinlock *lk) { (void)lk; }
static inline void release(struct spinlock *lk) { (void)lk; }
static inline int holding(struct spinlock *lk) {
  (void)lk;
  return 1;
}
#endif

// Returns the recommended alignment for instances of struct spinlock.
static inline size_t spinlock_optimal_alignment(void) {
  return __alignof__(struct spinlock);
}
