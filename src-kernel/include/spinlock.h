#pragma once

#include <stddef.h>
#include <stdint.h>

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

// Returns the recommended alignment for instances of struct spinlock.
static inline size_t
spinlock_optimal_alignment(void)
{
  return __alignof__(struct spinlock);
}

