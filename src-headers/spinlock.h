#pragma once
#include "types.h"


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

