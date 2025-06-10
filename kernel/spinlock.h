#pragma once

#include <stddef.h>
#include <stdint.h>
#include "config.h"

// Forward declaration of struct cpu, representing a CPU structure used in spinlock debugging.
struct cpu;

// Ticket-based mutual exclusion lock.
struct ticketlock {
  _Atomic uint16_t head;
  _Atomic uint16_t tail;
};

struct spinlock {
  struct ticketlock ticket; // Ticket lock implementation
  char *lock_name_ptr;  // Pointer to the name of the lock (null-terminated string).
  // For debugging:
  uint32_t pcs[10]; // Stores the call stack for debugging purposes.
                    // The call stack (an array of program counters) that locked the lock.
                    // This array is intended to store up to 10 program counters (return addresses)
                    // from the call stack at the time the lock was acquired. It is primarily used
                    // for debugging purposes to trace the code path that led to the lock being held.
                    // The exact mechanism for capturing these program counters is implementation-specific
                    // and may involve walking the stack or using compiler-provided intrinsics.
  struct cpu *cpu;  // The cpu holding the lock.
};
extern size_t cache_line_size;
// Represents the size of a cache line in bytes, used for optimizing spinlock alignment.
// It is initialized by the detect_cache_line_size() function at runtime.
extern size_t cache_line_size;

// Ensure cache_line_size is initialized during program startup.
__attribute__((constructor)) static void initialize_cache_line_size(void) {
  if (cache_line_size == 0) {
    detect_cache_line_size();
#endif // CONFIG_SMP && !defined(SPINLOCK_UNIPROCESSOR)
}
void detect_cache_line_size(void);
void initlock(struct spinlock *lk, char *lock_name_ptr);
// Enable spinlock functionality for symmetric multiprocessing (SMP) systems,
// unless explicitly configured for a uniprocessor setup.
#if CONFIG_SMP && !defined(SPINLOCK_UNIPROCESSOR)
// void initlock(struct spinlock *lk, char *name); // Removed duplicate declaration
void acquire(struct spinlock *lk);
void release(struct spinlock *lk);
#endif
// Returns the recommended alignment for instances of struct spinlock.
// Aligning spinlocks to the cache line size helps avoid false sharing,
// which can significantly improve performance in multi-core systems.
  // Assume cache_line_size is initialized during program startup.
  // No need to call detect_cache_line_size here.
  }
  return cache_line_size;
}

#endif // CONFIG_SMP && !defined(SPINLOCK_UNIPROCESSOR)

