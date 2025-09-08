#pragma once

#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>
#include "config.h"

/**
 * Forward declaration of CPU descriptor used for debugging ownership.
 */
struct cpu;

/** Ticket-based mutual exclusion lock. */
struct ticketlock {
  _Atomic uint16_t head; /**< Next ticket to serve. */
  _Atomic uint16_t tail; /**< Next ticket to issue. */
};

/** Spinlock implemented via a ticket lock with debug information. */
struct spinlock {
  struct ticketlock ticket; /**< Ticket lock state. */
  char *name;               /**< Human-readable lock identifier. */
  uint32_t pcs[10];         /**< Call stack PCs at lock acquisition. */
  struct cpu *cpu;          /**< CPU currently holding the lock. */
};

/** Size in bytes of a processor cache line. */
extern size_t cache_line_size;

/**
 * Detect the architecture's cache line size at runtime.
 */
void detect_cache_line_size(void);

/**
 * Initialise a spinlock with a descriptive name.
 *
 * \param lk   Spinlock to initialise.
 * \param name Null-terminated label used for diagnostics.
 */
void initlock(struct spinlock *lk, char *name);

#if CONFIG_SMP && !defined(SPINLOCK_UNIPROCESSOR)
/** Acquire a spinlock, blocking until it becomes available. */
void acquire(struct spinlock *lk);

/** Release a previously acquired spinlock. */
void release(struct spinlock *lk);
#endif

/**
 * Obtain the recommended alignment for \ref spinlock.
 *
 * The alignment equals the runtime-detected cache line width to minimise
 * false sharing across cores.
 *
 * \returns Number of bytes to align a spinlock instance.
 */
static inline size_t spinlock_align(void)
{
  if (!cache_line_size) {
    detect_cache_line_size();
  }
  return cache_line_size;
}
