#pragma once

#include <stddef.h>
#include <stdint.h>
#include <stdatomic.h>
#include "config.h"

struct cpu; /**< Forward declaration for CPU holding the lock. */

/** Ticket-based mutual exclusion lock used to implement spinlocks. */
struct ticketlock {
  _Atomic uint16_t head; /**< Next ticket number to service. */
  _Atomic uint16_t tail; /**< Current ticket being served. */
};

/**
 * @brief Simple spinlock built on a ticket lock.
 */
struct spinlock {
  struct ticketlock ticket; /**< Underlying ticket lock. */
  char *name;               /**< Human-readable lock name. */
  uint32_t pcs[10];         /**< Call stack at acquisition for debugging. */
  struct cpu *cpu;          /**< CPU that currently holds the lock. */
};

/** Size of a cache line in bytes. Determined at runtime. */
extern size_t cache_line_size;

/** Detect and set the hardware cache line size. */
void detect_cache_line_size(void);

/** Initialise a spinlock with the provided name. */
void initlock(struct spinlock *lk, char *name);

#if CONFIG_SMP && !defined(SPINLOCK_UNIPROCESSOR)
/** Acquire a spinlock, blocking until it is available. */
void acquire(struct spinlock *lk);

/** Release a previously acquired spinlock. */
void release(struct spinlock *lk);
#endif

/**
 * @brief Recommended alignment for spinlock instances.
 *
 * Aligning spinlocks to the cache line size helps avoid false sharing in
 * multi-core environments.
 */
static inline size_t spinlock_alignment(void) {
  return cache_line_size ? cache_line_size : 64u;
}

