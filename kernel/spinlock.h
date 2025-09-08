#pragma once

#include <stddef.h>
#include <stdint.h>
#include "kernel_compat.h"
#include "config.h"

/** Forward declaration for CPU reference in spinlock. */
struct cpu;

/** Size of a cache line in bytes. Determined at runtime. */
extern size_t cache_line_size;

/** Detect and set the hardware cache line size. */
void detect_cache_line_size(void);

/**
 * @brief Ticket-based mutual exclusion lock for spinlocks.
 *
 * Provides fair FIFO ordering of lock acquisition.
 */
struct ticketlock {
    _Atomic uint16_t head; /**< Next ticket number to service. */
    _Atomic uint16_t tail; /**< Current ticket being served. */
};

/**
 * @brief Simple spinlock built on a ticket lock.
 *
 * Collects debug info and owner tracking.
 */
struct spinlock {
    struct ticketlock ticket; /**< Underlying ticket lock. */
    char *name;               /**< Human-readable lock name. */
    uint32_t pcs[10];         /**< Call stack at acquisition for debugging. */
    struct cpu *cpu;          /**< CPU that currently holds the lock. */
};

/**
 * @brief Initialise a spinlock with the provided name.
 */
void initlock(struct spinlock *lk, char *name);

/** Ensure cache_line_size is initialized at program startup. */
__attribute__((constructor))
static void initialize_cache_line_size(void) {
    if (cache_line_size == 0) {
        detect_cache_line_size();
    }
}

#if CONFIG_SMP && !defined(SPINLOCK_UNIPROCESSOR)
/**
 * @brief Acquire a spinlock, blocking until it is available.
 */
void acquire(struct spinlock *lk);

/**
 * @brief Release a previously acquired spinlock.
 */
void release(struct spinlock *lk);
#endif

/**
 * @brief Recommended alignment for spinlock instances.
 *
 * Aligning to the cache line size helps avoid false sharing
 * in multi-core environments.
 */
static inline size_t spinlock_alignment(void) {
    return cache_line_size ? cache_line_size : 64u;
}