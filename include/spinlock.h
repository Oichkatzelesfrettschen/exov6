#pragma once

#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>
#include "kernel_compat.h"
#include "config.h"

/* Forward declarations */
struct cpu;

/* Cache line size for alignment optimization (kernel only) */
#ifdef EXO_KERNEL
extern size_t cache_line_size;
void detect_cache_line_size(void);
#endif

/* Ticket-based mutual exclusion lock for fair FIFO ordering */
struct ticketlock {
    _Atomic(uint_least16_t) head;  /* Next ticket to serve */
    _Atomic(uint_least16_t) tail;  /* Next ticket to issue */
};

/* Spinlock with debugging support */
struct spinlock {
    struct ticketlock ticket;  /* Underlying ticket lock */
    const char *name;          /* Human-readable identifier */
    uint32_t pcs[10];         /* Call stack at acquisition */
    struct cpu *cpu;          /* CPU holding the lock */
};

/* Initialize spinlock with name */
void initlock(struct spinlock *lk, const char *name);

#if CONFIG_SMP && !defined(SPINLOCK_UNIPROCESSOR)
/* SMP spinlock operations */
void acquire(struct spinlock *lk);
void release(struct spinlock *lk);
int holding(struct spinlock *lk);

/* Queued spinlock support */
#if !defined(USE_TICKET_LOCK)
void qspin_lock(struct spinlock *lk);
void qspin_unlock(struct spinlock *lk);
#endif
#else
/* Uniprocessor stubs */
static inline void acquire(struct spinlock *lk) { (void)lk; }
static inline void release(struct spinlock *lk) { (void)lk; }
static inline int holding(struct spinlock *lk) { (void)lk; return 1; }
#endif

/* Cache line size detection at startup - kernel only */
#ifdef EXO_KERNEL
__attribute__((constructor))
static void initialize_cache_line_size(void) {
    if (cache_line_size == 0) {
        detect_cache_line_size();
    }
}
#endif /* EXO_KERNEL */

/* Alignment helper - kernel only */
#ifdef EXO_KERNEL
static inline size_t spinlock_align(void) {
    if (!cache_line_size) {
        detect_cache_line_size();
    }
    return cache_line_size;
}
#else
/* User-space defaults to common cache line size */
static inline size_t spinlock_align(void) {
    return 64;  /* Default cache line size */
}
#endif /* EXO_KERNEL */
