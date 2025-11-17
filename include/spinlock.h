#pragma once

#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>
#include "kernel_compat.h"
#include "config.h"

/* Forward declarations */
struct cpu;

/* Cache line size for alignment optimization */
extern size_t cache_line_size;
void detect_cache_line_size(void);

/* Ticket-based mutual exclusion lock for fair FIFO ordering */
struct ticketlock {
    _Atomic uint16_t head;  /* Next ticket to serve */
    _Atomic uint16_t tail;  /* Next ticket to issue */
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

/* Queued spinlock support (legacy placeholders - use exo_lock.h for real qspinlock) */
/* DEPRECATED: Use exo_lock.h and struct qspinlock instead */
#if !defined(USE_TICKET_LOCK) && !defined(USE_EXOLOCK) && !defined(__EXOLOCK_H_INCLUDED)
void qspin_lock(struct spinlock *lk);
void qspin_unlock(struct spinlock *lk);
#endif
#else
/* Uniprocessor stubs */
static inline void acquire(struct spinlock *lk) { (void)lk; }
static inline void release(struct spinlock *lk) { (void)lk; }
static inline int holding(struct spinlock *lk) { (void)lk; return 1; }
#endif

/* Cache line size detection at startup */
__attribute__((constructor))
static void initialize_cache_line_size(void) {
    if (cache_line_size == 0) {
        detect_cache_line_size();
    }
}

/* Alignment helper */
static inline size_t spinlock_align(void) {
    if (!cache_line_size) {
        detect_cache_line_size();
    }
    return cache_line_size;
}
