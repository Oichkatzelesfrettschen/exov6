/**
 * @file unified_lock.h
 * @brief Unified Modern Lock Architecture for ExoV6
 * 
 * Consolidates 5+ redundant lock implementations into a single,
 * mathematically-sound, multi-dimensional synchronization framework.
 * 
 * Features:
 * - Pure C17 with <stdatomic.h>
 * - Architecture-agnostic via HAL
 * - Adaptive lock selection based on contention patterns
 * - Capability-based access control integration
 * - Performance monitoring and NUMA awareness
 * - Zero-copy, cache-line aligned structures
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <stdatomic.h>
#include <stddef.h>
#include "compiler_attrs.h"
#include "cap.h"
#include "hal/atomic.h"
#include "param.h"  /* For NCPU */

/* ============================================================================
 * Core Type Definitions
 * ============================================================================ */

/**
 * Lock type enumeration for adaptive selection
 */
typedef enum {
    LOCK_TYPE_TICKET,    /* Default fair ticket lock */
    LOCK_TYPE_MCS,       /* MCS queue lock for high contention */
    LOCK_TYPE_RWLOCK,    /* Reader-writer lock */
    LOCK_TYPE_SEQLOCK,   /* Sequence lock for read-heavy */
    LOCK_TYPE_SLEEPLOCK, /* Blocking lock for long sections */
    LOCK_TYPE_RCU        /* Read-Copy-Update for lockless reads */
} lock_type_t;

/**
 * Contention profile for adaptive behavior
 * Using atomic typedefs for proper C17 compliance
 */
typedef struct {
    atomic_uint64_t acquisitions;      /* Total acquisition attempts */
    atomic_uint64_t contentions;       /* Times lock was contested */
    atomic_uint64_t total_hold_ns;     /* Total hold time in nanoseconds */
    atomic_uint32_t max_waiters;       /* Maximum concurrent waiters */
    atomic_uint32_t current_waiters;   /* Current waiting threads */
} lock_stats_t;

/* ============================================================================
 * Unified Ticket Spinlock (Foundation Primitive)
 * ============================================================================ */

/**
 * Modern ticket spinlock with C17 atomics
 * Cache-line aligned to prevent false sharing
 */
typedef struct exo_spinlock {
    _Alignas(64) struct {
        atomic_uint32_t ticket_head;   /* Next ticket to be served */
        atomic_uint32_t ticket_tail;   /* Next ticket to be issued */
        
        /* Debug and ownership tracking */
        atomic_int32_t owner_cpu;      /* CPU holding the lock (-1 = none) */
        atomic_uint64_t acquisitions;  /* Total acquisitions */
        
        /* Capability integration */
        cap_id_t required_cap;          /* Required capability to acquire */
        
        /* Performance tuning */
        uint16_t backoff_base;          /* Base backoff cycles */
        uint16_t backoff_max;           /* Maximum backoff cycles */
        
        /* Padding to fill cache line */
        char _padding[24];
    };
    
    /* Statistics on separate cache line */
    _Alignas(64) lock_stats_t stats;
    
    /* Lock name for debugging */
    const char *name;
    
} exo_spinlock_t;

/* Static initializer for compile-time initialization */
#define EXO_SPINLOCK_INIT(name_str) { \
    .ticket_head = ATOMIC_VAR_INIT(0), \
    .ticket_tail = ATOMIC_VAR_INIT(0), \
    .owner_cpu = ATOMIC_VAR_INIT(-1), \
    .acquisitions = ATOMIC_VAR_INIT(0), \
    .required_cap = 0, \
    .backoff_base = 10, \
    .backoff_max = 1024, \
    .stats = {0}, \
    .name = name_str \
}

/* ============================================================================
 * MCS Lock for High Contention
 * ============================================================================ */

/**
 * MCS queue node - each CPU/thread has its own
 * Prevents cache-line bouncing in high contention
 */
typedef struct mcs_node {
    atomic_bool locked;
    _Atomic(struct mcs_node *) next;
} mcs_node_t;

typedef struct mcs_lock {
    _Alignas(64) _Atomic(mcs_node_t *) tail;
    cap_id_t required_cap;
    lock_stats_t stats;
    const char *name;
} mcs_lock_t;

/* ============================================================================
 * Reader-Writer Lock
 * ============================================================================ */

typedef struct rwlock {
    _Alignas(64) struct {
        atomic_int32_t readers;         /* Number of active readers */
        atomic_bool writer;             /* Writer holding lock */
        atomic_uint32_t write_waiters;  /* Writers waiting */
        cap_id_t required_cap;
    };
    
    exo_spinlock_t guard;                /* Protects state transitions */
    lock_stats_t stats;
    const char *name;
} rwlock_t;

/* ============================================================================
 * Sequence Lock for Extreme Read Optimization
 * ============================================================================ */

typedef struct seqlock {
    _Alignas(64) struct {
        atomic_uint64_t sequence;       /* Sequence counter */
        exo_spinlock_t write_lock;       /* Protects writes */
    };
    
    lock_stats_t stats;
    const char *name;
} seqlock_t;

/* ============================================================================
 * Sleeplock Implementation (Integrated)
 * ============================================================================ */

/**
 * Sleeplock - blocking lock for long critical sections
 */
typedef struct sleeplock {
    _Alignas(64) struct {
        exo_spinlock_t guard;        /* Protects state */
        atomic_bool locked;         /* Is locked? */
        atomic_int32_t owner_pid;   /* PID of owner */
        
        /* Waiting queue */
        struct proc *wait_head;
        struct proc *wait_tail;
        
        /* Capability */
        cap_id_t required_cap;
    };
    
    lock_stats_t stats;
    const char *name;
} sleeplock_t;

/* Sleeplock operations */
void sleeplock_init(sleeplock_t *lock, const char *name);
void sleeplock_acquire(sleeplock_t *lock);
void sleeplock_release(sleeplock_t *lock);
bool sleeplock_holding(const sleeplock_t *lock);

/* ============================================================================
 * RCU Implementation (Integrated)
 * ============================================================================ */

/**
 * RCU - Read-Copy-Update for lockless reads
 */
typedef struct rcu_state {
    _Alignas(64) struct {
        atomic_uint64_t global_counter;    /* Global RCU counter */
        atomic_uint32_t reader_count[NCPU]; /* Per-CPU reader counts */
        exo_spinlock_t writer_lock;         /* Serializes writers */
    };
    
    lock_stats_t stats;
    const char *name;
} rcu_state_t;

/* RCU operations */
void rcu_init(rcu_state_t *rcu, const char *name);
/* RCU read operations are declared in defs.h for compatibility */
/* void rcu_read_lock(rcu_state_t *rcu); */
/* void rcu_read_unlock(rcu_state_t *rcu); */
void rcu_synchronize(rcu_state_t *rcu);
void rcu_call(rcu_state_t *rcu, void (*func)(void *), void *arg);

/* ============================================================================
 * Adaptive Lock Framework
 * ============================================================================ */

/**
 * Adaptive lock that switches between implementations based on contention
 */
typedef struct adaptive_lock {
    _Alignas(64) struct {
        _Atomic(lock_type_t) current_type;
        atomic_uint64_t adaptation_counter;
        
        /* Contention thresholds for adaptation */
        uint32_t mcs_threshold;          /* Switch to MCS above this */
        uint32_t sleep_threshold_ns;     /* Switch to sleep if hold > this */
    };
    
    /* Union of possible implementations */
    _Alignas(64) union {
        exo_spinlock_t ticket;
        mcs_lock_t mcs;
        rwlock_t rwlock;
        seqlock_t seqlock;
    } impl;
    
    /* Unified statistics */
    lock_stats_t stats;
    const char *name;
} adaptive_lock_t;

/* ============================================================================
 * Core Lock Operations
 * ============================================================================ */

/* Spinlock operations */
void exo_spinlock_init(exo_spinlock_t *lock, const char *name);
void exo_spinlock_acquire(exo_spinlock_t *lock);
bool exo_spinlock_try_acquire(exo_spinlock_t *lock);
void exo_spinlock_release(exo_spinlock_t *lock);
bool exo_spinlock_is_held(const exo_spinlock_t *lock);

/* MCS lock operations */
void mcs_lock_init(mcs_lock_t *lock, const char *name);
void mcs_lock_acquire(mcs_lock_t *lock, mcs_node_t *node);
void mcs_lock_release(mcs_lock_t *lock, mcs_node_t *node);

/* Reader-writer lock operations */
void rwlock_init(rwlock_t *lock, const char *name);
void rwlock_read_acquire(rwlock_t *lock);
void rwlock_read_release(rwlock_t *lock);
void rwlock_write_acquire(rwlock_t *lock);
void rwlock_write_release(rwlock_t *lock);

/* Sequence lock operations */
void seqlock_init(seqlock_t *lock, const char *name);
uint64_t seqlock_read_begin(const seqlock_t *lock);
bool seqlock_read_retry(const seqlock_t *lock, uint64_t seq);
void seqlock_write_begin(seqlock_t *lock);
void seqlock_write_end(seqlock_t *lock);

/* Adaptive lock operations */
void adaptive_lock_init(adaptive_lock_t *lock, const char *name);
void adaptive_lock_acquire(adaptive_lock_t *lock);
void adaptive_lock_release(adaptive_lock_t *lock);
void adaptive_lock_adapt(adaptive_lock_t *lock);

/* ============================================================================
 * Performance and Debugging
 * ============================================================================ */

/* Statistics retrieval */
void lock_get_stats(const void *lock, lock_stats_t *stats);
void lock_reset_stats(void *lock);

/* Debugging helpers */
void lock_dump_state(const void *lock);
const char *lock_type_name(lock_type_t type);

/* NUMA optimization hints */
void lock_set_numa_node(void *lock, int node);
int lock_get_numa_node(const void *lock);

/* ============================================================================
 * Capability Integration
 * ============================================================================ */

/* Set required capability for lock acquisition */
void lock_set_capability(void *lock, cap_id_t cap);
cap_id_t lock_get_capability(const void *lock);

/* ============================================================================
 * Legacy Compatibility Macros
 * ============================================================================ */

/* Legacy macros are disabled to avoid conflicts with existing code */
/* Uncomment these if you want to enable legacy compatibility mode */
#ifdef UNIFIED_LOCK_LEGACY_COMPAT
#define spinlock exo_spinlock_t
#define spinlock_init(l, n) exo_spinlock_init(l, n)
#define acquire(l) exo_spinlock_acquire(l)
#define release(l) exo_spinlock_release(l)
#define holding(l) exo_spinlock_is_held(l)

/* Map old sleeplock to adaptive lock with sleep preference */
#define sleeplock adaptive_lock_t
#define initsleeplock(l, n) adaptive_lock_init(l, n)
#define acquiresleep(l) adaptive_lock_acquire(l)
#define releasesleep(l) adaptive_lock_release(l)
#endif

/* ============================================================================
 * Architecture-Specific Optimizations
 * ============================================================================ */

/* Pause instruction for spin-wait loops */
static inline void cpu_pause(void) {
#if defined(__x86_64__)
    __asm__ volatile("pause" ::: "memory");
#elif defined(__aarch64__)
    __asm__ volatile("yield" ::: "memory");
#else
    atomic_signal_fence(memory_order_acquire);
#endif
}

/* Exponential backoff helper */
static inline void exponential_backoff(uint32_t *delay, uint32_t max_delay) {
    uint32_t current = *delay;
    for (uint32_t i = 0; i < current; i++) {
        cpu_pause();
    }
    *delay = (current < max_delay) ? (current * 2) : max_delay;
}

/* ============================================================================
 * Compile-Time Assertions
 * ============================================================================ */

_Static_assert(sizeof(exo_spinlock_t) <= 128, "Spinlock exceeds two cache lines");
_Static_assert(_Alignof(exo_spinlock_t) == 64, "Spinlock not cache-line aligned");
_Static_assert(sizeof(mcs_node_t) == 16, "MCS node size incorrect");
/* Size varies based on architecture - just ensure reasonable bounds */
_Static_assert(sizeof(lock_stats_t) <= 64, "Lock stats too large");