#pragma once
/**
 * @file exo_lock.h
 * @brief Unified lock subsystem for ExoV6 exokernel
 *
 * Novel synthesis of:
 * - NUMA-aware qspinlock (Linux MCS)
 * - Adaptive mutex (illumos)
 * - LWKT tokens (DragonFlyBSD)
 * - DAG-based deadlock prevention
 * - Resurrection-aware monitoring
 * - Physics-inspired optimization
 *
 * @version 1.0
 * @date 2025-11-17
 */

#include <stdatomic.h>
#include <stdint.h>
#include <stddef.h>
#include "types.h"
#include "config.h"

/* Forward declarations */
struct cpu;
struct proc;

/* ========================================================================
 * Lock Type Enumeration
 * ======================================================================== */

typedef enum {
    EXOLOCK_QSPIN    = 0,  /**< Queued spinlock (NUMA-aware, < 10μs hold) */
    EXOLOCK_ADAPTIVE = 1,  /**< Adaptive mutex (spin/block, < 100μs hold) */
    EXOLOCK_TOKEN    = 2,  /**< LWKT token (soft lock, variable hold) */
    EXOLOCK_SLEEP    = 3,  /**< Priority sleeping lock (> 100μs hold) */
} exo_lock_type_t;

/* ========================================================================
 * MCS Node Structure (for qspinlock)
 * ======================================================================== */

/**
 * MCS queue node - per-CPU allocation
 * Stores position in lock wait queue
 * Supports hierarchical NUMA-aware queuing
 */
struct mcs_node {
    _Atomic(struct mcs_node *) next;        /**< Next waiter in global queue */
    _Atomic(struct mcs_node *) local_next;  /**< Next waiter in local NUMA queue */
    _Atomic uint32_t locked;                /**< 1 = waiting, 0 = acquired */
    uint32_t numa_node;                     /**< NUMA node of this CPU */
    uint8_t is_local;                       /**< 1 if same NUMA as predecessor */
    uint8_t _pad[3];                        /**< Padding to maintain alignment */
} __attribute__((aligned(64)));  /* Cache line alignment */

/* Compile-time assertion to ensure mcs_node fits in cache line */
_Static_assert(sizeof(struct mcs_node) <= 64, "mcs_node exceeds cache line size");

/* Per-CPU MCS node array (4 slots for nested locks) */
#define MCS_NODES_PER_CPU 4
extern struct mcs_node mcs_nodes[NCPU][MCS_NODES_PER_CPU];

/* ========================================================================
 * Queued Spinlock (qspinlock)
 * ======================================================================== */

/**
 * QSpinlock performance statistics
 */
struct qspin_stats {
    uint64_t fast_path_count;       /**< Uncontended acquisitions */
    uint64_t slow_path_count;       /**< Had to queue */
    uint64_t local_handoff_count;   /**< Woke local NUMA waiter */
    uint64_t remote_handoff_count;  /**< Woke remote NUMA waiter */
    uint64_t total_spin_cycles;     /**< Total TSC cycles spinning */
    uint64_t max_spin_cycles;       /**< Longest spin time */
    uint64_t max_queue_depth;       /**< Most waiters queued */
    uint64_t total_hold_cycles;     /**< Total TSC cycles held */
    uint64_t max_hold_cycles;       /**< Longest hold time */
    uint64_t acquire_count;         /**< Total acquisitions */
} __attribute__((aligned(64)));

/**
 * NUMA-aware queued spinlock
 * Based on Linux MCS implementation
 *
 * Layout (32-bit):
 * - Bits 0-7:   Locked flag
 * - Bits 8-15:  Pending flag
 * - Bits 16-31: Tail (CPU ID + index)
 */
struct qspinlock {
    union {
        _Atomic uint32_t val;
        struct {
            uint8_t  locked;   /**< Lock held */
            uint8_t  pending;  /**< Pending waiter */
            uint16_t tail;     /**< Tail CPU + index */
        };
    };
    struct qspin_stats stats;       /**< Performance statistics */
    uint64_t last_acquire_tsc;      /**< TSC when lock was acquired */
    uint32_t last_owner_numa;       /**< NUMA node of last owner */
} __attribute__((aligned(128)));  /* Double cache line for stats */

void qspin_init(struct qspinlock *lock);
void qspin_lock(struct qspinlock *lock);
int qspin_trylock(struct qspinlock *lock);
void qspin_unlock(struct qspinlock *lock);

/* Statistics functions */
void qspin_dump_stats(struct qspinlock *lock, const char *name);
void qspin_reset_stats(struct qspinlock *lock);

/* ========================================================================
 * Adaptive Mutex
 * ======================================================================== */

/**
 * Adaptive mutex with turnstile
 * Spins if owner is running, blocks otherwise
 */
struct adaptive_mutex {
    _Atomic uint64_t owner;     /**< Owner thread ID (or 0 if free) */
    _Atomic uint32_t waiters;   /**< Number of waiters */
    void *turnstile;            /**< Wait queue (allocated on contention) */
    uint32_t flags;             /**< Lock flags (priority inheritance, etc.) */
} __attribute__((aligned(64)));

#define ADAPTIVE_FLAG_PRIO_INHERIT  0x1  /**< Enable priority inheritance */
#define ADAPTIVE_FLAG_REALTIME      0x2  /**< Real-time priority */

void adaptive_init(struct adaptive_mutex *lock, uint32_t flags);
void adaptive_lock(struct adaptive_mutex *lock);
int adaptive_trylock(struct adaptive_mutex *lock);
void adaptive_unlock(struct adaptive_mutex *lock);

/* ========================================================================
 * LWKT Token (Soft Lock)
 * ======================================================================== */

/**
 * LWKT token - CPU-owned, released on thread block
 * Perfect for exokernel capability traversal
 */
struct lwkt_token {
    _Atomic uint32_t cpu_owner;  /**< CPU ID holding token (0 = free) */
    uint32_t hash;               /**< Token pool hash */
    const char *name;            /**< Debug name */
    uint64_t acquire_tsc;        /**< Timestamp of acquisition */
} __attribute__((aligned(64)));

/* Token pool for hash-based distribution */
#define TOKEN_POOL_SIZE 256
extern struct lwkt_token token_pool[TOKEN_POOL_SIZE];

void token_init(struct lwkt_token *token, const char *name);
void token_acquire(struct lwkt_token *token);
void token_release(struct lwkt_token *token);
void token_release_all(void);  /**< Release all tokens on block */

/* ========================================================================
 * Priority Sleeping Lock
 * ======================================================================== */

/**
 * Priority-aware sleeping lock
 * For long-held locks with blocking
 */
struct sleep_lock {
    _Atomic uint32_t locked;     /**< 1 = held, 0 = free */
    _Atomic uint32_t holder_pid; /**< Process ID of holder */
    void *wait_queue;            /**< Priority wait queue */
    const char *name;            /**< Debug name */
} __attribute__((aligned(64)));

void sleeplock_init(struct sleep_lock *lock, const char *name);
void sleeplock_acquire(struct sleep_lock *lock);
int sleeplock_tryacquire(struct sleep_lock *lock);
void sleeplock_release(struct sleep_lock *lock);
int sleeplock_holding(struct sleep_lock *lock);

/* ========================================================================
 * DAG Lock Ordering
 * ======================================================================== */

/**
 * DAG node for lock ordering
 * Prevents deadlock via topological constraints
 */
struct lock_dag_node {
    uint32_t level;              /**< Topological level (0 = leaf) */
    uint64_t dependency_bitmap;  /**< Locks that must be acquired first */
    const char *name;            /**< Debug name */
};

/**
 * DAG enforcement: verify lock order
 * Returns 0 on success, -1 on violation
 */
int dag_verify_order(struct lock_dag_node *new_lock);

/* ========================================================================
 * Unified Lock Structure
 * ======================================================================== */

/**
 * Unified exo_lock structure
 * Supports all lock types via tagged union
 */
struct exo_lock {
    exo_lock_type_t type;        /**< Lock type */
    const char *name;            /**< Debug name */
    struct lock_dag_node dag;    /**< DAG ordering node */

    /* Lock-specific data */
    union {
        struct qspinlock qspin;
        struct adaptive_mutex adaptive;
        struct lwkt_token token;
        struct sleep_lock sleep;
    };

    /* Monitoring and statistics */
    struct {
        uint64_t acquire_count;   /**< Total acquisitions */
        uint64_t contention_count;/**< Contended acquisitions */
        uint64_t total_hold_time; /**< Total cycles held */
        uint64_t max_hold_time;   /**< Max cycles held */
    } stats;
} __attribute__((aligned(64)));

/* ========================================================================
 * Unified Lock API
 * ======================================================================== */

/**
 * Initialize lock with explicit type
 */
void exo_lock_init(struct exo_lock *lock, exo_lock_type_t type,
                   const char *name, uint32_t dag_level);

/**
 * Initialize lock with automatic type selection based on hold time hint
 * @param hold_time_ns Expected hold time in nanoseconds
 */
void exo_lock_init_auto(struct exo_lock *lock, const char *name,
                        uint32_t dag_level, uint64_t hold_time_ns);

/**
 * Acquire lock (blocking)
 * Enforces DAG ordering
 */
void exo_lock_acquire(struct exo_lock *lock);

/**
 * Try to acquire lock (non-blocking)
 * Returns 1 on success, 0 on failure
 */
int exo_lock_tryacquire(struct exo_lock *lock);

/**
 * Release lock
 */
void exo_lock_release(struct exo_lock *lock);

/**
 * Check if current CPU/process holds lock
 */
int exo_lock_holding(struct exo_lock *lock);

/* ========================================================================
 * Resurrection Server Integration
 * ======================================================================== */

/**
 * Lock health monitoring
 * Called periodically by resurrection server
 */
void lock_health_check(void);

/**
 * Force release of lock held by dead/stuck process
 * @param lock Lock to forcibly release
 * @return 0 on success, -1 on error
 */
int lock_force_release(struct exo_lock *lock);

/**
 * Register lock for health monitoring
 */
void lock_register_monitor(struct exo_lock *lock);

/**
 * Unregister lock from health monitoring
 */
void lock_unregister_monitor(struct exo_lock *lock);

/* Resurrection event types */
typedef enum {
    LOCK_RESURRECTION_NONE = 0,
    LOCK_RESURRECTION_FORCE_RELEASE,  /**< Lock forcibly released */
    LOCK_TIMEOUT_KILL,                /**< Process killed for lock timeout */
    LOCK_DEADLOCK_DETECTED,           /**< Deadlock detected and resolved */
} resurrection_event_t;

/**
 * Log resurrection event
 */
void resurrection_event_log(resurrection_event_t event, uint32_t pid,
                           struct exo_lock *lock);

/* ========================================================================
 * Physics-Inspired Optimization
 * ======================================================================== */

/**
 * Optimize lock memory layout using simulated annealing
 * Minimizes cache contention based on access patterns
 *
 * @param locks Array of locks to optimize
 * @param count Number of locks
 * @param iterations Number of annealing iterations
 */
void lock_optimize_layout(struct exo_lock *locks[], size_t count,
                         uint32_t iterations);

/**
 * Entangled lock pair for correlated access patterns
 * Allows atomic acquisition of both locks if correlation > threshold
 */
struct entangled_lock_pair {
    struct exo_lock *lock_a;
    struct exo_lock *lock_b;
    double correlation;          /**< Access pattern correlation [0, 1] */
    _Atomic uint64_t joint_state;/**< Packed state for both locks */
};

/**
 * Initialize entangled lock pair
 */
void entangled_pair_init(struct entangled_lock_pair *pair,
                        struct exo_lock *a, struct exo_lock *b);

/**
 * Acquire entangled pair atomically (if highly correlated)
 */
void entangled_pair_acquire(struct entangled_lock_pair *pair);

/**
 * Release entangled pair
 */
void entangled_pair_release(struct entangled_lock_pair *pair);

/**
 * Update correlation based on access patterns
 */
void entangled_pair_update_correlation(struct entangled_lock_pair *pair);

/* ========================================================================
 * Legacy Compatibility
 * ======================================================================== */

#ifndef EXOLOCK_NO_LEGACY

/**
 * Legacy spinlock compatibility layer
 * Maps to EXOLOCK_QSPIN for drop-in replacement
 */
struct spinlock;

static inline void initlock_compat(struct spinlock *lk, const char *name) {
    exo_lock_init((struct exo_lock *)lk, EXOLOCK_QSPIN, name, 0);
}

static inline void acquire_compat(struct spinlock *lk) {
    exo_lock_acquire((struct exo_lock *)lk);
}

static inline void release_compat(struct spinlock *lk) {
    exo_lock_release((struct exo_lock *)lk);
}

static inline int holding_compat(struct spinlock *lk) {
    return exo_lock_holding((struct exo_lock *)lk);
}

#endif /* EXOLOCK_NO_LEGACY */

/* ========================================================================
 * Configuration and Tuning
 * ======================================================================== */

/* Lock timeouts (in TSC cycles) */
#define LOCK_TIMEOUT_CYCLES        (1000000000ULL)  /* 1 second @ 1GHz */
#define LOCK_CRITICAL_TIMEOUT      (5000000000ULL)  /* 5 seconds @ 1GHz */

/* Adaptive spinning thresholds */
#define ADAPTIVE_SPIN_MIN_CYCLES   10
#define ADAPTIVE_SPIN_MAX_CYCLES   1000

/* NUMA optimization */
#define NUMA_LOCAL_BIAS            2  /* Prefer local socket 2:1 */

/* Annealing parameters */
#define ANNEAL_INITIAL_TEMP        1000.0
#define ANNEAL_COOLING_RATE        0.95
#define ANNEAL_MIN_TEMP            0.01

/* Entanglement correlation threshold */
#define ENTANGLE_CORRELATION_MIN   0.8

/* ========================================================================
 * Statistics and Debugging
 * ======================================================================== */

/**
 * Global lock statistics
 */
struct lock_global_stats {
    uint64_t total_acquires;
    uint64_t total_contentions;
    uint64_t total_resurrections;
    uint64_t total_dag_violations;
    uint64_t total_force_releases;
};

extern struct lock_global_stats lock_stats;

/**
 * Print lock statistics
 */
void lock_print_stats(void);

/**
 * Reset lock statistics
 */
void lock_reset_stats(void);

/**
 * Dump lock state for debugging
 */
void lock_dump_state(struct exo_lock *lock);

/* ========================================================================
 * Initialization
 * ======================================================================== */

/**
 * Initialize lock subsystem
 * Called once at boot
 */
void lock_subsystem_init(void);

/**
 * Detect NUMA topology for lock optimization
 */
void lock_detect_numa_topology(void);

/**
 * Get number of NUMA nodes detected
 */
uint32_t lock_get_numa_node_count(void);

/**
 * Get NUMA node for specific CPU
 * @param cpu_id CPU ID (0-based)
 * @return NUMA node ID
 */
uint32_t lock_get_cpu_numa_node(uint32_t cpu_id);

/**
 * Start resurrection server monitoring thread
 */
void lock_start_resurrection_server(void);
