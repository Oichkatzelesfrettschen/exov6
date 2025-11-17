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

/* Guard to prevent old spinlock.h from declaring conflicting qspin_* functions */
#define __EXOLOCK_H_INCLUDED
#define __EXOLOCK_TYPES_DEFINED

#include <stdatomic.h>
#include <stdint.h>
#include <stddef.h>
#include "types.h"
#include "config.h"

/* Need NCPU for MCS node arrays */
#ifndef NCPU
#include "param.h"
#endif

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
 *
 * Note: Using C23 _Atomic keyword properly with clang's builtin stdatomic.h
 * The _Atomic qualifier is necessary for atomic_store_explicit/atomic_load_explicit
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
    const char *name;               /**< Debug name */
    uint32_t dag_level;             /**< DAG deadlock prevention level */
} __attribute__((aligned(128)));  /* Double cache line for stats */

void qspin_init(struct qspinlock *lock, const char *name, uint32_t dag_level);
void qspin_lock(struct qspinlock *lock);
int qspin_trylock(struct qspinlock *lock);
void qspin_unlock(struct qspinlock *lock);

/* Statistics functions */
void qspin_dump_stats(struct qspinlock *lock, const char *name);
void qspin_reset_stats(struct qspinlock *lock);

/* ========================================================================
 * Adaptive Mutex
 * ======================================================================== */

/* Forward declaration for turnstile */
struct turnstile;
struct thread;

/* Adaptive mutex configuration */
#define ADAPTIVE_SPIN_LIMIT_DEFAULT 100    /**< Default max spin iterations */
#define ADAPTIVE_SPIN_MIN_BACKOFF   10     /**< Min backoff cycles */
#define ADAPTIVE_SPIN_MAX_BACKOFF   1000   /**< Max backoff cycles */

/* Invalid CPU/thread markers */
#define INVALID_CPU ((uint32_t)-1)
#define INVALID_TID ((uint32_t)-1)

/**
 * Adaptive mutex performance statistics
 */
struct adaptive_mutex_stats {
    uint64_t acquire_count;           /**< Total acquisitions */
    uint64_t spin_acquire_count;      /**< Acquired while spinning */
    uint64_t block_acquire_count;     /**< Acquired after blocking */
    uint64_t trylock_success_count;   /**< Successful trylock attempts */
    uint64_t trylock_fail_count;      /**< Failed trylock attempts */
    uint64_t total_spin_cycles;       /**< Total TSC cycles spent spinning */
    uint64_t total_block_cycles;      /**< Total TSC cycles spent blocked */
    uint64_t max_spin_cycles;         /**< Longest spin time */
    uint64_t max_block_cycles;        /**< Longest block time */
    uint64_t max_hold_cycles;         /**< Longest hold time */
    uint64_t contention_count;        /**< Times lock was contended */
    uint64_t owner_running_count;     /**< Times owner was running (spin) */
    uint64_t owner_blocked_count;     /**< Times owner was blocked (no spin) */
    uint64_t priority_inherit_count;  /**< Times PI was triggered */
} __attribute__((aligned(128)));

/**
 * Adaptive mutex with turnstile queuing
 *
 * Key features:
 * - Spins if lock holder is running (likely to release soon)
 * - Blocks on turnstile if lock holder is sleeping/preempted
 * - Supports priority inheritance for real-time tasks
 * - NUMA-aware spinning behavior
 * - Comprehensive performance statistics
 *
 * Optimal for: 10μs - 100μs critical sections
 *
 * Memory layout (cache-aligned):
 * - Atomic state fields (1 cache line)
 * - Configuration and pointers (1 cache line)
 * - Statistics (2 cache lines)
 */
struct adaptive_mutex {
    /* Hot path: atomic state (frequently accessed) */
    _Atomic uint32_t locked;           /**< 0 = free, 1 = locked */
    _Atomic uint32_t owner_cpu;        /**< CPU ID of current holder */
    _Atomic uint32_t owner_tid;        /**< Thread ID of current holder */
    _Atomic uint32_t waiters;          /**< Number of threads waiting */

    /* Configuration and cold path data */
    struct turnstile *turnstile;       /**< Wait queue for blockers */
    uint32_t spin_limit;               /**< Max spin iterations before blocking */
    uint32_t flags;                    /**< Behavior flags */
    const char *name;                  /**< Debug name */
    uint32_t dag_level;                /**< DAG deadlock prevention level */

    /* Statistics (separate cache lines to avoid false sharing) */
    struct adaptive_mutex_stats stats;

    /* Padding to ensure cache line alignment */
    uint8_t _pad[0];
} __attribute__((aligned(256)));  /* 4 cache lines for full structure */

/* Compile-time size check */
_Static_assert(sizeof(struct adaptive_mutex) <= 512,
              "adaptive_mutex too large - optimize structure");

/* Adaptive mutex flags */
#define ADAPTIVE_FLAG_PRIO_INHERIT  0x1  /**< Enable priority inheritance */
#define ADAPTIVE_FLAG_REALTIME      0x2  /**< Real-time priority */
#define ADAPTIVE_FLAG_NUMA_AWARE    0x4  /**< NUMA-aware spinning */
#define ADAPTIVE_FLAG_STATS_ENABLED 0x8  /**< Track detailed statistics */

/* Adaptive mutex API */
void adaptive_mutex_init(struct adaptive_mutex *mutex, const char *name,
                        uint32_t dag_level, uint32_t flags);
void adaptive_mutex_lock(struct adaptive_mutex *mutex);
int adaptive_mutex_trylock(struct adaptive_mutex *mutex);
void adaptive_mutex_unlock(struct adaptive_mutex *mutex);

/* Statistics and debugging */
void adaptive_mutex_dump_stats(struct adaptive_mutex *mutex, const char *name);
void adaptive_mutex_reset_stats(struct adaptive_mutex *mutex);

/* Advanced operations */
int adaptive_mutex_holding(struct adaptive_mutex *mutex);
void adaptive_mutex_set_spin_limit(struct adaptive_mutex *mutex, uint32_t limit);

/* ========================================================================
 * Turnstile (Wait Queue for Adaptive Mutex)
 * ======================================================================== */

/**
 * Thread queue node
 * Used in turnstile FIFO queue
 */
struct thread_queue_node {
    struct thread *thread;             /**< Waiting thread */
    struct thread_queue_node *next;    /**< Next in queue */
    struct thread_queue_node *prev;    /**< Previous in queue */
    uint32_t priority;                 /**< Thread priority (for PI) */
    uint64_t enqueue_tsc;              /**< When thread joined queue */
} __attribute__((aligned(64)));

/**
 * Thread wait queue (FIFO with priority inheritance support)
 */
struct thread_queue {
    struct thread_queue_node *head;    /**< First waiter */
    struct thread_queue_node *tail;    /**< Last waiter */
    uint32_t count;                    /**< Number of waiters */
    uint32_t max_priority;             /**< Highest priority in queue */
} __attribute__((aligned(64)));

/**
 * Turnstile - wait queue with priority inheritance
 *
 * Design based on FreeBSD turnstiles:
 * - One turnstile per blocking lock
 * - FIFO ordering for fairness
 * - Priority inheritance to prevent priority inversion
 * - Statistics for performance analysis
 *
 * Turnstiles are allocated on first contention and recycled.
 */
struct turnstile {
    struct thread_queue waiters;       /**< FIFO wait queue */
    _Atomic uint32_t count;            /**< Number of waiters (atomic for stats) */
    struct adaptive_mutex *mutex;      /**< Associated mutex */

    /* Priority inheritance state */
    uint8_t priority_inherited;        /**< 1 if PI is active */
    uint8_t _pad1[3];
    uint32_t inherited_priority;       /**< Priority we inherited */
    uint32_t original_priority;        /**< Original owner priority */

    /* Statistics */
    uint64_t total_wait_time;          /**< Total wait time of all threads */
    uint64_t max_wait_time;            /**< Longest wait time */
    uint64_t wakeup_count;             /**< Total wakeups */

    /* Debugging */
    const char *name;                  /**< Debug name (from mutex) */
} __attribute__((aligned(128)));

/* Turnstile pool size (pre-allocated for performance) */
#define TURNSTILE_POOL_SIZE 64

/* Turnstile API */
struct turnstile *turnstile_alloc(struct adaptive_mutex *mutex);
void turnstile_free(struct turnstile *ts);
void turnstile_wait(struct turnstile *ts, struct thread *thread);
struct thread *turnstile_wake_one(struct turnstile *ts);
void turnstile_wake_all(struct turnstile *ts);
int turnstile_has_waiters(struct turnstile *ts);

/* Thread queue operations */
void thread_queue_init(struct thread_queue *q);
void thread_queue_push(struct thread_queue *q, struct thread *thread, uint32_t priority);
struct thread *thread_queue_pop(struct thread_queue *q);
int thread_queue_empty(struct thread_queue *q);

/* ========================================================================
 * LWKT Token (Soft Lock)
 * ======================================================================== */

/**
 * LWKT (Light-Weight Kernel Thread) Token
 *
 * Inspired by DragonFlyBSD's LWKT token design:
 * - CPU-owned (not thread-owned)
 * - Automatically released on context switch/block
 * - No sleep/wakeup mechanism (pure spin)
 * - Extremely low overhead
 * - Perfect for exokernel capability traversal
 *
 * Key properties:
 * - One owner CPU at a time (or none)
 * - Multiple tokens can be held simultaneously per CPU
 * - Tokens released in batch on scheduler entry
 * - Hash-based pool distribution reduces contention
 *
 * Optimal for: Very short critical sections (< 1μs)
 */

/* Per-CPU token ownership tracking */
#define MAX_TOKENS_PER_CPU 16  /**< Max simultaneous tokens per CPU */

struct cpu_token_list {
    struct lwkt_token *tokens[MAX_TOKENS_PER_CPU];
    uint32_t count;
} __attribute__((aligned(64)));

/* Token pool configuration */
#define TOKEN_POOL_SIZE 256         /**< Pool size (power of 2) */
#define TOKEN_POOL_HASH_BITS 8      /**< Hash bits for pool lookup */
#define TOKEN_FREE_MARKER NCPU      /**< Free token marker (invalid CPU ID) */

/**
 * LWKT token statistics
 */
struct lwkt_token_stats {
    uint64_t acquire_count;         /**< Total acquisitions */
    uint64_t release_count;         /**< Total releases */
    uint64_t contention_count;      /**< Times had to wait */
    uint64_t total_hold_cycles;     /**< Total cycles held */
    uint64_t max_hold_cycles;       /**< Longest hold time */
    uint64_t reacquire_count;       /**< Already owned (fast path) */

    /* Per-CPU acquisition tracking */
    uint64_t cpu_acquire_count[NCPU]; /**< Acquisitions per CPU */
} __attribute__((aligned(128)));

/**
 * LWKT token structure
 *
 * Memory layout (cache-optimized):
 * - Atomic owner field (hot path)
 * - Metadata (cold path)
 * - Statistics (separate cache line)
 */
struct lwkt_token {
    /* Hot path: atomic owner */
    _Atomic uint32_t owner_cpu;     /**< CPU ID holding token (TOKEN_FREE_MARKER = free) */

    /* Cold path: metadata */
    uint32_t hash;                  /**< Token pool hash */
    const char *name;               /**< Debug name */
    uint32_t dag_level;             /**< DAG deadlock prevention level */
    uint64_t acquire_tsc;           /**< Timestamp of acquisition */

    /* Statistics (separate cache line for minimal false sharing) */
    struct lwkt_token_stats stats;

    /* Padding */
    uint8_t _pad[0];
} __attribute__((aligned(256)));

/* Compile-time size check */
_Static_assert(sizeof(struct lwkt_token) <= 512,
              "lwkt_token too large - optimize structure");

/* Token pool for hash-based distribution */
extern struct lwkt_token token_pool[TOKEN_POOL_SIZE];
extern struct cpu_token_list cpu_tokens[NCPU];

/* Core token API */
void token_init(struct lwkt_token *token, const char *name, uint32_t dag_level);
void token_acquire(struct lwkt_token *token);
void token_release(struct lwkt_token *token);
void token_release_all(void);  /**< Release all tokens on block */

/* Token pool API */
void token_pool_init(void);
struct lwkt_token *token_pool_get(void *resource);  /**< Get token for resource */

/* Verification and debugging */
int token_holding(struct lwkt_token *token);
void token_assert_held(struct lwkt_token *token);

/* Statistics */
void token_dump_stats(struct lwkt_token *token, const char *name);
void token_reset_stats(struct lwkt_token *token);

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
 * DAG Lock Hierarchy and Tracking (Phase 4)
 * ======================================================================== */

/* Lock hierarchy levels (DAG ordering) */
#define LOCK_LEVEL_NONE         0   /**< No ordering requirement */
#define LOCK_LEVEL_SCHEDULER    10  /**< Scheduler internal locks */
#define LOCK_LEVEL_PROCESS      20  /**< Process table, thread management */
#define LOCK_LEVEL_MEMORY       30  /**< Page tables, allocators */
#define LOCK_LEVEL_VFS          40  /**< File system metadata */
#define LOCK_LEVEL_FILESYSTEM   40  /**< Alias for LOCK_LEVEL_VFS */
#define LOCK_LEVEL_IPC          50  /**< IPC queues, pipes */
#define LOCK_LEVEL_CAPABILITY   60  /**< Capability tables */
#define LOCK_LEVEL_DEVICE       70  /**< Device drivers */
#define LOCK_LEVEL_USER         80  /**< User-visible resources */
#define LOCK_LEVEL_MAX          100 /**< Maximum level */

/* Lock type constants for DAG tracking */
#define LOCK_TYPE_QSPIN         0
#define LOCK_TYPE_ADAPTIVE      1
#define LOCK_TYPE_TOKEN         2
#define LOCK_TYPE_SLEEP         3

/* Maximum locks held simultaneously per thread */
#define MAX_HELD_LOCKS          16

/**
 * Per-lock acquisition record
 * Tracks when and where a lock was acquired
 */
struct lock_acquisition {
    void *lock_addr;           /**< Address of lock structure */
    const char *lock_name;     /**< Debug name */
    uint32_t dag_level;        /**< DAG level at acquisition */
    uint32_t lock_type;        /**< LOCK_TYPE_* constant */
    uint64_t acquire_tsc;      /**< Acquisition timestamp (TSC) */
    const char *file;          /**< Source file */
    int line;                  /**< Source line number */
} __attribute__((aligned(64)));

/**
 * Per-thread lock tracking
 * Stack of currently held locks for DAG validation
 */
struct thread_lock_tracker {
    struct lock_acquisition stack[MAX_HELD_LOCKS];
    uint32_t depth;            /**< Current stack depth */
    uint32_t max_depth;        /**< Maximum depth reached */
    uint32_t violations;       /**< DAG violations detected */
    uint32_t highest_level;    /**< Highest DAG level currently held */
} __attribute__((aligned(128)));

/**
 * Global DAG statistics
 */
struct dag_stats {
    _Atomic uint64_t total_acquisitions;
    _Atomic uint64_t dag_checks;
    _Atomic uint64_t violations_detected;
    _Atomic uint64_t violations_by_level[LOCK_LEVEL_MAX];
    _Atomic uint64_t max_chain_length;
} __attribute__((aligned(128)));

extern struct dag_stats global_dag_stats;

/* DAG API */

/**
 * Get current thread's lock tracker
 * @return Pointer to tracker or NULL if not available
 */
struct thread_lock_tracker *get_lock_tracker(void);

/**
 * Validate lock acquisition against DAG ordering
 * @param lock_addr Address of lock being acquired
 * @param name Lock name (debug)
 * @param dag_level DAG level of lock
 * @param lock_type Type of lock (LOCK_TYPE_*)
 * @param file Source file
 * @param line Source line
 * @return 1 if acquisition is safe, 0 if would violate DAG
 */
int dag_validate_acquisition(void *lock_addr, const char *name,
                             uint32_t dag_level, uint32_t lock_type,
                             const char *file, int line);

/**
 * Track lock acquisition in DAG
 * @param lock_addr Address of lock acquired
 * @param name Lock name (debug)
 * @param dag_level DAG level of lock
 * @param lock_type Type of lock (LOCK_TYPE_*)
 * @param file Source file
 * @param line Source line
 */
void dag_lock_acquired(void *lock_addr, const char *name,
                      uint32_t dag_level, uint32_t lock_type,
                      const char *file, int line);

/**
 * Track lock release in DAG
 * @param lock_addr Address of lock being released
 */
void dag_lock_released(void *lock_addr);

/**
 * Dump DAG statistics
 */
void dag_dump_stats(void);

/**
 * Reset DAG statistics
 */
void dag_reset_stats(void);

/**
 * Initialize DAG subsystem
 */
void dag_init(void);

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
