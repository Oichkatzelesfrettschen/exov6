#pragma once

/**
 * @file zerocopy_cow_dag.h
 * @brief Zero-Copy Copy-on-Write DAG Lock Framework with Resurrection
 * 
 * Implements a revolutionary lock architecture combining:
 * - Zero-copy fastpath for uncontended locks
 * - Copy-on-Write semantics for lock state transitions
 * - DAG-based dependency tracking for deadlock prevention
 * - Minix-style resurrection server for temporal corrections
 * - Checkpoint/restore for lock state recovery
 * 
 * Key innovations:
 * - Lock states as immutable DAG nodes (functional approach)
 * - Temporal versioning for lock history replay
 * - Zero-copy reader fastpath using RCU + seqlock
 * - Automatic deadlock resolution via DAG analysis
 * - Crash-consistent lock recovery
 */

#include <stdint.h>
#include <stdatomic.h>
#include <stdbool.h>
#include "unified_lock.h"
#include "posix_clock.h"
#include "cap.h"

/* ============================================================================
 * Core Types and Constants
 * ============================================================================ */

#define MAX_LOCK_DEPTH 64       /* Maximum lock nesting depth */
#define MAX_LOCK_HISTORY 256    /* Lock state history for resurrection */
#define RESURRECTION_INTERVAL_MS 100  /* Checkpoint interval */

/* Lock state represented as immutable DAG node */
typedef struct lock_dag_node {
    /* Immutable lock state (Copy-on-Write) */
    struct {
        uint64_t version;           /* Monotonic version number */
        uint64_t timestamp_ns;      /* Acquisition timestamp */
        int32_t owner_cpu;          /* CPU holding lock (-1 = free) */
        int32_t owner_pid;          /* Process holding lock */
        cap_id_t required_cap;      /* Required capability */
        uint32_t hold_count;        /* Recursive hold count */
    } state;
    
    /* DAG structure (immutable pointers) */
    struct lock_dag_node *parent;  /* Previous state */
    struct lock_dag_node *children[8]; /* Next states (branching) */
    uint32_t child_count;
    
    /* Dependency tracking */
    struct lock_dag_node *deps[MAX_LOCK_DEPTH]; /* Locks this depends on */
    uint32_t dep_count;
    
    /* Reference counting for GC */
    atomic_uint32_t refcount;
    
    /* RCU for safe reclamation */
    struct rcu_head rcu;
} lock_dag_node_t;

/* Zero-copy CoW lock structure */
typedef struct zcow_lock {
    /* Current state pointer (RCU protected) */
    _Alignas(64) _Atomic(lock_dag_node_t *) current;
    
    /* Seqlock for zero-copy reads */
    atomic_uint64_t sequence;
    
    /* Lock metadata */
    const char *name;
    lock_type_t type;
    uint32_t flags;
    
    /* History ring buffer for resurrection */
    struct {
        lock_dag_node_t *states[MAX_LOCK_HISTORY];
        uint32_t head;
        uint32_t tail;
    } history;
    
    /* Statistics */
    _Alignas(64) struct {
        atomic_uint64_t acquisitions;
        atomic_uint64_t zero_copy_reads;
        atomic_uint64_t cow_transitions;
        atomic_uint64_t resurrections;
        atomic_uint64_t deadlocks_resolved;
    } stats;
    
    /* Resurrection checkpoint */
    struct {
        lock_dag_node_t *checkpoint;   /* Last known good state */
        uint64_t checkpoint_time;       /* Checkpoint timestamp */
        uint32_t checkpoint_version;    /* Checkpoint version */
    } resurrection;
    
} zcow_lock_t;

/* Resurrection server state */
typedef struct resurrection_server {
    /* Global lock registry */
    struct {
        zcow_lock_t *locks[4096];      /* All registered locks */
        uint32_t count;
        atomic_uint32_t version;        /* Global version counter */
    } registry;
    
    /* Checkpoint ring buffer */
    struct {
        struct checkpoint {
            uint64_t timestamp;
            uint32_t version;
            lock_dag_node_t *states[4096]; /* Snapshot of all lock states */
        } checkpoints[16];
        uint32_t current;
    } checkpoints;
    
    /* Deadlock detector state */
    struct {
        atomic_bool enabled;
        uint64_t last_scan;
        uint32_t deadlocks_found;
        uint32_t deadlocks_resolved;
    } detector;
    
    /* Temporal correction state */
    struct {
        bool replay_mode;              /* Are we replaying history? */
        uint64_t replay_target;         /* Target timestamp */
        uint32_t corrections_made;      /* Number of corrections */
    } temporal;
    
} resurrection_server_t;

/* Global resurrection server */
extern resurrection_server_t *resurrection_server;

/* ============================================================================
 * Zero-Copy Read Operations (Fastpath)
 * ============================================================================ */

/**
 * Zero-copy lock state read
 * Uses seqlock + RCU for wait-free reads
 */
static inline bool zcow_is_locked(zcow_lock_t *lock) {
    uint64_t seq;
    bool locked;
    
    do {
        seq = atomic_load_explicit(&lock->sequence, memory_order_acquire);
        if (seq & 1) {
            __builtin_ia32_pause();
            continue;
        }
        
        /* RCU read-side critical section */
        lock_dag_node_t *node = atomic_load_explicit(&lock->current, 
                                                     memory_order_consume);
        locked = (node && node->state.owner_cpu >= 0);
        
        atomic_thread_fence(memory_order_acquire);
    } while (seq != atomic_load_explicit(&lock->sequence, memory_order_acquire));
    
    atomic_fetch_add_explicit(&lock->stats.zero_copy_reads, 1, 
                             memory_order_relaxed);
    return locked;
}

/**
 * Zero-copy owner check
 */
static inline bool zcow_is_owner(zcow_lock_t *lock, int cpu, int pid) {
    lock_dag_node_t *node = atomic_load_explicit(&lock->current,
                                                 memory_order_consume);
    return node && node->state.owner_cpu == cpu && 
           node->state.owner_pid == pid;
}

/* ============================================================================
 * Copy-on-Write State Transitions
 * ============================================================================ */

/**
 * Create new lock state (Copy-on-Write)
 * Old state remains immutable, new state created
 */
lock_dag_node_t *zcow_create_state(lock_dag_node_t *parent,
                                   int owner_cpu, int owner_pid);

/**
 * Transition lock to new state atomically
 */
bool zcow_transition(zcow_lock_t *lock, lock_dag_node_t *new_state);

/**
 * Acquire lock with CoW semantics
 */
int zcow_acquire(zcow_lock_t *lock, int timeout_ms);

/**
 * Release lock with state transition
 */
int zcow_release(zcow_lock_t *lock);

/* ============================================================================
 * DAG Operations for Dependency Tracking
 * ============================================================================ */

/**
 * Add dependency edge in lock DAG
 * Returns false if would create cycle (deadlock)
 */
bool zcow_add_dependency(zcow_lock_t *held, zcow_lock_t *wanted);

/**
 * Check if acquiring lock would cause deadlock
 */
bool zcow_would_deadlock(zcow_lock_t *lock, int pid);

/**
 * Find and break deadlock cycles
 * Returns number of locks forcibly released
 */
int zcow_break_deadlock(void);

/**
 * Topological sort of lock DAG for acquisition order
 */
int zcow_topo_sort(zcow_lock_t **locks, int count);

/* ============================================================================
 * Resurrection and Temporal Correction
 * ============================================================================ */

/**
 * Initialize resurrection server
 */
void resurrection_init(void);

/**
 * Register lock with resurrection server
 */
void resurrection_register(zcow_lock_t *lock);

/**
 * Create checkpoint of all lock states
 */
void resurrection_checkpoint(void);

/**
 * Restore locks to previous checkpoint
 * Used after crash or deadlock
 */
void resurrection_restore(uint32_t checkpoint_version);

/**
 * Replay lock history to specific timestamp
 * Allows temporal debugging and correction
 */
void resurrection_replay_to(uint64_t target_timestamp);

/**
 * Correct temporal anomaly in lock history
 * Fixes out-of-order acquisitions
 */
void resurrection_correct_temporal(zcow_lock_t *lock, 
                                  uint64_t when,
                                  lock_dag_node_t *correct_state);

/**
 * Garbage collect old DAG nodes
 */
void resurrection_gc(void);

/* ============================================================================
 * Advanced Lock Operations
 * ============================================================================ */

/**
 * Multi-lock acquisition with deadlock prevention
 * Sorts locks by address to prevent circular wait
 */
int zcow_acquire_multiple(zcow_lock_t **locks, int count, int timeout_ms);

/**
 * Release all locks held by process
 * Used during process cleanup
 */
void zcow_release_all(int pid);

/**
 * Transfer lock ownership atomically
 * Used for priority inheritance
 */
int zcow_transfer(zcow_lock_t *lock, int new_cpu, int new_pid);

/**
 * Upgrade read lock to write lock
 */
int zcow_upgrade(zcow_lock_t *lock);

/**
 * Downgrade write lock to read lock
 */
int zcow_downgrade(zcow_lock_t *lock);

/* ============================================================================
 * Lock Introspection and Debugging
 * ============================================================================ */

/**
 * Get lock history as DAG
 */
lock_dag_node_t *zcow_get_history(zcow_lock_t *lock, int max_depth);

/**
 * Visualize lock DAG (outputs DOT format)
 */
void zcow_visualize_dag(zcow_lock_t *lock, char *buffer, size_t size);

/**
 * Dump resurrection server state
 */
void resurrection_dump_state(void);

/**
 * Verify lock invariants
 */
bool zcow_verify_invariants(zcow_lock_t *lock);

/* ============================================================================
 * Performance Monitoring
 * ============================================================================ */

typedef struct zcow_metrics {
    uint64_t avg_acquire_ns;       /* Average acquisition time */
    uint64_t avg_hold_ns;          /* Average hold time */
    uint64_t p99_acquire_ns;       /* 99th percentile acquisition */
    uint64_t zero_copy_ratio;      /* Percentage of zero-copy reads */
    uint64_t cow_overhead_ns;      /* CoW transition overhead */
    uint64_t resurrection_time_ns; /* Time to restore from checkpoint */
    uint32_t dag_depth;            /* Current DAG depth */
    uint32_t dag_width;            /* Maximum DAG width */
} zcow_metrics_t;

/**
 * Get performance metrics
 */
void zcow_get_metrics(zcow_lock_t *lock, zcow_metrics_t *metrics);

/* ============================================================================
 * Integration with Unified Lock System
 * ============================================================================ */

/**
 * Convert unified lock to ZCoW lock
 */
zcow_lock_t *zcow_from_unified(exo_spinlock_t *lock);

/**
 * Bridge to existing spinlock API
 */
#define zcow_spinlock_init(l, n) zcow_init(l, n, LOCK_TYPE_TICKET)
#define zcow_spinlock_acquire(l) zcow_acquire(l, -1)
#define zcow_spinlock_release(l) zcow_release(l)

/* ============================================================================
 * Compile-Time Configuration
 * ============================================================================ */

/* Enable resurrection server by default */
#ifndef ZCOW_ENABLE_RESURRECTION
#define ZCOW_ENABLE_RESURRECTION 1
#endif

/* Enable deadlock detection by default */
#ifndef ZCOW_ENABLE_DEADLOCK_DETECTION
#define ZCOW_ENABLE_DEADLOCK_DETECTION 1
#endif

/* Enable temporal correction (experimental) */
#ifndef ZCOW_ENABLE_TEMPORAL
#define ZCOW_ENABLE_TEMPORAL 1
#endif

/* ============================================================================
 * Static Assertions
 * ============================================================================ */

_Static_assert(sizeof(lock_dag_node_t) <= 512, "DAG node too large");
_Static_assert(sizeof(zcow_lock_t) <= 8192, "Lock structure too large");
_Static_assert(_Alignof(zcow_lock_t) >= 64, "Lock must be cache-aligned");

#endif /* ZEROCOPY_COW_DAG_H */