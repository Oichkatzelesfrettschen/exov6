#pragma once

/**
 * @file ultimate_lock_synthesis.h 
 * @brief Ultimate Lock Synthesis - All Repository Locks Unified
 * 
 * Complete synthesis of ALL lock implementations found in the repository:
 * 1. unified_lock.h/c - Core ticket/MCS/seqlock/RCU/rwlock framework
 * 2. zerocopy_cow_dag.h/c - Zero-copy CoW DAG with resurrection
 * 3. quaternion_spinlock.h - Quaternion-based fairness rotation
 * 4. uv_spinlock.h - LibUV-style simple atomic spinlock  
 * 5. modern_locks.c - CLH, flat combining, hazard pointers
 * 6. spinlock_c17.c - Pure C17 compliance layer
 * 7. sleeplock.c - Blocking locks for long critical sections
 * 8. Legacy locks (qspinlock, rspinlock) - Archived but available
 * 9. pthread_mutex.c - POSIX threading integration
 * 10. beatty_dag scheduler locks - DAG dependency tracking
 * 
 * This creates a unified meta-framework that can dynamically select
 * the optimal lock type from ALL available implementations based on
 * workload characteristics, mathematical analysis, and ML optimization.
 */

#include "unified_lock.h"
#include "zerocopy_cow_dag.h"
#include "quaternion_spinlock.h"
#include "uv_spinlock.h"
#include "posix_clock.h"
#include <stdint.h>
#include <stdatomic.h>

/* ============================================================================
 * Meta Lock Types - All Available Implementations
 * ============================================================================ */

typedef enum {
    /* Core Unified Lock Types */
    META_LOCK_TICKET = 0,        /* Ticket spinlock (FIFO fair) */
    META_LOCK_MCS,               /* MCS queue lock (NUMA-aware) */
    META_LOCK_SEQLOCK,           /* Sequence lock (read-heavy) */
    META_LOCK_RWLOCK,            /* Reader-writer lock */
    META_LOCK_RCU,               /* Read-copy-update */
    META_LOCK_SLEEPLOCK,         /* Blocking lock for long sections */
    
    /* Zero-Copy CoW DAG */
    META_LOCK_ZCOW_DAG,          /* ZCoW with resurrection */
    
    /* Specialized Implementations */
    META_LOCK_QUATERNION,        /* Quaternion fairness spinlock */
    META_LOCK_UV_SIMPLE,         /* LibUV simple spinlock */
    
    /* Advanced Modern Locks */
    META_LOCK_CLH,               /* CLH queue lock */
    META_LOCK_FLAT_COMBINING,    /* Flat combining for high contention */
    META_LOCK_HAZARD_POINTER,    /* Lock-free with hazard pointers */
    
    /* POSIX Integration */
    META_LOCK_PTHREAD_MUTEX,     /* POSIX pthread mutex */
    META_LOCK_PTHREAD_RWLOCK,    /* POSIX pthread rwlock */
    META_LOCK_PTHREAD_SPINLOCK,  /* POSIX pthread spinlock */
    
    /* Legacy/Archived */
    META_LOCK_QSPINLOCK,         /* Queued spinlock variant */
    META_LOCK_RSPINLOCK,         /* Recursive spinlock */
    
    /* ML-Optimized */
    META_LOCK_AI_ADAPTIVE,       /* AI/ML optimized selection */
    META_LOCK_NEURAL_PREDICT,    /* Neural network contention prediction */
    
    /* Quantum-Ready */
    META_LOCK_QUANTUM_PQ,        /* Quantum-ready with post-quantum crypto */
    META_LOCK_QUANTUM_ENTANGLED, /* Quantum entanglement for distributed locks */
    
    /* Genetically Evolved */
    META_LOCK_GENETIC_EVOLVED,   /* Genetically evolved algorithm */
    META_LOCK_HYBRID_EVOLVED,    /* Hybrid of multiple evolved algorithms */
    
    META_LOCK_TYPE_MAX
} meta_lock_type_t;

/* ============================================================================
 * Ultimate Lock Structure - Union of All Types
 * ============================================================================ */

typedef struct ultimate_lock {
    /* Current active type */
    _Alignas(64) atomic_uint32_t active_type;
    
    /* Union of all possible lock implementations */
    union {
        /* Core unified locks */
        exo_spinlock_t ticket;
        mcs_lock_t mcs;
        rwlock_t rwlock;
        seqlock_t seqlock;
        sleeplock_t sleeplock;
        rcu_state_t rcu;
        
        /* Zero-copy CoW DAG */
        zcow_lock_t zcow_dag;
        
        /* Specialized locks */
        qspin_lock_t quaternion;
        uv_spinlock_t uv_simple;
        
        /* Modern advanced locks */
        struct {
            atomic_uint64_t tail;      /* CLH lock */
            atomic_uint32_t combiner;  /* Flat combining */
            atomic_uintptr_t hazard;   /* Hazard pointer */
        } modern;
        
        /* POSIX locks */
        struct {
            atomic_uint32_t mutex;
            atomic_uint64_t rwlock;
            atomic_uint32_t spinlock;
        } posix;
        
        /* Legacy locks */
        struct {
            atomic_uint32_t qspinlock;
            atomic_uint32_t rspinlock;
        } legacy;
        
        /* Quantum-ready locks */
        struct {
            atomic_uint64_t quantum_state;    /* Post-quantum authenticated state */
            atomic_uint32_t pq_auth_gen;      /* Authentication generation */
            atomic_uint64_t entanglement_ref; /* Quantum entanglement reference */
        } quantum;
        
        /* Genetically evolved locks */
        struct {
            atomic_uintptr_t chromosome_ref;  /* Reference to lock_chromosome_t */
            atomic_uint64_t generation_id;    /* Generation number */
            atomic_uint32_t fitness_score;    /* Current fitness (scaled to uint32) */
            atomic_uint32_t mutation_count;   /* Number of mutations applied */
        } genetic;
        
    } impl;
    
    /* Meta-lock control structure */
    _Alignas(64) struct {
        /* Lock metadata */
        const char *name;
        uint32_t flags;
        cap_id_t required_cap;
        
        /* Performance characteristics */
        struct {
            atomic_uint64_t total_acquisitions;
            atomic_uint64_t total_contentions;
            atomic_uint64_t total_hold_time_ns;
            atomic_uint64_t total_wait_time_ns;
            atomic_uint32_t max_waiters;
            atomic_uint32_t avg_waiters;
        } perf;
        
        /* Workload analysis */
        struct {
            atomic_uint64_t read_ops;
            atomic_uint64_t write_ops;
            atomic_uint64_t short_holds;    /* < 1μs */
            atomic_uint64_t medium_holds;   /* 1μs - 1ms */
            atomic_uint64_t long_holds;     /* > 1ms */
            atomic_uint32_t numa_locality;  /* 0-100% */
        } workload;
        
        /* ML/AI optimization state */
        struct {
            float contention_probability;   /* Predicted contention [0,1] */
            float optimal_type_scores[META_LOCK_TYPE_MAX];
            uint32_t prediction_accuracy;   /* Percentage */
            uint64_t last_ml_update;       /* Timestamp of last ML update */
        } ai;
        
        /* Dynamic adaptation */
        struct {
            atomic_uint32_t adaptation_counter;
            atomic_uint64_t last_switch_time;
            atomic_uint32_t switch_cooldown_ms;
            atomic_bool adaptation_enabled;
        } adapt;
        
    } meta;
    
    /* Zero-copy read cache (separate cache line) */
    _Alignas(64) struct {
        atomic_uint64_t cached_state;    /* Cached lock state for fast reads */
        atomic_uint64_t cache_version;   /* Version for cache invalidation */
        atomic_uint32_t cache_hits;      /* Statistics */
        atomic_uint32_t cache_misses;
    } cache;
    
    /* Resurrection and temporal correction */
    struct {
        zcow_lock_t *zcow_shadow;       /* Shadow ZCoW for any lock type */
        atomic_bool resurrection_enabled;
        atomic_uint32_t checkpoint_version;
    } resurrection;
    
} ultimate_lock_t;

/* ============================================================================
 * Machine Learning Lock Optimizer
 * ============================================================================ */

typedef struct ml_lock_optimizer {
    /* Feature vectors for workload analysis */
    struct {
        float features[16];             /* Normalized feature vector */
        float weights[META_LOCK_TYPE_MAX][16]; /* Per-type weights */
        float bias[META_LOCK_TYPE_MAX];  /* Per-type bias */
    } neural_net;
    
    /* Performance history for training */
    struct {
        struct {
            float features[16];
            meta_lock_type_t optimal_type;
            float performance_score;
        } samples[1024];
        uint32_t sample_count;
        uint32_t current_sample;
    } training_data;
    
    /* Optimization state */
    struct {
        atomic_bool enabled;
        atomic_uint64_t last_training;
        atomic_uint32_t training_iterations;
        atomic_float learning_rate;
    } state;
    
} ml_lock_optimizer_t;

extern ml_lock_optimizer_t *global_ml_optimizer;

/* ============================================================================
 * Ultimate Lock Operations - Meta Interface
 * ============================================================================ */

/**
 * Initialize ultimate lock with auto-detection of optimal type
 */
void ultimate_lock_init(ultimate_lock_t *lock, const char *name);

/**
 * Acquire lock with automatic type selection and adaptation
 */
void ultimate_lock_acquire(ultimate_lock_t *lock);

/**
 * Try to acquire lock (non-blocking)
 */
bool ultimate_lock_tryacquire(ultimate_lock_t *lock);

/**
 * Release lock with performance feedback
 */
void ultimate_lock_release(ultimate_lock_t *lock);

/**
 * Check if lock is held (zero-copy fastpath)
 */
static inline bool ultimate_lock_is_held(ultimate_lock_t *lock) {
    /* Fast cache lookup first */
    uint64_t cached = atomic_load_explicit(&lock->cache.cached_state,
                                          memory_order_acquire);
    if (cached != 0) {
        atomic_fetch_add_explicit(&lock->cache.cache_hits, 1,
                                 memory_order_relaxed);
        return true;
    }
    
    atomic_fetch_add_explicit(&lock->cache.cache_misses, 1,
                             memory_order_relaxed);
    
    /* Delegate to active implementation */
    meta_lock_type_t type = atomic_load_explicit(&lock->active_type,
                                                memory_order_acquire);
    
    switch (type) {
        case META_LOCK_TICKET:
            return exo_spinlock_is_held(&lock->impl.ticket);
        case META_LOCK_ZCOW_DAG:
            return zcow_is_locked(&lock->impl.zcow_dag);
        case META_LOCK_QUATERNION:
            return qspin_holding(&lock->impl.quaternion);
        case META_LOCK_UV_SIMPLE:
            return lock->impl.uv_simple.lock != 0;
        /* ... other types */
        default:
            return false;
    }
}

/* ============================================================================
 * Advanced Meta Operations
 * ============================================================================ */

/**
 * Force switch to specific lock type
 */
void ultimate_lock_switch_type(ultimate_lock_t *lock, meta_lock_type_t new_type);

/**
 * Enable/disable automatic adaptation
 */
void ultimate_lock_set_adaptive(ultimate_lock_t *lock, bool enabled);

/**
 * Get comprehensive lock metrics
 */
void ultimate_lock_get_metrics(ultimate_lock_t *lock, 
                              struct ultimate_lock_metrics *metrics);

/**
 * Visualize lock state and history (for debugging)
 */
void ultimate_lock_visualize(ultimate_lock_t *lock, char *buffer, size_t size);

/* ============================================================================
 * ML/AI Lock Optimization
 * ============================================================================ */

/**
 * Initialize ML optimizer
 */
void ml_optimizer_init(void);

/**
 * Train ML model on lock performance data
 */
void ml_optimizer_train(void);

/**
 * Predict optimal lock type for given workload
 */
meta_lock_type_t ml_optimizer_predict(ultimate_lock_t *lock);

/**
 * Update ML model with performance feedback
 */
void ml_optimizer_feedback(ultimate_lock_t *lock, 
                          meta_lock_type_t type,
                          float performance_score);

/* ============================================================================
 * Multi-Lock Operations (Global Coordination)
 * ============================================================================ */

/**
 * Acquire multiple locks in deadlock-free order
 * Uses global deadlock detection and resolution
 */
int ultimate_multilock_acquire(ultimate_lock_t **locks, int count, int timeout_ms);

/**
 * Release all locks held by current thread
 */
void ultimate_multilock_release_all(void);

/**
 * Global deadlock detection and resolution
 */
int ultimate_deadlock_resolve(void);

/**
 * Create checkpoint of all locks for resurrection
 */
void ultimate_checkpoint_all(void);

/**
 * Restore all locks from checkpoint (after crash/deadlock)
 */
void ultimate_restore_all(uint32_t checkpoint_id);

/* ============================================================================
 * Integration Bridges to Existing Code
 * ============================================================================ */

/**
 * Convert any existing lock type to ultimate lock
 */
ultimate_lock_t *ultimate_from_spinlock(exo_spinlock_t *spinlock);
ultimate_lock_t *ultimate_from_sleeplock(sleeplock_t *sleeplock);
ultimate_lock_t *ultimate_from_zcow(zcow_lock_t *zcow);
ultimate_lock_t *ultimate_from_quaternion(qspin_lock_t *qlock);

/**
 * Legacy API compatibility (drop-in replacements)
 */
#ifdef ULTIMATE_LOCK_COMPAT
#define spinlock ultimate_lock_t
#define acquire(l) ultimate_lock_acquire(l)
#define release(l) ultimate_lock_release(l)
#define holding(l) ultimate_lock_is_held(l)
#define initlock(l, n) ultimate_lock_init(l, n)
#endif

/* ============================================================================
 * Performance Tuning and Optimization
 * ============================================================================ */

/**
 * Performance tuning parameters
 */
struct ultimate_lock_params {
    /* Adaptation thresholds */
    uint32_t contention_switch_threshold;   /* Switch if contention > this */
    uint32_t hold_time_switch_threshold;    /* Switch based on hold time */
    uint32_t numa_locality_threshold;       /* NUMA-aware switching */
    
    /* ML parameters */
    float ml_learning_rate;                 /* Neural network learning rate */
    uint32_t ml_training_interval_ms;       /* How often to retrain */
    uint32_t ml_history_size;               /* Training data history */
    
    /* Cache parameters */
    uint32_t cache_invalidation_ms;         /* Cache TTL */
    uint32_t cache_warmup_samples;          /* Samples before caching */
    
    /* Resurrection parameters */
    uint32_t checkpoint_interval_ms;        /* Auto-checkpoint frequency */
    uint32_t history_retention_hours;       /* How long to keep history */
};

extern struct ultimate_lock_params ultimate_lock_config;

/**
 * Tune performance parameters
 */
void ultimate_lock_tune(struct ultimate_lock_params *params);

/**
 * Run comprehensive benchmarks on all lock types
 */
void ultimate_lock_benchmark(void);

/* ============================================================================
 * Debugging and Diagnostics
 * ============================================================================ */

/**
 * Dump global lock state for debugging
 */
void ultimate_lock_dump_global_state(void);

/**
 * Verify all lock invariants
 */
bool ultimate_lock_verify_invariants(void);

/**
 * Export performance data for analysis
 */
void ultimate_lock_export_perf_data(const char *filename);

/* ============================================================================
 * Compile-Time Configuration
 * ============================================================================ */

/* Enable specific lock types */
#ifndef ULTIMATE_ENABLE_ALL_TYPES
#define ULTIMATE_ENABLE_ALL_TYPES 1
#endif

#ifndef ULTIMATE_ENABLE_ML
#define ULTIMATE_ENABLE_ML 1
#endif

#ifndef ULTIMATE_ENABLE_RESURRECTION
#define ULTIMATE_ENABLE_RESURRECTION 1
#endif

/* Performance vs space tradeoffs */
#ifndef ULTIMATE_CACHE_SIZE
#define ULTIMATE_CACHE_SIZE 1024
#endif

#ifndef ULTIMATE_HISTORY_SIZE
#define ULTIMATE_HISTORY_SIZE 256
#endif

/* ============================================================================
 * Static Assertions for Correctness
 * ============================================================================ */

_Static_assert(sizeof(ultimate_lock_t) <= 16384, "Ultimate lock too large");
_Static_assert(_Alignof(ultimate_lock_t) >= 64, "Must be cache-aligned");
_Static_assert(META_LOCK_TYPE_MAX < 32, "Too many lock types for bitfield");

#endif /* ULTIMATE_LOCK_SYNTHESIS_H */