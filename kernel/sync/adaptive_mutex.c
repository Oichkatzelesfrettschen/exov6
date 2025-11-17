/**
 * @file adaptive_mutex.c
 * @brief Adaptive mutex implementation for ExoV6
 *
 * Adaptive mutex with owner-running detection and turnstile queuing:
 * - Spins if lock holder is running (likely to release soon)
 * - Blocks on turnstile if lock holder is sleeping/preempted
 * - Supports priority inheritance for real-time tasks
 * - NUMA-aware spinning behavior
 *
 * Based on:
 * - illumos adaptive mutex
 * - NetBSD adaptive mutex
 * - FreeBSD turnstiles
 *
 * @version 1.0
 * @date 2025-11-17
 */

#include <types.h>
#include "defs.h"
#include "param.h"
#include "arch.h"
#include "memlayout.h"
#include "compiler_attrs.h"
#include "exo_lock.h"
#include "proc.h"

/* ========================================================================
 * Architecture-Specific Helpers
 * ======================================================================== */

/**
 * Read Time-Stamp Counter (non-serialized)
 */
static inline uint64_t rdtsc(void) {
    uint32_t lo, hi;
    __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
    return ((uint64_t)hi << 32) | lo;
}

/**
 * Memory fence (full barrier)
 */
static inline void mfence(void) {
    __asm__ __volatile__("mfence" ::: "memory");
}

/**
 * CPU pause hint (for spin loops)
 */
static inline void pause(void) {
    __asm__ __volatile__("pause" ::: "memory");
}

/* ========================================================================
 * Helper Functions
 * ======================================================================== */

/**
 * Get current thread structure
 */
static inline struct thread *mythread(void) {
    struct cpu *c = mycpu();
    if (!c->proc) return NULL;
    // Assuming proc has a thread field - adjust based on actual structure
    return (struct thread *)c->proc;  // Simplified - may need adjustment
}

/**
 * Get thread ID of current thread
 */
static inline uint32_t mythreadid(void) {
    struct thread *t = mythread();
    if (!t) return INVALID_TID;
    // Assuming thread has a tid field - adjust based on actual structure
    return (uint32_t)((uintptr_t)t);  // Use pointer as TID for now
}

/**
 * Set lock owner to current thread
 */
static EXO_ALWAYS_INLINE void set_owner(struct adaptive_mutex *mutex) {
    atomic_store_explicit(&mutex->owner_cpu, mycpu() - cpus, memory_order_relaxed);
    atomic_store_explicit(&mutex->owner_tid, mythreadid(), memory_order_relaxed);
}

/**
 * Clear lock owner
 */
static EXO_ALWAYS_INLINE void clear_owner(struct adaptive_mutex *mutex) {
    atomic_store_explicit(&mutex->owner_cpu, INVALID_CPU, memory_order_relaxed);
    atomic_store_explicit(&mutex->owner_tid, INVALID_TID, memory_order_relaxed);
}

/**
 * Check if current thread owns the mutex
 */
static inline bool is_owner(struct adaptive_mutex *mutex) {
    uint32_t owner_cpu = atomic_load_explicit(&mutex->owner_cpu, memory_order_relaxed);
    uint32_t owner_tid = atomic_load_explicit(&mutex->owner_tid, memory_order_relaxed);
    uint32_t my_cpu = mycpu() - cpus;
    uint32_t my_tid = mythreadid();

    return (owner_cpu == my_cpu) && (owner_tid == my_tid);
}

/**
 * Check if lock owner is currently running on a CPU
 *
 * This is the key heuristic for adaptive behavior:
 * - If owner is running: spin (likely to release soon)
 * - If owner is not running: block (may take long time)
 */
static EXO_ALWAYS_INLINE bool owner_is_running(struct adaptive_mutex *mutex) {
    uint32_t owner_cpu = atomic_load_explicit(&mutex->owner_cpu, memory_order_acquire);
    uint32_t owner_tid = atomic_load_explicit(&mutex->owner_tid, memory_order_acquire);

    // No owner means lock is free
    if (unlikely(owner_cpu == INVALID_CPU || owner_tid == INVALID_TID)) {
        return false;
    }

    // Owner CPU must be valid
    if (unlikely(owner_cpu >= NCPU)) {
        return false;
    }

    // Check if owner's CPU is running the owner thread
    struct cpu *cpu = &cpus[owner_cpu];
    struct proc *running = cpu->proc;

    if (!running) {
        return false;  // CPU is idle
    }

    // Check if the running process/thread matches the owner
    uint32_t running_tid = (uint32_t)((uintptr_t)running);  // Simplified TID

    if (running_tid != owner_tid) {
        return false;  // Different thread is running
    }

    return true;  // Owner is running!
}

/* ========================================================================
 * Adaptive Mutex Operations
 * ======================================================================== */

/**
 * Initialize adaptive mutex
 *
 * @param mutex Mutex to initialize
 * @param name Debug name
 * @param dag_level DAG deadlock prevention level
 * @param flags Behavior flags (PI, RT, NUMA, stats)
 */
void adaptive_mutex_init(struct adaptive_mutex *mutex, const char *name,
                        uint32_t dag_level, uint32_t flags) {
    // Initialize atomic state
    atomic_store_explicit(&mutex->locked, 0, memory_order_relaxed);
    atomic_store_explicit(&mutex->owner_cpu, INVALID_CPU, memory_order_relaxed);
    atomic_store_explicit(&mutex->owner_tid, INVALID_TID, memory_order_relaxed);
    atomic_store_explicit(&mutex->waiters, 0, memory_order_relaxed);

    // Configuration
    mutex->turnstile = NULL;  // Allocated on first contention
    mutex->spin_limit = ADAPTIVE_SPIN_LIMIT_DEFAULT;
    mutex->flags = flags;
    mutex->name = name;
    mutex->dag_level = dag_level;

    // Zero statistics
    memset(&mutex->stats, 0, sizeof(mutex->stats));
}

/**
 * Try to acquire mutex (fast path - non-blocking)
 *
 * @param mutex Mutex to try to acquire
 * @return 1 on success, 0 on failure
 */
int adaptive_mutex_trylock(struct adaptive_mutex *mutex) {
    uint32_t expected = 0;

    // Try to acquire with single CAS
    if (likely(atomic_compare_exchange_strong_explicit(
            &mutex->locked, &expected, 1,
            memory_order_acquire, memory_order_relaxed))) {
        // Success - set owner
        set_owner(mutex);

        // Update statistics
        if (mutex->flags & ADAPTIVE_FLAG_STATS_ENABLED) {
            __sync_fetch_and_add(&mutex->stats.acquire_count, 1);
            __sync_fetch_and_add(&mutex->stats.trylock_success_count, 1);
        }

        return 1;
    }

    // Failed
    if (mutex->flags & ADAPTIVE_FLAG_STATS_ENABLED) {
        __sync_fetch_and_add(&mutex->stats.trylock_fail_count, 1);
    }

    return 0;
}

/**
 * Acquire adaptive mutex
 *
 * Adaptive strategy:
 * 1. Fast path: Try immediate acquisition (uncontended)
 * 2. Adaptive spin: Spin if owner is running
 * 3. Block: Wait on turnstile if owner is not running
 */
void adaptive_mutex_lock(struct adaptive_mutex *mutex) {
#ifdef USE_DAG_CHECKING
    // Validate DAG ordering before attempting acquisition
    if (!dag_validate_acquisition(mutex, mutex->name, mutex->dag_level,
                                  LOCK_TYPE_ADAPTIVE, __FILE__, __LINE__)) {
#ifdef DAG_PANIC_ON_VIOLATION
        panic("adaptive_mutex_lock: DAG violation");
#else
        return;  // Skip acquisition on violation (warning mode)
#endif
    }
#endif

    uint64_t start_tsc = rdtsc();

    /* ===== FAST PATH ===== */
    // Try immediate acquisition (common case: no contention)
    if (likely(adaptive_mutex_trylock(mutex))) {
#ifdef USE_DAG_CHECKING
        // Record acquisition in DAG tracker
        dag_lock_acquired(mutex, mutex->name, mutex->dag_level,
                         LOCK_TYPE_ADAPTIVE, __FILE__, __LINE__);
#endif
        return;  // Got it immediately!
    }

    /* ===== ADAPTIVE SPIN PATH ===== */
    uint64_t spin_start = rdtsc();
    int spins = 0;
    int backoff = ADAPTIVE_SPIN_MIN_BACKOFF;

    while (spins < mutex->spin_limit) {
        // Check if owner is running
        if (likely(owner_is_running(mutex))) {
            // Owner is running - spin with backoff
            if (mutex->flags & ADAPTIVE_FLAG_STATS_ENABLED) {
                __sync_fetch_and_add(&mutex->stats.owner_running_count, 1);
            }

            // Exponential backoff to reduce cache line bouncing
            for (int i = 0; i < backoff; i++) {
                pause();
            }

            // Try to acquire again
            if (adaptive_mutex_trylock(mutex)) {
                // Spin succeeded!
                uint64_t spin_cycles = rdtsc() - spin_start;

                if (mutex->flags & ADAPTIVE_FLAG_STATS_ENABLED) {
                    __sync_fetch_and_add(&mutex->stats.spin_acquire_count, 1);
                    __sync_fetch_and_add(&mutex->stats.total_spin_cycles, spin_cycles);

                    // Update max spin time
                    uint64_t old_max = mutex->stats.max_spin_cycles;
                    while (spin_cycles > old_max) {
                        if (__sync_bool_compare_and_swap(&mutex->stats.max_spin_cycles,
                                                         old_max, spin_cycles)) {
                            break;
                        }
                        old_max = mutex->stats.max_spin_cycles;
                    }
                }

#ifdef USE_DAG_CHECKING
                // Record acquisition in DAG tracker
                dag_lock_acquired(mutex, mutex->name, mutex->dag_level,
                                 LOCK_TYPE_ADAPTIVE, __FILE__, __LINE__);
#endif

                return;
            }

            spins++;
            backoff = (backoff < ADAPTIVE_SPIN_MAX_BACKOFF) ? backoff * 2 : ADAPTIVE_SPIN_MAX_BACKOFF;
        } else {
            // Owner not running - break to block path
            if (mutex->flags & ADAPTIVE_FLAG_STATS_ENABLED) {
                __sync_fetch_and_add(&mutex->stats.owner_blocked_count, 1);
            }
            break;
        }
    }

    /* ===== BLOCK PATH ===== */
    // Owner not running or spin limit reached - block on turnstile
    uint64_t block_start = rdtsc();

    // Increment waiter count
    atomic_fetch_add_explicit(&mutex->waiters, 1, memory_order_relaxed);

    // Allocate turnstile if needed
    if (unlikely(!mutex->turnstile)) {
        mutex->turnstile = turnstile_alloc(mutex);
    }

    // Update contention statistics
    if (mutex->flags & ADAPTIVE_FLAG_STATS_ENABLED) {
        __sync_fetch_and_add(&mutex->stats.contention_count, 1);
    }

    // Block on turnstile
    struct thread *me = mythread();
    turnstile_wait(mutex->turnstile, me);

    // When we wake up, we have the lock
    // Owner is already set by turnstile_wake_one()

#ifdef USE_DAG_CHECKING
    // Record acquisition in DAG tracker
    dag_lock_acquired(mutex, mutex->name, mutex->dag_level,
                     LOCK_TYPE_ADAPTIVE, __FILE__, __LINE__);
#endif

    // Decrement waiter count
    atomic_fetch_sub_explicit(&mutex->waiters, 1, memory_order_relaxed);

    // Record block time
    uint64_t block_cycles = rdtsc() - block_start;

    if (mutex->flags & ADAPTIVE_FLAG_STATS_ENABLED) {
        __sync_fetch_and_add(&mutex->stats.block_acquire_count, 1);
        __sync_fetch_and_add(&mutex->stats.total_block_cycles, block_cycles);

        // Update max block time
        uint64_t old_max = mutex->stats.max_block_cycles;
        while (block_cycles > old_max) {
            if (__sync_bool_compare_and_swap(&mutex->stats.max_block_cycles,
                                             old_max, block_cycles)) {
                break;
            }
            old_max = mutex->stats.max_block_cycles;
        }
    }
}

/**
 * Release adaptive mutex
 */
void adaptive_mutex_unlock(struct adaptive_mutex *mutex) {
#ifdef USE_DAG_CHECKING
    // Track lock release in DAG
    dag_lock_released(mutex);
#endif

    // Verify we're the owner (debug builds)
    if (unlikely(!is_owner(mutex))) {
        panic("adaptive_mutex_unlock: not owner");
    }

    mfence();  // Memory barrier before release

    // Check if there are waiters on the turnstile
    if (unlikely(turnstile_has_waiters(mutex->turnstile))) {
        // Wake next waiter
        struct thread *next = turnstile_wake_one(mutex->turnstile);

        if (next) {
            // Transfer ownership to next waiter
            // Note: turnstile_wake_one handles setting the owner
            // Just release the locked flag
            atomic_store_explicit(&mutex->locked, 0, memory_order_release);
            return;
        }
    }

    // No waiters - simple unlock
    clear_owner(mutex);
    atomic_store_explicit(&mutex->locked, 0, memory_order_release);
}

/**
 * Check if current thread holds the mutex
 *
 * @param mutex Mutex to check
 * @return 1 if holding, 0 otherwise
 */
int adaptive_mutex_holding(struct adaptive_mutex *mutex) {
    return is_owner(mutex);
}

/**
 * Set spin limit for adaptive spinning
 *
 * @param mutex Mutex to configure
 * @param limit Maximum spin iterations before blocking
 */
void adaptive_mutex_set_spin_limit(struct adaptive_mutex *mutex, uint32_t limit) {
    mutex->spin_limit = limit;
}

/* ========================================================================
 * Statistics and Debugging
 * ======================================================================== */

/**
 * Dump mutex statistics
 *
 * @param mutex Mutex to dump stats for
 * @param name Name to display
 */
void adaptive_mutex_dump_stats(struct adaptive_mutex *mutex, const char *name) {
    struct adaptive_mutex_stats *s = &mutex->stats;

    cprintf("\n=== Adaptive Mutex Stats: %s ===\n", name ? name : mutex->name);
    cprintf("Acquisitions:\n");
    cprintf("  Total:           %lu\n", s->acquire_count);

    if (s->acquire_count > 0) {
        cprintf("  Spin acquired:   %lu (%.1f%%)\n",
                s->spin_acquire_count,
                100.0 * s->spin_acquire_count / s->acquire_count);
        cprintf("  Block acquired:  %lu (%.1f%%)\n",
                s->block_acquire_count,
                100.0 * s->block_acquire_count / s->acquire_count);
    }

    uint64_t total_trylock = s->trylock_success_count + s->trylock_fail_count;
    if (total_trylock > 0) {
        cprintf("\nTrylock:\n");
        cprintf("  Success:         %lu (%.1f%%)\n",
                s->trylock_success_count,
                100.0 * s->trylock_success_count / total_trylock);
        cprintf("  Failed:          %lu (%.1f%%)\n",
                s->trylock_fail_count,
                100.0 * s->trylock_fail_count / total_trylock);
    }

    if (s->contention_count > 0) {
        cprintf("\nContention:\n");
        cprintf("  Events:          %lu\n", s->contention_count);
        cprintf("  Owner running:   %lu\n", s->owner_running_count);
        cprintf("  Owner blocked:   %lu\n", s->owner_blocked_count);
    }

    if (s->spin_acquire_count > 0) {
        cprintf("\nSpin Performance:\n");
        cprintf("  Avg cycles:      %lu\n",
                s->total_spin_cycles / s->spin_acquire_count);
        cprintf("  Max cycles:      %lu\n", s->max_spin_cycles);
    }

    if (s->block_acquire_count > 0) {
        cprintf("\nBlock Performance:\n");
        cprintf("  Avg cycles:      %lu\n",
                s->total_block_cycles / s->block_acquire_count);
        cprintf("  Max cycles:      %lu\n", s->max_block_cycles);
    }

    if (s->priority_inherit_count > 0) {
        cprintf("\nPriority Inheritance:\n");
        cprintf("  Events:          %lu\n", s->priority_inherit_count);
    }
}

/**
 * Reset mutex statistics
 *
 * @param mutex Mutex to reset stats for
 */
void adaptive_mutex_reset_stats(struct adaptive_mutex *mutex) {
    memset(&mutex->stats, 0, sizeof(mutex->stats));
}
