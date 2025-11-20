/**
 * @file dag.c
 * @brief DAG (Directed Acyclic Graph) lock ordering for deadlock prevention
 *
 * Implements hierarchical lock ordering to prevent deadlocks:
 * - Locks are assigned levels in a DAG hierarchy
 * - Locks must be acquired in strictly increasing order
 * - Violations are detected at runtime and reported
 * - Per-thread tracking of held locks
 *
 * Based on:
 * - Solaris lock_lint
 * - FreeBSD witness(4)
 * - Linux lockdep
 *
 * @version 1.0
 * @date 2025-11-17
 */

#include <types.h>
#include <string.h>
#include "defs.h"
#include "param.h"
#include "arch.h"
#include "memlayout.h"
#include "exo_lock.h"
#include "proc.h"

/* ========================================================================
 * Architecture-Specific Helpers
 * ======================================================================== */

/**
 * Read Time-Stamp Counter
 */
static inline __attribute__((unused)) uint64_t rdtsc(void) {
    uint32_t lo, hi;
    __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
    return ((uint64_t)hi << 32) | lo;
}

/* ========================================================================
 * Global DAG Statistics
 * ======================================================================== */

struct dag_stats global_dag_stats = {
    .total_acquisitions = 0,
    .dag_checks = 0,
    .violations_detected = 0,
    .max_chain_length = 0,
};

/* ========================================================================
 * Per-Thread Lock Tracker Access
 * ======================================================================== */

/**
 * Get current thread's lock tracker
 *
 * @return Pointer to tracker or NULL if not available
 */
struct thread_lock_tracker *get_lock_tracker(void) {
#ifdef USE_DAG_CHECKING
    struct proc *p = myproc();
    if (p) {
        return &p->lock_tracker;
    }
#endif
    return NULL;
}

/* ========================================================================
 * Helper Functions
 * ======================================================================== */

/**
 * Get human-readable lock type name
 */
static const char *lock_type_name(uint32_t lock_type) {
    switch (lock_type) {
        case LOCK_TYPE_QSPIN:    return "qspinlock";
        case LOCK_TYPE_ADAPTIVE: return "adaptive_mutex";
        case LOCK_TYPE_TOKEN:    return "lwkt_token";
        case LOCK_TYPE_SLEEP:    return "sleep_lock";
        default:                 return "unknown";
    }
}

/* ========================================================================
 * DAG Violation Reporting
 * ======================================================================== */

/**
 * Report DAG violation with detailed diagnostics
 *
 * @param tracker Current thread's lock tracker
 * @param new_lock Address of lock being acquired
 * @param new_name Name of lock being acquired
 * @param new_level DAG level of lock being acquired
 * @param new_type Type of lock being acquired
 * @param file Source file of acquisition
 * @param line Source line of acquisition
 */
static __attribute__((unused)) void dag_report_violation(struct thread_lock_tracker *tracker,
                                void *new_lock, const char *new_name,
                                uint32_t new_level, uint32_t new_type,
                                const char *file, int line) {
    cprintf("\n=== DAG VIOLATION DETECTED ===\n");
    cprintf("Attempted acquisition:\n");
    cprintf("  Lock:   %s (%p)\n", new_name, new_lock);
    cprintf("  Level:  %u\n", new_level);
    cprintf("  Type:   %s\n", lock_type_name(new_type));
    cprintf("  Source: %s:%d\n", file, line);

    cprintf("\nCurrently held locks (%u):\n", tracker->depth);
    for (uint32_t i = 0; i < tracker->depth; i++) {
        struct lock_acquisition *acq = &tracker->stack[i];
        cprintf("  [%u] %s (level %u, %s) at %s:%d\n",
               i, acq->lock_name, acq->dag_level,
               lock_type_name(acq->lock_type),
               acq->file, acq->line);
    }

    cprintf("\nViolation: Level %u <= %u (must be strictly increasing)\n",
           new_level, tracker->highest_level);
    cprintf("Total violations by this thread: %u\n", tracker->violations + 1);

    tracker->violations++;

#ifdef DAG_PANIC_ON_VIOLATION
    panic("DAG violation - deadlock risk");
#endif
}

/* ========================================================================
 * DAG Validation Functions
 * ======================================================================== */

/**
 * Validate lock acquisition against DAG ordering
 *
 * Checks if acquiring a new lock would violate the DAG hierarchy.
 * Returns 1 if safe, 0 if would cause violation.
 *
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
                             const char *file, int line) {
#ifndef USE_DAG_CHECKING
    return 1;  // DAG checking disabled
#else
    struct thread_lock_tracker *tracker = get_lock_tracker();

    if (!tracker) {
        return 1;  // No tracking available (e.g., early boot)
    }

    atomic_fetch_add_explicit(&global_dag_stats.dag_checks, 1, memory_order_relaxed);

    // Check if already holding this lock (reacquisition)
    for (uint32_t i = 0; i < tracker->depth; i++) {
        if (tracker->stack[i].lock_addr == lock_addr) {
            // Reacquisition of same lock

            if (lock_type == LOCK_TYPE_TOKEN) {
                // LWKT tokens allow reacquisition (CPU-owned)
                return 1;
            }

            // Error for other lock types
            cprintf("\nERROR: Reacquisition of non-token lock detected:\n");
            cprintf("  Lock: %s (%p)\n", name, lock_addr);
            cprintf("  Type: %s\n", lock_type_name(lock_type));
            cprintf("  Location: %s:%d\n", file, line);
            cprintf("  Originally acquired at: %s:%d\n",
                   tracker->stack[i].file, tracker->stack[i].line);

#ifdef DAG_PANIC_ON_VIOLATION
            panic("Lock reacquisition");
#endif
            return 0;
        }
    }

    // Check DAG ordering: new lock must be at higher level than all held locks
    for (uint32_t i = 0; i < tracker->depth; i++) {
        if (dag_level <= tracker->stack[i].dag_level) {
            // DAG VIOLATION!
            atomic_fetch_add_explicit(&global_dag_stats.violations_detected, 1, memory_order_relaxed);

            if (dag_level < LOCK_LEVEL_MAX) {
                atomic_fetch_add_explicit(&global_dag_stats.violations_by_level[dag_level], 1, memory_order_relaxed);
            }

            dag_report_violation(tracker, lock_addr, name, dag_level,
                               lock_type, file, line);

            return 0;  // Violation detected
        }
    }

    return 1;  // Acquisition is safe
#endif
}

/**
 * Track lock acquisition in DAG
 *
 * Called after successful lock acquisition to record in thread's stack.
 *
 * @param lock_addr Address of lock acquired
 * @param name Lock name (debug)
 * @param dag_level DAG level of lock
 * @param lock_type Type of lock (LOCK_TYPE_*)
 * @param file Source file
 * @param line Source line
 */
void dag_lock_acquired(void *lock_addr, const char *name,
                      uint32_t dag_level, uint32_t lock_type,
                      const char *file, int line) {
#ifndef USE_DAG_CHECKING
    return;  // DAG checking disabled
#else
    struct thread_lock_tracker *tracker = get_lock_tracker();

    if (!tracker) {
        return;  // No tracking available
    }

    // Check for stack overflow
    if (tracker->depth >= MAX_HELD_LOCKS) {
        cprintf("dag_lock_acquired: lock stack overflow (max %d)\n", MAX_HELD_LOCKS);
        panic("dag_lock_acquired: lock stack overflow");
    }

    // Record acquisition
    struct lock_acquisition *acq = &tracker->stack[tracker->depth];
    acq->lock_addr = lock_addr;
    acq->lock_name = name;
    acq->dag_level = dag_level;
    acq->lock_type = lock_type;
    acq->acquire_tsc = rdtsc();
    acq->file = file;
    acq->line = line;

    tracker->depth++;

    // Update statistics
    if (tracker->depth > tracker->max_depth) {
        tracker->max_depth = tracker->depth;

        // Update global max chain length
        uint64_t old_max = atomic_load_explicit(&global_dag_stats.max_chain_length, memory_order_relaxed);
        while (tracker->depth > old_max) {
            uint64_t expected = old_max;
            if (atomic_compare_exchange_weak_explicit(&global_dag_stats.max_chain_length,
                                                      &expected, tracker->depth,
                                                      memory_order_relaxed, memory_order_relaxed)) {
                break;
            }
            old_max = expected;
        }
    }

    if (dag_level > tracker->highest_level) {
        tracker->highest_level = dag_level;
    }

    atomic_fetch_add_explicit(&global_dag_stats.total_acquisitions, 1, memory_order_relaxed);
#endif
}

/**
 * Track lock release in DAG
 *
 * Removes lock from thread's held stack. Handles both LIFO (proper nesting)
 * and non-LIFO release (e.g., token_release_all).
 *
 * @param lock_addr Address of lock being released
 */
void dag_lock_released(void *lock_addr) {
#ifndef USE_DAG_CHECKING
    return;  // DAG checking disabled
#else
    struct thread_lock_tracker *tracker = get_lock_tracker();

    if (!tracker || tracker->depth == 0) {
        return;  // No locks held
    }

    // Find lock in stack (should be at top for proper nesting)
    for (int i = tracker->depth - 1; i >= 0; i--) {
        if (tracker->stack[i].lock_addr == lock_addr) {
            // Found it - remove from stack

            if (i != (int)(tracker->depth - 1)) {
                // Not at top - improper nesting (warning only)
                // This is OK for LWKT tokens via token_release_all()
                cprintf("WARNING: Non-LIFO lock release: %s (depth %d, expected %d)\n",
                       tracker->stack[i].lock_name, i, tracker->depth - 1);
            }

            // Shift stack down (remove element at index i)
            for (uint32_t j = i; j < tracker->depth - 1; j++) {
                tracker->stack[j] = tracker->stack[j + 1];
            }

            tracker->depth--;

            // Recalculate highest level
            tracker->highest_level = 0;
            for (uint32_t j = 0; j < tracker->depth; j++) {
                if (tracker->stack[j].dag_level > tracker->highest_level) {
                    tracker->highest_level = tracker->stack[j].dag_level;
                }
            }

            return;
        }
    }

    // Lock not found in stack
    // This is OK - could be released via token_release_all()
    // Just ignore
#endif
}

/* ========================================================================
 * Statistics and Debugging
 * ======================================================================== */

/**
 * Dump DAG statistics
 */
void dag_dump_stats(void) {
    struct dag_stats *s = &global_dag_stats;

    cprintf("\n=== DAG Lock Ordering Statistics ===\n");
    cprintf("Total acquisitions: %lu\n", s->total_acquisitions);
    cprintf("DAG checks:         %lu\n", s->dag_checks);
    cprintf("Violations:         %lu\n", s->violations_detected);
    cprintf("Max chain length:   %lu\n", s->max_chain_length);

    if (s->violations_detected > 0) {
        cprintf("\nViolations by level:\n");
        for (int i = 0; i < LOCK_LEVEL_MAX; i++) {
            if (s->violations_by_level[i] > 0) {
                cprintf("  Level %2d: %lu\n", i, s->violations_by_level[i]);
            }
        }
    }
}

/**
 * Reset DAG statistics
 */
void dag_reset_stats(void) {
    memset(&global_dag_stats, 0, sizeof(global_dag_stats));
}

/**
 * Initialize DAG subsystem
 *
 * Called once at boot
 */
void dag_init(void) {
    dag_reset_stats();

#ifdef USE_DAG_CHECKING
    cprintf("DAG lock ordering: ENABLED\n");
#ifdef DAG_PANIC_ON_VIOLATION
    cprintf("  Panic on violation: YES\n");
#else
    cprintf("  Panic on violation: NO (warning only)\n");
#endif
#else
    cprintf("DAG lock ordering: DISABLED\n");
#endif
}
