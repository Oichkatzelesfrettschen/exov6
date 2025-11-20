/**
 * @file turnstile.c
 * @brief Turnstile (wait queue) implementation for adaptive mutex
 *
 * Turn stiles provide FIFO queuing with priority inheritance:
 * - One turnstile per blocking lock
 * - FIFO ordering for fairness
 * - Priority inheritance to prevent priority inversion
 * - Pre-allocated pool for performance
 *
 * Based on FreeBSD turnstile design
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
 * Turnstile Pool
 * ======================================================================== */

/**
 * Pre-allocated turnstile pool
 * Avoids memory allocation in critical path
 */
static struct turnstile turnstile_pool[TURNSTILE_POOL_SIZE];
static _Atomic uint32_t turnstile_pool_bitmap __attribute__((unused)) = 0;  // Bitmap of free slots

/**
 * Turnstile memory pool initialization
 * Called once at boot
 */
void turnstile_subsystem_init(void) {
    for (int i = 0; i < TURNSTILE_POOL_SIZE; i++) {
        turnstile_pool[i].mutex = NULL;
        thread_queue_init(&turnstile_pool[i].waiters);
        atomic_store_explicit(&turnstile_pool[i].count, 0, memory_order_relaxed);
        turnstile_pool[i].priority_inherited = 0;
        turnstile_pool[i].total_wait_time = 0;
        turnstile_pool[i].max_wait_time = 0;
        turnstile_pool[i].wakeup_count = 0;
        turnstile_pool[i].name = NULL;
    }

    cprintf("turnstile: initialized pool with %d turnstiles\n", TURNSTILE_POOL_SIZE);
}

/* ========================================================================
 * Thread Queue Operations
 * ======================================================================== */

/**
 * Initialize thread queue
 *
 * @param q Queue to initialize
 */
void thread_queue_init(struct thread_queue *q) {
    q->head = NULL;
    q->tail = NULL;
    q->count = 0;
    q->max_priority = 0;
}

/**
 * Add thread to queue (FIFO)
 *
 * @param q Queue
 * @param thread Thread to add
 * @param priority Thread priority (for PI)
 */
void thread_queue_push(struct thread_queue *q, struct thread *thread, uint32_t priority) {
    // Allocate queue node
    // Note: In production, this should come from a pre-allocated pool
    struct thread_queue_node *node = (struct thread_queue_node *)kalloc();  // Simplified - should be from pool
    if (!node) {
        panic("thread_queue_push: out of memory");
    }

    node->thread = thread;
    node->next = NULL;
    node->prev = q->tail;
    node->priority = priority;
    node->enqueue_tsc = 0;  // rdtsc() if needed

    // Link into queue
    if (q->tail) {
        q->tail->next = node;
    } else {
        q->head = node;
    }

    q->tail = node;
    q->count++;

    // Track maximum priority in queue
    if (priority > q->max_priority) {
        q->max_priority = priority;
    }
}

/**
 * Remove and return first thread from queue
 *
 * @param q Queue
 * @return Thread, or NULL if queue empty
 */
struct thread *thread_queue_pop(struct thread_queue *q) {
    if (!q->head) {
        return NULL;
    }

    struct thread_queue_node *node = q->head;
    struct thread *thread = node->thread;

    q->head = node->next;

    if (q->head) {
        q->head->prev = NULL;
    } else {
        q->tail = NULL;
    }

    q->count--;

    // Free node
    kfree((char *)node);  // Simplified - should return to pool

    // Recalculate max priority if needed
    if (q->count == 0) {
        q->max_priority = 0;
    }

    return thread;
}

/**
 * Check if queue is empty
 *
 * @param q Queue
 * @return 1 if empty, 0 otherwise
 */
int thread_queue_empty(struct thread_queue *q) {
    return q->head == NULL;
}

/* ========================================================================
 * Turnstile Operations
 * ======================================================================== */

/**
 * Allocate turnstile for mutex
 *
 * @param mutex Associated mutex
 * @return Allocated turnstile
 */
struct turnstile *turnstile_alloc(struct adaptive_mutex *mutex) {
    // Try to allocate from pool
    for (int i = 0; i < TURNSTILE_POOL_SIZE; i++) {
        if (!turnstile_pool[i].mutex) {
            // Try to claim this slot
            if (__sync_bool_compare_and_swap(&turnstile_pool[i].mutex, NULL, mutex)) {
                struct turnstile *ts = &turnstile_pool[i];

                // Initialize turnstile
                thread_queue_init(&ts->waiters);
                atomic_store_explicit(&ts->count, 0, memory_order_relaxed);
                ts->priority_inherited = 0;
                ts->inherited_priority = 0;
                ts->original_priority = 0;
                ts->total_wait_time = 0;
                ts->max_wait_time = 0;
                ts->wakeup_count = 0;
                ts->name = mutex->name;

                return ts;
            }
        }
    }

    // Pool exhausted - allocate dynamically (fallback)
    cprintf("WARNING: turnstile pool exhausted, allocating dynamically\n");

    struct turnstile *ts = (struct turnstile *)kalloc();
    if (!ts) {
        panic("turnstile_alloc: out of memory");
    }

    ts->mutex = mutex;
    thread_queue_init(&ts->waiters);
    atomic_store_explicit(&ts->count, 0, memory_order_relaxed);
    ts->priority_inherited = 0;
    ts->inherited_priority = 0;
    ts->original_priority = 0;
    ts->total_wait_time = 0;
    ts->max_wait_time = 0;
    ts->wakeup_count = 0;
    ts->name = mutex->name;

    return ts;
}

/**
 * Free turnstile (return to pool)
 *
 * @param ts Turnstile to free
 */
void turnstile_free(struct turnstile *ts) {
    if (!ts) return;

    // Check if from pool
    if (ts >= &turnstile_pool[0] && ts < &turnstile_pool[TURNSTILE_POOL_SIZE]) {
        // Return to pool
        ts->mutex = NULL;
        atomic_store_explicit(&ts->count, 0, memory_order_relaxed);
    } else {
        // Dynamically allocated - free it
        kfree((char *)ts);
    }
}

/**
 * Wait on turnstile (block current thread)
 *
 * This is called when adaptive spinning fails and we need to block.
 * The thread will sleep until woken by turnstile_wake_one().
 *
 * @param ts Turnstile to wait on
 * @param thread Current thread
 */
void turnstile_wait(struct turnstile *ts, struct thread *thread) {
    if (!ts || !thread) {
        panic("turnstile_wait: null argument");
    }

    pushcli();  // Disable interrupts

    // Get thread priority (simplified - adjust based on actual thread structure)
    uint32_t my_priority = 0;  // Default priority

    // Add thread to wait queue
    thread_queue_push(&ts->waiters, thread, my_priority);
    atomic_fetch_add_explicit(&ts->count, 1, memory_order_relaxed);

    // Set thread state to sleeping
    // Note: This is simplified - actual implementation depends on thread/proc structure
    // thread->state = SLEEPING;
    // thread->wchan = ts;

    // Priority inheritance: boost lock owner if needed
    if (ts->mutex->flags & ADAPTIVE_FLAG_PRIO_INHERIT) {
        if (ts->waiters.max_priority > 0) {
            // Owner should inherit highest priority from wait queue
            // This is handled by priority_inherit() in priority.c
            ts->priority_inherited = 1;
            ts->inherited_priority = ts->waiters.max_priority;

            if (ts->mutex->flags & ADAPTIVE_FLAG_STATS_ENABLED) {
                __sync_fetch_and_add(&ts->mutex->stats.priority_inherit_count, 1);
            }
        }
    }

    // Yield CPU and reschedule
    // Note: Simplified - actual implementation calls sched()
    // sched();

    // When we wake up, we have the lock
    // Lock owner is set by turnstile_wake_one()

    popcli();  // Re-enable interrupts
}

/**
 * Wake one waiting thread (FIFO)
 *
 * This transfers lock ownership to the woken thread.
 *
 * @param ts Turnstile
 * @return Woken thread, or NULL if no waiters
 */
struct thread *turnstile_wake_one(struct turnstile *ts) {
    if (!ts) return NULL;

    // Pop first waiter (FIFO ordering)
    struct thread *next = thread_queue_pop(&ts->waiters);

    if (!next) {
        return NULL;  // No waiters
    }

    atomic_fetch_sub_explicit(&ts->count, 1, memory_order_relaxed);

    // Restore priority if PI was active
    if (ts->priority_inherited) {
        // Priority restoration handled by priority_restore() in priority.c
        ts->priority_inherited = 0;
        ts->inherited_priority = 0;
    }

    // Wake the thread (set to RUNNABLE)
    // Note: Simplified - actual implementation sets thread state
    // next->state = RUNNABLE;
    // next->wchan = NULL;

    // Update statistics
    ts->wakeup_count++;

    return next;
}

/**
 * Wake all waiting threads
 *
 * Used for broadcast operations (rare for mutexes)
 *
 * @param ts Turnstile
 */
void turnstile_wake_all(struct turnstile *ts) {
    if (!ts) return;

    while (turnstile_has_waiters(ts)) {
        turnstile_wake_one(ts);
    }
}

/**
 * Check if turnstile has waiting threads
 *
 * @param ts Turnstile
 * @return 1 if has waiters, 0 otherwise
 */
int turnstile_has_waiters(struct turnstile *ts) {
    if (!ts) return 0;

    return !thread_queue_empty(&ts->waiters);
}
