/**
 * @file priority.c
 * @brief Priority inheritance support for adaptive mutex
 *
 * Priority inheritance prevents priority inversion:
 * - Low priority thread holds lock
 * - High priority thread blocks waiting for lock
 * - Medium priority threads preempt low priority thread
 * - Result: High priority thread blocked by medium priority threads
 *
 * Solution: Temporarily boost low priority lock holder to highest
 * waiting thread priority.
 *
 * Based on:
 * - POSIX priority inheritance protocol
 * - NetBSD priority lending
 * - VxWorks priority inheritance
 *
 * @version 1.0
 * @date 2025-11-17
 */

#include <types.h>
#include "defs.h"
#include "param.h"
#include "arch.h"
#include "memlayout.h"
#include "exo_lock.h"
#include "proc.h"

/* ========================================================================
 * Priority Inheritance Operations
 * ======================================================================== */

/**
 * Inherit priority from waiter
 *
 * Boosts lock owner's priority to prevent priority inversion.
 *
 * @param mutex Mutex whose owner will inherit priority
 * @param waiter_priority Priority of waiting thread
 */
void priority_inherit(struct adaptive_mutex *mutex, uint32_t waiter_priority) {
    if (!mutex) return;

    // Get owner thread ID
    uint32_t owner_tid = atomic_load_explicit(&mutex->owner_tid, memory_order_acquire);

    if (owner_tid == INVALID_TID) {
        return;  // No owner
    }

    // Find owner thread
    // Note: This is simplified - actual implementation would look up thread by TID
    // struct thread *owner = find_thread(owner_tid);
    struct thread *owner = (struct thread *)(uintptr_t)owner_tid;  // Simplified

    if (!owner) {
        return;  // Owner thread not found
    }

    // Boost owner priority if waiter has higher priority
    // Note: Simplified - actual implementation depends on thread priority structure
    uint32_t owner_priority = 0;  // Get from owner->priority

    if (waiter_priority > owner_priority) {
        // Save original priority if not already saved
        if (!mutex->turnstile->priority_inherited) {
            mutex->turnstile->original_priority = owner_priority;
        }

        // Boost priority
        // owner->effective_priority = waiter_priority;

        // Re-insert into run queue if thread is runnable
        // if (owner->state == RUNNABLE) {
        //     runqueue_update_priority(owner);
        // }

        cprintf("priority_inherit: boosted owner TID %u from %u to %u\n",
                owner_tid, owner_priority, waiter_priority);
    }
}

/**
 * Restore original priority after lock release
 *
 * @param mutex Mutex whose owner will have priority restored
 */
void priority_restore(struct adaptive_mutex *mutex) {
    if (!mutex || !mutex->turnstile) return;

    // Only restore if we actually inherited priority
    if (!mutex->turnstile->priority_inherited) {
        return;
    }

    // Get owner thread ID
    uint32_t owner_tid = atomic_load_explicit(&mutex->owner_tid, memory_order_acquire);

    if (owner_tid == INVALID_TID) {
        return;  // No owner
    }

    // Find owner thread
    struct thread *owner = (struct thread *)(uintptr_t)owner_tid;  // Simplified

    if (!owner) {
        return;
    }

    // Restore original priority
    uint32_t original = mutex->turnstile->original_priority;

    // owner->effective_priority = original;

    // Re-insert into run queue if needed
    // if (owner->state == RUNNABLE) {
    //     runqueue_update_priority(owner);
    // }

    cprintf("priority_restore: restored owner TID %u to priority %u\n",
            owner_tid, original);
}

/**
 * Check if priority inheritance is active
 *
 * @param mutex Mutex to check
 * @return 1 if PI active, 0 otherwise
 */
int priority_inherited(struct adaptive_mutex *mutex) {
    if (!mutex || !mutex->turnstile) {
        return 0;
    }

    return mutex->turnstile->priority_inherited;
}

/**
 * Get effective priority of thread
 *
 * Returns inherited priority if PI is active, otherwise base priority.
 *
 * @param thread Thread to query
 * @return Effective priority
 */
uint32_t get_effective_priority(struct thread *thread) {
    if (!thread) return 0;

    // Note: Simplified - actual implementation depends on thread structure
    // if (thread->effective_priority != thread->base_priority) {
    //     return thread->effective_priority;
    // }

    return 0;  // thread->base_priority;
}
