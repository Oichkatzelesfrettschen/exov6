/*
 * Modern Locking Mechanisms Implementation
 * Pure C17 with GCC built-ins for atomics
 */

#include <types.h>
#include "defs.h"
#include "param.h"
#include "arch.h"
#include "proc.h"
#include "spinlock.h"
#include "modern_locks.h"

// Forward declare CPU functions
extern void cpu_pause(void);
extern void pause(void);

/*
 * MCS Lock Implementation
 * Each CPU spins on its own cache line for optimal performance
 */

void mcs_init(struct mcs_lock *lock, const char *name) {
    lock->tail = NULL;
    lock->name = name;
}

void mcs_acquire(struct mcs_lock *lock, struct mcs_node *node) {
    struct mcs_node *prev;
    
    // Initialize our node
    node->next = NULL;
    node->locked = 1;
    
    // Add ourselves to the queue and get previous tail
    prev = (struct mcs_node *)(uintptr_t)atomic_xchg((volatile uintptr_t *)&lock->tail, 
                                                     (uintptr_t)node);
    
    if (prev != NULL) {
        // Queue was not empty, link ourselves and wait
        smp_wmb();  // Ensure our node is initialized before linking
        prev->next = node;
        
        // Spin on our local locked flag
        while (atomic_load(&node->locked)) {
            cpu_pause();  // CPU hint for spinning
        }
    }
    
    // We have the lock
    smp_mb();  // Full barrier before entering critical section
}

void mcs_release(struct mcs_lock *lock, struct mcs_node *node) {
    struct mcs_node *next = (struct mcs_node *)node->next;
    
    if (next == NULL) {
        // No known successor, try to remove ourselves from tail
        if (atomic_cas((volatile uintptr_t *)&lock->tail, 
                       (uintptr_t)node, (uintptr_t)NULL)) {
            // Successfully removed, lock is free
            return;
        }
        
        // Someone is adding themselves, wait for link
        while ((next = (struct mcs_node *)node->next) == NULL) {
            cpu_pause();
        }
    }
    
    // Pass lock to next waiter
    smp_wmb();  // Ensure critical section writes complete
    next->locked = 0;
}

int mcs_tryacquire(struct mcs_lock *lock, struct mcs_node *node) {
    node->next = NULL;
    node->locked = 0;
    
    // Try to claim empty queue
    if (atomic_cas((volatile uintptr_t *)&lock->tail, 
                   (uintptr_t)NULL, (uintptr_t)node)) {
        smp_mb();
        return 1;  // Success
    }
    
    return 0;  // Lock is held
}

/*
 * Read-Write Lock Implementation
 * Allows multiple readers or single writer
 */

void rwlock_init(struct rwlock *lock, const char *name) {
    lock->lock = 0;
    lock->writers_waiting = 0;
    lock->name = name;
}

void rwlock_acquire_read(struct rwlock *lock) {
    while (1) {
        // Wait for writer to finish
        while (atomic_load(&lock->lock) < 0 || 
               atomic_load(&lock->writers_waiting) > 0) {
            cpu_pause();
        }
        
        // Try to increment reader count
        int32_t old = atomic_load(&lock->lock);
        if (old >= 0 && atomic_cas(&lock->lock, old, old + 1)) {
            break;  // Successfully acquired read lock
        }
    }
    
    smp_rmb();  // Read barrier before accessing protected data
}

void rwlock_release_read(struct rwlock *lock) {
    smp_rmb();  // Ensure reads complete before release
    atomic_sub(&lock->lock, 1);
}

void rwlock_acquire_write(struct rwlock *lock) {
    // Announce writer waiting
    atomic_add(&lock->writers_waiting, 1);
    
    // Wait for exclusive access
    while (!atomic_cas(&lock->lock, 0, -1)) {
        pause();
    }
    
    // Decrement waiting count
    atomic_sub(&lock->writers_waiting, 1);
    
    smp_wmb();  // Write barrier before modifying protected data
}

void rwlock_release_write(struct rwlock *lock) {
    smp_wmb();  // Ensure writes complete before release
    atomic_store(&lock->lock, 0);
}

int rwlock_try_read(struct rwlock *lock) {
    int32_t old = atomic_load(&lock->lock);
    
    // Can acquire if no writer and no writers waiting
    if (old >= 0 && atomic_load(&lock->writers_waiting) == 0) {
        if (atomic_cas(&lock->lock, old, old + 1)) {
            smp_rmb();
            return 1;  // Success
        }
    }
    
    return 0;  // Failed
}

int rwlock_try_write(struct rwlock *lock) {
    if (atomic_cas(&lock->lock, 0, -1)) {
        smp_wmb();
        return 1;  // Success
    }
    
    return 0;  // Failed
}

/*
 * Sequence Lock Implementation
 * Writers update sequence counter, readers retry if sequence changes
 */

void seqlock_init(struct seqlock *lock, const char *name) {
    lock->sequence = 0;
    initlock(&lock->lock, name);
    lock->name = name;
}

uint32_t seqlock_read_begin(struct seqlock *lock) {
    uint32_t seq;
    
    do {
        seq = atomic_load(&lock->sequence);
        // Wait if writer is active (odd sequence number)
        if (seq & 1) {
            while (atomic_load(&lock->sequence) & 1) {
                cpu_pause();
            }
            continue;
        }
        
        smp_rmb();  // Read barrier before reading protected data
        return seq;
    } while (1);
}

int seqlock_read_retry(struct seqlock *lock, uint32_t seq) {
    smp_rmb();  // Ensure reads complete before checking sequence
    
    // Retry if sequence changed or writer is active
    return (seq != atomic_load(&lock->sequence)) || (seq & 1);
}

void seqlock_write_begin(struct seqlock *lock) {
    acquire(&lock->lock);  // Exclude other writers
    
    // Increment sequence to odd (writer active)
    atomic_add(&lock->sequence, 1);
    
    smp_wmb();  // Write barrier before modifying protected data
}

void seqlock_write_end(struct seqlock *lock) {
    smp_wmb();  // Ensure writes complete
    
    // Increment sequence to even (writer done)
    atomic_add(&lock->sequence, 1);
    
    release(&lock->lock);
}

/*
 * Hybrid Lock Implementation
 * Spins briefly then blocks to save CPU
 */

#define HYBRID_SPIN_COUNT 100

void hybrid_init(struct hybrid_lock *lock, const char *name) {
    lock->locked = 0;
    lock->waiters = 0;
    lock->name = name;
    lock->owner = NULL;
}

void hybrid_acquire(struct hybrid_lock *lock) {
    int spin_count = HYBRID_SPIN_COUNT;
    
    // Try spinning first
    while (spin_count-- > 0) {
        if (atomic_cas(&lock->locked, 0, 1)) {
            lock->owner = mycpu();
            smp_mb();
            return;  // Got the lock
        }
        pause();
    }
    
    // Add ourselves as a waiter
    atomic_add(&lock->waiters, 1);
    
    // Now block until lock is available
    while (!atomic_cas(&lock->locked, 0, 1)) {
        // In a real implementation, we would sleep here
        // For now, continue spinning with backoff
        for (int i = 0; i < 1000; i++) {
            cpu_pause();
        }
    }
    
    // Got the lock, remove from waiters
    atomic_sub(&lock->waiters, 1);
    lock->owner = mycpu();
    smp_mb();
}

void hybrid_release(struct hybrid_lock *lock) {
    lock->owner = NULL;
    smp_mb();  // Ensure critical section completes
    
    atomic_store(&lock->locked, 0);
    
    // Wake waiters if any (would use actual wakeup in real implementation)
    if (atomic_load(&lock->waiters) > 0) {
        // Wakeup mechanism would go here
    }
}

int hybrid_tryacquire(struct hybrid_lock *lock) {
    if (atomic_cas(&lock->locked, 0, 1)) {
        lock->owner = mycpu();
        smp_mb();
        return 1;  // Success
    }
    
    return 0;  // Failed
}