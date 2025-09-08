/**
 * @file unified_lock.c
 * @brief Unified Modern Lock Implementation for ExoV6
 * 
 * Consolidates 5+ redundant spinlock implementations into a single,
 * high-performance, capability-aware synchronization framework.
 * 
 * This implementation replaces:
 * - kernel/sync/spinlock.c (legacy ticket lock)
 * - kernel/sync/spinlock_c17.c (C17 variant)
 * - kernel/sync/legacy/qspinlock.c (randomized variant)
 * - kernel/sync/legacy/rspinlock.c (recursive variant)  
 * - kernel/sync/legacy/quaternion_spinlock.c (experimental)
 */

#include "unified_lock.h"
#include "defs.h"
#include "proc.h"
#include "arch.h"
#include <string.h>

/* ============================================================================
 * Internal Helpers
 * ============================================================================ */

/**
 * Get current CPU ID (architecture-agnostic via HAL)
 */
static inline int get_current_cpu(void) {
    struct cpu *c = mycpu();
    return c ? c->apicid : -1;
}

/**
 * Get current timestamp in nanoseconds
 */
static inline uint64_t get_timestamp_ns(void) {
    /* TODO: Use HAL timer interface when available */
    return ticks * 10000000ULL; /* Approximate: ticks to ns */
}

/**
 * Check if current thread has required capability
 */
static inline bool has_capability(cap_id_t required) {
    if (required == 0) return true; /* No capability required */
    
    struct proc *p = myproc();
    if (!p) return true; /* Kernel context always has access */
    
    /* TODO: Implement capability checking */
    return true;
}

/* ============================================================================
 * Unified Ticket Spinlock Implementation
 * ============================================================================ */

/**
 * Initialize a spinlock
 */
void exo_spinlock_init(exo_spinlock_t *lock, const char *name) {
    lock->ticket_head = 0;
    lock->ticket_tail = 0;
    lock->owner_cpu = -1;
    lock->acquisitions = 0;
    
    lock->required_cap = 0;
    lock->backoff_base = 10;
    lock->backoff_max = 1024;
    lock->name = name;
    
    /* Initialize statistics */
    memset(&lock->stats, 0, sizeof(lock->stats));
}

/**
 * Acquire spinlock with exponential backoff
 */
void exo_spinlock_acquire(exo_spinlock_t *lock) {
    /* Check capability */
    if (!has_capability(lock->required_cap)) {
        panic("spinlock: capability check failed");
    }
    
    /* Get ticket */
    uint32_t my_ticket = atomic_fetch_add_explicit(&lock->ticket_tail, 1, 
                                                   memory_order_acq_rel);
    
    /* Update statistics - use proper atomic operations */
    atomic_fetch_add_explicit(&lock->stats.acquisitions, 1, 
                             memory_order_relaxed);
    
    /* Check for contention */
    uint32_t head = atomic_load(&lock->ticket_head);
    if (my_ticket != head) {
        atomic_fetch_add((_Atomic uint64_t *)&lock->stats.contentions, 1);
        atomic_fetch_add((_Atomic uint32_t *)&lock->stats.current_waiters, 1);
        
        /* Update max waiters if needed */
        uint32_t waiters = atomic_load(&lock->stats.current_waiters);
        uint32_t max_waiters = atomic_load(&lock->stats.max_waiters);
        while (waiters > max_waiters) {
            atomic_compare_exchange_weak(&lock->stats.max_waiters, 
                                        &max_waiters, waiters);
            max_waiters = atomic_load(&lock->stats.max_waiters);
        }
    }
    
    /* Spin with exponential backoff */
    uint32_t backoff = lock->backoff_base;
    uint64_t start_time = get_timestamp_ns();
    
    while (atomic_load_explicit(&lock->ticket_head, memory_order_acquire) != my_ticket) {
        exponential_backoff(&backoff, lock->backoff_max);
        
        /* Adaptive behavior: consider switching to MCS if high contention */
        uint32_t waiters = atomic_load(&lock->stats.current_waiters);
        if (waiters > 16) {
            /* TODO: Trigger adaptive lock upgrade */
        }
    }
    
    /* Lock acquired */
    if (my_ticket != head) {
        atomic_fetch_sub((_Atomic uint32_t *)&lock->stats.current_waiters, 1);
    }
    
    /* Record ownership */
    atomic_store(&lock->owner_cpu, get_current_cpu());
    
    /* Memory barrier to ensure all previous stores are visible */
    atomic_thread_fence(memory_order_seq_cst);
}

/**
 * Try to acquire spinlock without blocking
 */
bool exo_spinlock_try_acquire(exo_spinlock_t *lock) {
    /* Check capability */
    if (!has_capability(lock->required_cap)) {
        return false;
    }
    
    uint32_t head = atomic_load(&lock->ticket_head);
    uint32_t tail = atomic_load(&lock->ticket_tail);
    
    /* Lock is free if head == tail */
    if (head != tail) {
        return false;
    }
    
    /* Try to get the next ticket */
    if (!atomic_compare_exchange_strong(&lock->ticket_tail, &tail, tail + 1)) {
        return false;
    }
    
    /* Wait for our turn (should be immediate) */
    while (atomic_load_explicit(&lock->ticket_head, 
                                memory_order_acquire) != tail) {
        cpu_pause();
    }
    
    /* Record ownership */
    atomic_store(&lock->owner_cpu, get_current_cpu());
    atomic_fetch_add((_Atomic uint64_t *)&lock->stats.acquisitions, 1);
    
    return true;
}

/**
 * Release spinlock
 */
void exo_spinlock_release(exo_spinlock_t *lock) {
    /* Verify we own the lock */
    int cpu = get_current_cpu();
    int owner = atomic_load(&lock->owner_cpu);
    if (owner != cpu) {
        panic("spinlock: releasing lock not held by current CPU");
    }
    
    /* Clear ownership */
    atomic_store(&lock->owner_cpu, -1);
    
    /* Release the lock by incrementing head */
    atomic_fetch_add_explicit(&lock->ticket_head, 1, memory_order_release);
}

/**
 * Check if spinlock is held by current CPU
 */
bool exo_spinlock_is_held(const exo_spinlock_t *lock) {
    return atomic_load(&lock->owner_cpu) == get_current_cpu();
}

/* ============================================================================
 * MCS Lock Implementation
 * ============================================================================ */

/**
 * Initialize MCS lock
 */
void mcs_lock_init(mcs_lock_t *lock, const char *name) {
    atomic_store(&lock->tail, NULL);
    lock->required_cap = 0;
    memset(&lock->stats, 0, sizeof(lock->stats));
    lock->name = name;
}

/**
 * Acquire MCS lock
 */
void mcs_lock_acquire(mcs_lock_t *lock, mcs_node_t *node) {
    /* Check capability */
    if (!has_capability(lock->required_cap)) {
        panic("mcs_lock: capability check failed");
    }
    
    /* Initialize our node */
    atomic_store(&node->locked, true);
    atomic_store(&node->next, NULL);
    
    /* Add ourselves to the queue */
    mcs_node_t *prev = atomic_exchange(&lock->tail, node);
    
    /* If there was a predecessor, wait for them to unlock us */
    if (prev != NULL) {
        atomic_store(&prev->next, node);
        atomic_fetch_add((_Atomic uint64_t *)&lock->stats.contentions, 1);
        
        /* Spin on our own cache line */
        while (atomic_load(&node->locked)) {
            cpu_pause();
        }
    }
    
    atomic_fetch_add((_Atomic uint64_t *)&lock->stats.acquisitions, 1);
}

/**
 * Release MCS lock
 */
void mcs_lock_release(mcs_lock_t *lock, mcs_node_t *node) {
    /* Check if we have a successor */
    if (atomic_load(&node->next) == NULL) {
        /* Try to remove ourselves from the tail */
        mcs_node_t *expected = node;
        if (atomic_compare_exchange_strong(&lock->tail, &expected, NULL)) {
            /* No successor, lock is free */
            return;
        }
        
        /* Someone is adding themselves, wait for them */
        while (atomic_load(&node->next) == NULL) {
            cpu_pause();
        }
    }
    
    /* Unlock our successor */
    atomic_store(&atomic_load(&node->next)->locked, false);
}

/* ============================================================================
 * Reader-Writer Lock Implementation
 * ============================================================================ */

/**
 * Initialize reader-writer lock
 */
void rwlock_init(rwlock_t *lock, const char *name) {
    atomic_store(&lock->readers, 0);
    atomic_store(&lock->writer, false);
    atomic_store(&lock->write_waiters, 0);
    lock->required_cap = 0;
    
    exo_spinlock_init(&lock->guard, "rwlock_guard");
    memset(&lock->stats, 0, sizeof(lock->stats));
    lock->name = name;
}

/**
 * Acquire read lock
 */
void rwlock_read_acquire(rwlock_t *lock) {
    if (!has_capability(lock->required_cap)) {
        panic("rwlock: capability check failed");
    }
    
    exo_spinlock_acquire(&lock->guard);
    
    /* Wait for writer to finish */
    while (atomic_load(&lock->writer) || atomic_load(&lock->write_waiters) > 0) {
        exo_spinlock_release(&lock->guard);
        cpu_pause();
        exo_spinlock_acquire(&lock->guard);
    }
    
    atomic_fetch_add(&lock->readers, 1);
    atomic_fetch_add((_Atomic uint64_t *)&lock->stats.acquisitions, 1);
    
    exo_spinlock_release(&lock->guard);
}

/**
 * Release read lock
 */
void rwlock_read_release(rwlock_t *lock) {
    atomic_fetch_sub(&lock->readers, 1);
}

/**
 * Acquire write lock
 */
void rwlock_write_acquire(rwlock_t *lock) {
    if (!has_capability(lock->required_cap)) {
        panic("rwlock: capability check failed");
    }
    
    exo_spinlock_acquire(&lock->guard);
    
    atomic_fetch_add(&lock->write_waiters, 1);
    
    /* Wait for all readers and current writer */
    while (atomic_load(&lock->readers) > 0 || atomic_load(&lock->writer)) {
        exo_spinlock_release(&lock->guard);
        cpu_pause();
        exo_spinlock_acquire(&lock->guard);
    }
    
    atomic_store(&lock->writer, true);
    atomic_fetch_sub(&lock->write_waiters, 1);
    atomic_fetch_add((_Atomic uint64_t *)&lock->stats.acquisitions, 1);
    
    exo_spinlock_release(&lock->guard);
}

/**
 * Release write lock
 */
void rwlock_write_release(rwlock_t *lock) {
    atomic_store(&lock->writer, false);
}

/* ============================================================================
 * Sequence Lock Implementation
 * ============================================================================ */

/**
 * Initialize sequence lock
 */
void seqlock_init(seqlock_t *lock, const char *name) {
    atomic_store(&lock->sequence, 0);
    exo_spinlock_init(&lock->write_lock, "seqlock_write");
    memset(&lock->stats, 0, sizeof(lock->stats));
    lock->name = name;
}

/**
 * Begin sequence lock read
 */
uint64_t seqlock_read_begin(const seqlock_t *lock) {
    uint64_t seq;
    do {
        seq = atomic_load(&lock->sequence);
    } while (seq & 1); /* Wait if write in progress */
    
    atomic_thread_fence(memory_order_acquire);
    return seq;
}

/**
 * Check if sequence lock read should retry
 */
bool seqlock_read_retry(const seqlock_t *lock, uint64_t seq) {
    atomic_thread_fence(memory_order_acquire);
    return atomic_load(&lock->sequence) != seq;
}

/**
 * Begin sequence lock write
 */
void seqlock_write_begin(seqlock_t *lock) {
    exo_spinlock_acquire(&lock->write_lock);
    atomic_fetch_add(&lock->sequence, 1); /* Make odd to indicate write */
    atomic_thread_fence(memory_order_release);
}

/**
 * End sequence lock write
 */
void seqlock_write_end(seqlock_t *lock) {
    atomic_thread_fence(memory_order_release);
    atomic_fetch_add(&lock->sequence, 1); /* Make even to indicate done */
    exo_spinlock_release(&lock->write_lock);
}

/* ============================================================================
 * Sleeplock Implementation (Complete)
 * ============================================================================ */

/**
 * Initialize sleeplock
 */
void sleeplock_init(sleeplock_t *lock, const char *name) {
    exo_spinlock_init(&lock->guard, "sleeplock_guard");
    atomic_store(&lock->locked, false);
    atomic_store(&lock->owner_pid, -1);
    lock->wait_head = NULL;
    lock->wait_tail = NULL;
    lock->required_cap = 0;
    memset(&lock->stats, 0, sizeof(lock->stats));
    lock->name = name;
}

/**
 * Acquire sleeplock - blocks if necessary
 */
void sleeplock_acquire(sleeplock_t *lock) {
    struct proc *p = myproc();
    if (!p) panic("sleeplock: no process context");
    
    /* Check capability */
    if (!has_capability(lock->required_cap)) {
        panic("sleeplock: capability check failed");
    }
    
    exo_spinlock_acquire(&lock->guard);
    
    /* Already own it? */
    if (atomic_load(&lock->owner_pid) == p->pid) {
        panic("sleeplock: already holding");
    }
    
    /* Wait while locked */
    while (atomic_load(&lock->locked)) {
        /* Add to wait queue */
        p->next_wait = NULL;
        if (lock->wait_tail) {
            lock->wait_tail->next_wait = p;
        } else {
            lock->wait_head = p;
        }
        lock->wait_tail = p;
        
        /* Sleep on this lock */
        sleep(lock, &lock->guard);
        
        /* Woken up - remove from queue if still there */
        struct proc **pp = &lock->wait_head;
        while (*pp) {
            if (*pp == p) {
                *pp = p->next_wait;
                if (lock->wait_tail == p) {
                    lock->wait_tail = NULL;
                }
                break;
            }
            pp = &(*pp)->next_wait;
        }
    }
    
    /* Lock is free - take it */
    atomic_store(&lock->locked, true);
    atomic_store(&lock->owner_pid, p->pid);
    atomic_fetch_add((_Atomic uint64_t *)&lock->stats.acquisitions, 1);
    
    exo_spinlock_release(&lock->guard);
}

/**
 * Release sleeplock
 */
void sleeplock_release(sleeplock_t *lock) {
    struct proc *p = myproc();
    if (!p) panic("sleeplock: no process context");
    
    exo_spinlock_acquire(&lock->guard);
    
    /* Verify we own it */
    if (atomic_load(&lock->owner_pid) != p->pid) {
        panic("sleeplock: not holding");
    }
    
    /* Release ownership */
    atomic_store(&lock->locked, false);
    atomic_store(&lock->owner_pid, -1);
    
    /* Wake one waiter */
    if (lock->wait_head) {
        wakeup(lock);
    }
    
    exo_spinlock_release(&lock->guard);
}

/**
 * Check if current process holds sleeplock
 */
bool sleeplock_holding(const sleeplock_t *lock) {
    struct proc *p = myproc();
    if (!p) return false;
    return atomic_load(&lock->owner_pid) == p->pid;
}

/* ============================================================================
 * RCU Implementation (Complete)
 * ============================================================================ */

/**
 * Initialize RCU state
 */
void rcu_init(rcu_state_t *rcu, const char *name) {
    atomic_store(&rcu->global_counter, 0);
    
    for (int i = 0; i < NCPU; i++) {
        atomic_store(&rcu->reader_count[i], 0);
    }
    
    exo_spinlock_init(&rcu->writer_lock, "rcu_writer");
    memset(&rcu->stats, 0, sizeof(rcu->stats));
    rcu->name = name;
}

/**
 * Enter RCU read-side critical section
 */
void rcu_read_lock(rcu_state_t *rcu) {
    int cpu = get_current_cpu();
    if (cpu < 0 || cpu >= NCPU) return;
    
    /* Increment per-CPU reader count */
    atomic_fetch_add(&rcu->reader_count[cpu], 1);
    
    /* Memory barrier to ensure reads happen after lock */
    atomic_thread_fence(memory_order_acquire);
    
    atomic_fetch_add(&rcu->stats.acquisitions, 1);
}

/**
 * Exit RCU read-side critical section
 */
void rcu_read_unlock(rcu_state_t *rcu) {
    int cpu = get_current_cpu();
    if (cpu < 0 || cpu >= NCPU) return;
    
    /* Memory barrier to ensure reads complete before unlock */
    atomic_thread_fence(memory_order_release);
    
    /* Decrement per-CPU reader count */
    atomic_fetch_sub(&rcu->reader_count[cpu], 1);
}

/**
 * Wait for all RCU readers to complete (grace period)
 */
void rcu_synchronize(rcu_state_t *rcu) {
    /* Acquire writer lock to serialize synchronize operations */
    exo_spinlock_acquire(&rcu->writer_lock);
    
    /* Increment global counter to mark new grace period */
    atomic_fetch_add(&rcu->global_counter, 1);
    
    /* Wait for all readers to drain */
    for (int i = 0; i < NCPU; i++) {
        while (atomic_load(&rcu->reader_count[i]) > 0) {
            cpu_pause();
        }
    }
    
    /* All readers have completed */
    exo_spinlock_release(&rcu->writer_lock);
}

/**
 * Schedule callback after grace period (simplified version)
 */
void rcu_call(rcu_state_t *rcu, void (*func)(void *), void *arg) {
    /* Simplified: just synchronize then call */
    rcu_synchronize(rcu);
    func(arg);
}

/* ============================================================================
 * Adaptive Lock Implementation
 * ============================================================================ */

/**
 * Initialize adaptive lock
 */
void adaptive_lock_init(adaptive_lock_t *lock, const char *name) {
    atomic_store(&lock->current_type, LOCK_TYPE_TICKET);
    atomic_store(&lock->adaptation_counter, 0);
    
    lock->mcs_threshold = 16;        /* Switch to MCS with >16 waiters */
    lock->sleep_threshold_ns = 1000000; /* Sleep if hold time > 1ms */
    
    /* Initialize default implementation */
    exo_spinlock_init(&lock->impl.ticket, name);
    
    memset(&lock->stats, 0, sizeof(lock->stats));
    lock->name = name;
}

/**
 * Acquire adaptive lock
 */
void adaptive_lock_acquire(adaptive_lock_t *lock) {
    lock_type_t type = atomic_load(&lock->current_type);
    
    switch (type) {
        case LOCK_TYPE_TICKET:
            exo_spinlock_acquire(&lock->impl.ticket);
            break;
            
        case LOCK_TYPE_MCS: {
            /* Get per-CPU MCS node */
            struct cpu *c = mycpu();
            if (!c) panic("adaptive_lock: no CPU context");
            
            mcs_node_t *node = &c->mcs_node;  /* Each CPU has its own node */
            mcs_lock_acquire(&lock->impl.mcs, node);
            break;
        }
            
        case LOCK_TYPE_RWLOCK:
            rwlock_write_acquire(&lock->impl.rwlock);
            break;
            
        case LOCK_TYPE_SEQLOCK:
            seqlock_write_begin(&lock->impl.seqlock);
            break;
            
        default:
            panic("adaptive_lock: unknown lock type");
    }
    
    atomic_fetch_add((_Atomic uint64_t *)&lock->stats.acquisitions, 1);
}

/**
 * Release adaptive lock
 */
void adaptive_lock_release(adaptive_lock_t *lock) {
    lock_type_t type = atomic_load(&lock->current_type);
    
    switch (type) {
        case LOCK_TYPE_TICKET:
            exo_spinlock_release(&lock->impl.ticket);
            break;
            
        case LOCK_TYPE_MCS: {
            /* Get per-CPU MCS node */
            struct cpu *c = mycpu();
            if (!c) panic("adaptive_lock: no CPU context");
            
            mcs_node_t *node = &c->mcs_node;
            mcs_lock_release(&lock->impl.mcs, node);
            break;
        }
            
        case LOCK_TYPE_RWLOCK:
            rwlock_write_release(&lock->impl.rwlock);
            break;
            
        case LOCK_TYPE_SEQLOCK:
            seqlock_write_end(&lock->impl.seqlock);
            break;
            
        default:
            panic("adaptive_lock: unknown lock type");
    }
    
    /* Consider adaptation */
    adaptive_lock_adapt(lock);
}

/**
 * Adapt lock type based on contention patterns
 */
void adaptive_lock_adapt(adaptive_lock_t *lock) {
    /* Increment adaptation counter */
    uint64_t counter = atomic_fetch_add(&lock->adaptation_counter, 1);
    
    /* Only consider adaptation every 1000 operations */
    if ((counter % 1000) != 0) {
        return;
    }
    
    /* Analyze statistics */
    uint64_t contentions = atomic_load(&lock->stats.contentions);
    uint64_t acquisitions = atomic_load(&lock->stats.acquisitions);
    
    if (acquisitions == 0) return;
    
    double contention_rate = (double)contentions / acquisitions;
    
    /* High contention: switch to MCS */
    if (contention_rate > 0.5 && atomic_load(&lock->current_type) == LOCK_TYPE_TICKET) {
        /* TODO: Implement safe lock type transition */
        cprintf("adaptive_lock: would switch to MCS (contention rate: %d%%)\n",
                (int)(contention_rate * 100));
    }
}

/* ============================================================================
 * Statistics and Debugging
 * ============================================================================ */

/**
 * Get lock statistics
 */
void lock_get_stats(const void *lock, lock_stats_t *stats) {
    /* Determine lock type and extract stats */
    const exo_spinlock_t *spinlock = (const exo_spinlock_t *)lock;
    *stats = spinlock->stats; /* Works for all lock types due to layout */
}

/**
 * Reset lock statistics
 */
void lock_reset_stats(void *lock) {
    exo_spinlock_t *spinlock = (exo_spinlock_t *)lock;
    memset(&spinlock->stats, 0, sizeof(spinlock->stats));
}

/**
 * Dump lock state for debugging
 */
void lock_dump_state(const void *lock) {
    const exo_spinlock_t *spinlock = (const exo_spinlock_t *)lock;
    
    cprintf("Lock: %s\n", spinlock->name ? spinlock->name : "unnamed");
    cprintf("  Type: Ticket Spinlock\n");
    cprintf("  Head: %u, Tail: %u\n", 
            atomic_load(&spinlock->ticket_head),
            atomic_load(&spinlock->ticket_tail));
    cprintf("  Owner CPU: %d\n", atomic_load(&spinlock->owner_cpu));
    cprintf("  Statistics:\n");
    cprintf("    Acquisitions: %llu\n", atomic_load(&spinlock->stats.acquisitions));
    cprintf("    Contentions: %llu\n", atomic_load(&spinlock->stats.contentions));
    cprintf("    Current Waiters: %u\n", atomic_load(&spinlock->stats.current_waiters));
    cprintf("    Max Waiters: %u\n", atomic_load(&spinlock->stats.max_waiters));
}

/**
 * Get lock type name
 */
const char *lock_type_name(lock_type_t type) {
    switch (type) {
        case LOCK_TYPE_TICKET:    return "Ticket";
        case LOCK_TYPE_MCS:       return "MCS";
        case LOCK_TYPE_RWLOCK:    return "RWLock";
        case LOCK_TYPE_SEQLOCK:   return "SeqLock";
        case LOCK_TYPE_SLEEPLOCK: return "SleepLock";
        case LOCK_TYPE_RCU:       return "RCU";
        default:                  return "Unknown";
    }
}

/* ============================================================================
 * Capability Integration
 * ============================================================================ */

/**
 * Set required capability for lock
 */
void lock_set_capability(void *lock, cap_id_t cap) {
    exo_spinlock_t *spinlock = (exo_spinlock_t *)lock;
    spinlock->required_cap = cap;
}

/**
 * Get required capability for lock
 */
cap_id_t lock_get_capability(const void *lock) {
    const exo_spinlock_t *spinlock = (const exo_spinlock_t *)lock;
    return spinlock->required_cap;
}