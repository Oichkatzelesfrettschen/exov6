#pragma once

/*
 * Modern Locking Mechanisms for ExoKernel v6
 * Implements MCS locks, Read-Write locks, and Seqlocks
 * Pure C17 implementation without C11 atomics
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

struct cpu;

/*
 * MCS Lock (Mellor-Crummey and Scott)
 * Provides FIFO ordering with local spinning for cache efficiency
 */
struct mcs_node {
    volatile struct mcs_node *next;
    volatile int locked;
};

struct mcs_lock {
    volatile struct mcs_node *tail;
    const char *name;
};

/*
 * Read-Write Lock
 * Allows multiple concurrent readers or a single writer
 */
struct rwlock {
    volatile int32_t lock;  // -1 = writer, 0 = free, >0 = reader count
    volatile uint32_t writers_waiting;
    const char *name;
};

/*
 * Sequence Lock (Seqlock)
 * Optimized for frequent reads with infrequent writes
 */
struct seqlock {
    volatile uint32_t sequence;
    struct spinlock lock;  // Protects writers
    const char *name;
};

/*
 * Hybrid Lock
 * Combines spinlock for short critical sections with blocking for long waits
 */
struct hybrid_lock {
    volatile uint32_t locked;
    volatile uint32_t waiters;
    const char *name;
    struct cpu *owner;
};

// MCS Lock Operations
void mcs_init(struct mcs_lock *lock, const char *name);
void mcs_acquire(struct mcs_lock *lock, struct mcs_node *node);
void mcs_release(struct mcs_lock *lock, struct mcs_node *node);
int mcs_tryacquire(struct mcs_lock *lock, struct mcs_node *node);

// Read-Write Lock Operations
void rwlock_init(struct rwlock *lock, const char *name);
void rwlock_acquire_read(struct rwlock *lock);
void rwlock_release_read(struct rwlock *lock);
void rwlock_acquire_write(struct rwlock *lock);
void rwlock_release_write(struct rwlock *lock);
int rwlock_try_read(struct rwlock *lock);
int rwlock_try_write(struct rwlock *lock);

// Seqlock Operations
void seqlock_init(struct seqlock *lock, const char *name);
uint32_t seqlock_read_begin(struct seqlock *lock);
int seqlock_read_retry(struct seqlock *lock, uint32_t seq);
void seqlock_write_begin(struct seqlock *lock);
void seqlock_write_end(struct seqlock *lock);

// Hybrid Lock Operations
void hybrid_init(struct hybrid_lock *lock, const char *name);
void hybrid_acquire(struct hybrid_lock *lock);
void hybrid_release(struct hybrid_lock *lock);
int hybrid_tryacquire(struct hybrid_lock *lock);

// Architecture-specific memory barriers (defined in arch_x86_64.h)
extern void mfence(void);
extern void lfence(void);
extern void sfence(void);

// Atomic operations using GCC built-ins (C17 compatible)
#define atomic_load(ptr) __sync_add_and_fetch(ptr, 0)
#define atomic_store(ptr, val) __sync_lock_test_and_set(ptr, val)
#define atomic_add(ptr, val) __sync_add_and_fetch(ptr, val)
#define atomic_sub(ptr, val) __sync_sub_and_fetch(ptr, val)
#define atomic_cas(ptr, old, new) __sync_bool_compare_and_swap(ptr, old, new)
#define atomic_xchg(ptr, val) __sync_lock_test_and_set(ptr, val)

// Memory ordering helpers
#define smp_mb() mfence()
#define smp_rmb() lfence()
#define smp_wmb() sfence()
#define compiler_barrier() __asm__ volatile("" ::: "memory")