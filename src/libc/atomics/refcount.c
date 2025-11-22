/*
 * refcount.c - C17 Atomic Reference Counting
 *
 * Lock-free reference counting using C17 atomics
 * For use in capability management and resource tracking
 */

#include <stdatomic.h>
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

/* Type-safe atomic reference counter */
typedef struct {
    _Alignas(64) _Atomic(uint32_t) count;
    char padding[60];  /* Prevent false sharing */
} refcount_t;

/* Static assertions for safety */
_Static_assert(sizeof(refcount_t) == 64, "refcount must be cache-line sized");
_Static_assert(alignof(refcount_t) == 64, "refcount must be cache-line aligned");

/**
 * @brief Initialize a reference counter.
 * @param ref Pointer to reference counter
 * @param initial Initial reference count (typically 1)
 *
 * C17 Features: atomic_init for initialization
 */
static inline void refcount_init(refcount_t *ref, uint32_t initial)
{
    atomic_init(&ref->count, initial);
}

/**
 * @brief Increment reference count.
 * @param ref Pointer to reference counter
 *
 * Returns: New reference count
 * 
 * C17 Features: atomic_fetch_add with memory ordering
 */
static inline uint32_t refcount_inc(refcount_t *ref)
{
    return atomic_fetch_add_explicit(&ref->count, 1, memory_order_relaxed) + 1;
}

/**
 * @brief Decrement reference count.
 * @param ref Pointer to reference counter
 *
 * Returns: true if this was the last reference (count reached 0)
 *
 * C17 Features: atomic_fetch_sub with release-acquire ordering
 */
static inline bool refcount_dec(refcount_t *ref)
{
    uint32_t old = atomic_fetch_sub_explicit(&ref->count, 1, memory_order_release);
    
    if (old == 1) {
        /* This was the last reference - synchronize with all previous operations */
        atomic_thread_fence(memory_order_acquire);
        return true;
    }
    
    return false;
}

/**
 * @brief Get current reference count.
 * @param ref Pointer to reference counter
 *
 * Returns: Current reference count
 *
 * C17 Features: atomic_load with acquire ordering
 */
static inline uint32_t refcount_get(refcount_t *ref)
{
    return atomic_load_explicit(&ref->count, memory_order_acquire);
}

/**
 * @brief Increment reference count unless zero.
 * @param ref Pointer to reference counter
 *
 * Returns: true if increment succeeded, false if count was zero
 *
 * C17 Features: atomic_compare_exchange_weak for lock-free algorithm
 */
static inline bool refcount_inc_not_zero(refcount_t *ref)
{
    uint32_t old = atomic_load_explicit(&ref->count, memory_order_relaxed);
    
    do {
        if (old == 0) {
            return false;
        }
    } while (!atomic_compare_exchange_weak_explicit(
        &ref->count, &old, old + 1,
        memory_order_relaxed,
        memory_order_relaxed
    ));
    
    return true;
}

/**
 * @brief Add to reference count.
 * @param ref Pointer to reference counter
 * @param delta Amount to add
 *
 * Returns: New reference count
 *
 * C17 Features: atomic_fetch_add for arbitrary increments
 */
static inline uint32_t refcount_add(refcount_t *ref, uint32_t delta)
{
    return atomic_fetch_add_explicit(&ref->count, delta, memory_order_relaxed) + delta;
}

/**
 * @brief Subtract from reference count and test for zero.
 * @param ref Pointer to reference counter
 * @param delta Amount to subtract
 *
 * Returns: true if count reached zero
 *
 * C17 Features: Full memory barriers for correctness
 */
static inline bool refcount_sub_and_test(refcount_t *ref, uint32_t delta)
{
    uint32_t old = atomic_fetch_sub_explicit(&ref->count, delta, memory_order_release);
    
    if (old == delta) {
        atomic_thread_fence(memory_order_acquire);
        return true;
    }
    
    return false;
}
