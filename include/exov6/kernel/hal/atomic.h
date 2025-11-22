#pragma once

/**
 * @file hal/atomic.h
 * @brief Hardware Abstraction Layer for atomic operations
 * 
 * Pure C17 implementation using <stdatomic.h> for lock-free programming.
 */

#include <stdatomic.h>
#include <stdint.h>
#include <stdbool.h>

// Atomic types using C17 standard atomics
typedef _Atomic(int32_t) hal_atomic32_t;
typedef _Atomic(int64_t) hal_atomic64_t;
typedef _Atomic(void*) hal_atomic_ptr_t;

/**
 * @brief Initialize atomic variable
 */
#define HAL_ATOMIC_INIT(value) ATOMIC_VAR_INIT(value)

/**
 * @brief Atomic load with memory order
 */
#define hal_atomic_load(ptr, order) \
    atomic_load_explicit(ptr, order)

/**
 * @brief Atomic store with memory order
 */
#define hal_atomic_store(ptr, value, order) \
    atomic_store_explicit(ptr, value, order)

/**
 * @brief Atomic exchange
 */
#define hal_atomic_exchange(ptr, value, order) \
    atomic_exchange_explicit(ptr, value, order)

/**
 * @brief Atomic compare and exchange
 */
#define hal_atomic_compare_exchange(ptr, expected, desired, order) \
    atomic_compare_exchange_strong_explicit(ptr, expected, desired, order, order)

/**
 * @brief Atomic fetch and add
 */
#define hal_atomic_fetch_add(ptr, value, order) \
    atomic_fetch_add_explicit(ptr, value, order)

/**
 * @brief Atomic fetch and subtract
 */
#define hal_atomic_fetch_sub(ptr, value, order) \
    atomic_fetch_sub_explicit(ptr, value, order)

/**
 * @brief Atomic fetch and OR
 */
#define hal_atomic_fetch_or(ptr, value, order) \
    atomic_fetch_or_explicit(ptr, value, order)

/**
 * @brief Atomic fetch and AND
 */
#define hal_atomic_fetch_and(ptr, value, order) \
    atomic_fetch_and_explicit(ptr, value, order)

/**
 * @brief Atomic increment
 */
static inline int32_t hal_atomic_inc(hal_atomic32_t* ptr) {
    return hal_atomic_fetch_add(ptr, 1, memory_order_seq_cst);
}

/**
 * @brief Atomic decrement
 */
static inline int32_t hal_atomic_dec(hal_atomic32_t* ptr) {
    return hal_atomic_fetch_sub(ptr, 1, memory_order_seq_cst);
}

/**
 * @brief Atomic test and set
 */
static inline bool hal_atomic_test_and_set(hal_atomic32_t* ptr, int32_t bit) {
    int32_t mask = (1 << bit);
    int32_t old = hal_atomic_fetch_or(ptr, mask, memory_order_seq_cst);
    return (old & mask) != 0;
}

/**
 * @brief Atomic test and clear
 */
static inline bool hal_atomic_test_and_clear(hal_atomic32_t* ptr, int32_t bit) {
    int32_t mask = (1 << bit);
    int32_t old = hal_atomic_fetch_and(ptr, ~mask, memory_order_seq_cst);
    return (old & mask) != 0;
}

/**
 * @brief Spinlock using C17 atomics
 */
typedef struct {
    _Alignas(64) atomic_flag lock;  // Cache-line aligned
    char padding[64 - sizeof(atomic_flag)];
} hal_spinlock_t;

/**
 * @brief Initialize spinlock
 */
static inline void hal_spinlock_init(hal_spinlock_t* lock) {
    atomic_flag_clear(&lock->lock);
}

/**
 * @brief Acquire spinlock
 */
static inline void hal_spinlock_acquire(hal_spinlock_t* lock) {
    while (atomic_flag_test_and_set_explicit(&lock->lock, memory_order_acquire)) {
        // Exponential backoff
        for (volatile int32_t i = 0; i < 100; i++) {
            __asm__ volatile("" ::: "memory");
        }
    }
}

/**
 * @brief Try to acquire spinlock
 */
static inline bool hal_spinlock_try_acquire(hal_spinlock_t* lock) {
    return !atomic_flag_test_and_set_explicit(&lock->lock, memory_order_acquire);
}

/**
 * @brief Release spinlock
 */
static inline void hal_spinlock_release(hal_spinlock_t* lock) {
    atomic_flag_clear_explicit(&lock->lock, memory_order_release);
}

// Compile-time assertions
_Static_assert(sizeof(hal_spinlock_t) == 64, "Spinlock must be cache-line sized");
_Static_assert(_Alignof(hal_spinlock_t) == 64, "Spinlock must be cache-line aligned");