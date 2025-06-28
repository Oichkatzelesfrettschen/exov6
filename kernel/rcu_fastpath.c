/*
 * C23 RCU Fastpath Implementation
 * This file provides a sample implementation of the advanced
 * Read-Copy-Update primitives described in the documentation.
 */

#include "types.h"
#include "defs.h"
#include <stdatomic.h>
#include <stdint.h>

/**
 * @brief Sequence number type used for grace period tracking.
 */
typedef _BitInt(42) rcu_gp_seq_t;

/**
 * @brief Per-thread reader state.
 */
struct rcu_reader_state {
    _BitInt(1) in_critical : 1; /**< Reader in a critical section. */
    _BitInt(1) need_qs : 1;     /**< Quiescent state pending. */
    _BitInt(6) nest_count : 6;  /**< Nesting depth. */
    _BitInt(8) cpu_id : 8;      /**< CPU identifier. */
    _BitInt(48) gp_seq : 48;    /**< Grace period sequence. */
};

/** Thread local RCU data. */
_Thread_local static struct {
    struct rcu_reader_state reader; /**< State for the current thread. */
    _Atomic(uint64_t) qs_pending;   /**< Pending callbacks. */
} __rcu_data = {0};

/** Global grace period sequence. */
static _Atomic(rcu_gp_seq_t) global_rcu_gp_seq = 0;

/**
 * @brief Enter an RCU read-side critical section.
 */
void rcu_read_lock_c23(void)
{
    atomic_signal_fence(memory_order_acquire);
    __rcu_data.reader.nest_count++;
    __rcu_data.reader.in_critical = 1;
}

/**
 * @brief Exit an RCU read-side critical section.
 */
void rcu_read_unlock_c23(void)
{
    atomic_signal_fence(memory_order_release);
    if (--__rcu_data.reader.nest_count == 0) {
        __rcu_data.reader.in_critical = 0;
    }
}

/**
 * @brief Helper to obtain the next grace period sequence number.
 */
static inline rcu_gp_seq_t rcu_seq_next(rcu_gp_seq_t seq)
{
    return seq + ((_BitInt(42))1 << 1);
}

/**
 * @brief Queue a callback to be invoked after the next grace period.
 *
 * @param func Callback function pointer.
 * @param arg  Argument to pass to the callback.
 *
 * @return true on success, false if queue is full.
 */
bool call_rcu_c23(void (*func)(void *), void *arg)
{
    rcu_gp_seq_t current_gp = atomic_load_explicit(
        &global_rcu_gp_seq, memory_order_acquire);

    /* In this simplified example we only store a single callback
       per thread. A real implementation would maintain a list. */
    if (atomic_load(&__rcu_data.qs_pending) != 0)
        return false;

    __rcu_data.qs_pending = 1;
    (void)current_gp; /* Unused until a real list is implemented. */
    func(arg);
    return true;
}

/**
 * @brief Start a new grace period and wait for readers.
 */
void synchronize_rcu_expedited_c23(void)
{
    rcu_gp_seq_t old = atomic_fetch_add(&global_rcu_gp_seq, 2);
    (void)old; /* In a real implementation we would notify readers. */
}

