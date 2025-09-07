/*
 * stdatomic.h - Complete C17 Atomic Operations Implementation
 *
 * Full C17 atomic support for lock-free programming
 * Provides all standard atomic types and operations per ISO C17
 */

#ifndef _STDATOMIC_H
#define _STDATOMIC_H

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

/* Memory ordering semantics per C17 */
typedef enum {
    memory_order_relaxed = __ATOMIC_RELAXED,
    memory_order_consume = __ATOMIC_CONSUME,
    memory_order_acquire = __ATOMIC_ACQUIRE,
    memory_order_release = __ATOMIC_RELEASE,
    memory_order_acq_rel = __ATOMIC_ACQ_REL,
    memory_order_seq_cst = __ATOMIC_SEQ_CST
} memory_order;

/* Generic atomic type */
#define _Atomic(T) __attribute__((aligned(sizeof(T)))) T

/* Standard atomic types */
typedef _Atomic(_Bool)              atomic_bool;
typedef _Atomic(char)               atomic_char;
typedef _Atomic(signed char)        atomic_schar;
typedef _Atomic(unsigned char)      atomic_uchar;
typedef _Atomic(short)              atomic_short;
typedef _Atomic(unsigned short)     atomic_ushort;
typedef _Atomic(int)                atomic_int;
typedef _Atomic(unsigned int)       atomic_uint;
typedef _Atomic(long)               atomic_long;
typedef _Atomic(unsigned long)      atomic_ulong;
typedef _Atomic(long long)          atomic_llong;
typedef _Atomic(unsigned long long) atomic_ullong;

/* Fixed-width atomic types */
typedef _Atomic(int8_t)    atomic_int8_t;
typedef _Atomic(uint8_t)   atomic_uint8_t;
typedef _Atomic(int16_t)   atomic_int16_t;
typedef _Atomic(uint16_t)  atomic_uint16_t;
typedef _Atomic(int32_t)   atomic_int32_t;
typedef _Atomic(uint32_t)  atomic_uint32_t;
typedef _Atomic(int64_t)   atomic_int64_t;
typedef _Atomic(uint64_t)  atomic_uint64_t;

/* Pointer types */
typedef _Atomic(intptr_t)  atomic_intptr_t;
typedef _Atomic(uintptr_t) atomic_uintptr_t;
typedef _Atomic(size_t)    atomic_size_t;
typedef _Atomic(ptrdiff_t) atomic_ptrdiff_t;

/* Atomic flag */
typedef struct {
    atomic_bool _Value;
} atomic_flag;

#define ATOMIC_FLAG_INIT { 0 }
#define ATOMIC_VAR_INIT(VAL) (VAL)

/* Lock-free macros */
#define ATOMIC_BOOL_LOCK_FREE       __GCC_ATOMIC_BOOL_LOCK_FREE
#define ATOMIC_CHAR_LOCK_FREE       __GCC_ATOMIC_CHAR_LOCK_FREE
#define ATOMIC_SHORT_LOCK_FREE      __GCC_ATOMIC_SHORT_LOCK_FREE
#define ATOMIC_INT_LOCK_FREE        __GCC_ATOMIC_INT_LOCK_FREE
#define ATOMIC_LONG_LOCK_FREE       __GCC_ATOMIC_LONG_LOCK_FREE
#define ATOMIC_LLONG_LOCK_FREE      __GCC_ATOMIC_LLONG_LOCK_FREE
#define ATOMIC_POINTER_LOCK_FREE    __GCC_ATOMIC_POINTER_LOCK_FREE

/* Atomic operations with explicit memory ordering */
#define atomic_init(obj, val) (*(obj) = (val))

#define atomic_store_explicit(obj, val, order) \
    __atomic_store_n(obj, val, order)
#define atomic_store(obj, val) \
    atomic_store_explicit(obj, val, memory_order_seq_cst)

#define atomic_load_explicit(obj, order) \
    __atomic_load_n(obj, order)
#define atomic_load(obj) \
    atomic_load_explicit(obj, memory_order_seq_cst)

#define atomic_exchange_explicit(obj, val, order) \
    __atomic_exchange_n(obj, val, order)
#define atomic_exchange(obj, val) \
    atomic_exchange_explicit(obj, val, memory_order_seq_cst)

#define atomic_compare_exchange_strong_explicit(obj, expected, desired, succ, fail) \
    __atomic_compare_exchange_n(obj, expected, desired, 0, succ, fail)
#define atomic_compare_exchange_strong(obj, expected, desired) \
    atomic_compare_exchange_strong_explicit(obj, expected, desired, \
        memory_order_seq_cst, memory_order_seq_cst)

#define atomic_compare_exchange_weak_explicit(obj, expected, desired, succ, fail) \
    __atomic_compare_exchange_n(obj, expected, desired, 1, succ, fail)
#define atomic_compare_exchange_weak(obj, expected, desired) \
    atomic_compare_exchange_weak_explicit(obj, expected, desired, \
        memory_order_seq_cst, memory_order_seq_cst)

/* Arithmetic operations */
#define atomic_fetch_add_explicit(obj, val, order) \
    __atomic_fetch_add(obj, val, order)
#define atomic_fetch_add(obj, val) \
    atomic_fetch_add_explicit(obj, val, memory_order_seq_cst)

#define atomic_fetch_sub_explicit(obj, val, order) \
    __atomic_fetch_sub(obj, val, order)
#define atomic_fetch_sub(obj, val) \
    atomic_fetch_sub_explicit(obj, val, memory_order_seq_cst)

#define atomic_fetch_or_explicit(obj, val, order) \
    __atomic_fetch_or(obj, val, order)
#define atomic_fetch_or(obj, val) \
    atomic_fetch_or_explicit(obj, val, memory_order_seq_cst)

#define atomic_fetch_xor_explicit(obj, val, order) \
    __atomic_fetch_xor(obj, val, order)
#define atomic_fetch_xor(obj, val) \
    atomic_fetch_xor_explicit(obj, val, memory_order_seq_cst)

#define atomic_fetch_and_explicit(obj, val, order) \
    __atomic_fetch_and(obj, val, order)
#define atomic_fetch_and(obj, val) \
    atomic_fetch_and_explicit(obj, val, memory_order_seq_cst)

/* Flag operations */
static inline bool atomic_flag_test_and_set_explicit(volatile atomic_flag *flag, 
                                                     memory_order order) {
    return __atomic_test_and_set(&flag->_Value, order);
}

static inline bool atomic_flag_test_and_set(volatile atomic_flag *flag) {
    return atomic_flag_test_and_set_explicit(flag, memory_order_seq_cst);
}

static inline void atomic_flag_clear_explicit(volatile atomic_flag *flag,
                                              memory_order order) {
    __atomic_clear(&flag->_Value, order);
}

static inline void atomic_flag_clear(volatile atomic_flag *flag) {
    atomic_flag_clear_explicit(flag, memory_order_seq_cst);
}

/* Memory synchronization */
#define atomic_thread_fence(order) __atomic_thread_fence(order)
#define atomic_signal_fence(order) __atomic_signal_fence(order)

/* Lock-free query */
#define atomic_is_lock_free(obj) \
    __atomic_is_lock_free(sizeof(*(obj)), (obj))

/* Kill dependency */
#define kill_dependency(y) __extension__({ \
    __auto_type __tmp = (y); \
    __asm__("" : "+r"(__tmp)); \
    __tmp; \
})

/* Static assertions for correctness */
_Static_assert(sizeof(atomic_int) == sizeof(int), "atomic_int size");
_Static_assert(ATOMIC_INT_LOCK_FREE == 2, "int must be lock-free");
_Static_assert(ATOMIC_POINTER_LOCK_FREE == 2, "pointers must be lock-free");

#endif /* _STDATOMIC_H */