/* stdatomic.h - C11/C17 atomic operations */
#ifndef _STDATOMIC_H
#define _STDATOMIC_H

/* Basic atomic types */
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

/* Atomic flag */
typedef struct {
    atomic_bool _Value;
} atomic_flag;

#define ATOMIC_FLAG_INIT { 0 }

/* Memory order */
typedef enum {
    memory_order_relaxed,
    memory_order_consume,
    memory_order_acquire,
    memory_order_release,
    memory_order_acq_rel,
    memory_order_seq_cst
} memory_order;

/* Atomic operations - simplified implementations */
#define atomic_store(PTR, VAL) (*(PTR) = (VAL))
#define atomic_load(PTR) (*(PTR))
#define atomic_exchange(PTR, VAL) __sync_lock_test_and_set(PTR, VAL)
#define atomic_compare_exchange_strong(PTR, EXPECTED, DESIRED) \
    __sync_bool_compare_and_swap(PTR, *(EXPECTED), DESIRED)
#define atomic_fetch_add(PTR, VAL) __sync_fetch_and_add(PTR, VAL)
#define atomic_fetch_sub(PTR, VAL) __sync_fetch_and_sub(PTR, VAL)

/* Atomic flag operations */
#define atomic_flag_test_and_set(PTR) __sync_lock_test_and_set(&(PTR)->_Value, 1)
#define atomic_flag_clear(PTR) __sync_lock_release(&(PTR)->_Value)

/* Thread fence */
#define atomic_thread_fence(MO) __sync_synchronize()
#define atomic_signal_fence(MO) __asm__ __volatile__("" ::: "memory")

/* Atomic init */
#define atomic_init(PTR, VAL) (*(PTR) = (VAL))

/* Lock-free property */
#define atomic_is_lock_free(PTR) (sizeof(*(PTR)) <= sizeof(void*))

#define ATOMIC_VAR_INIT(VAL) (VAL)

#endif /* _STDATOMIC_H */