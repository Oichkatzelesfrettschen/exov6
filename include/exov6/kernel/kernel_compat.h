/**
 * @file kernel_compat.h
 * @brief Kernel compatibility layer for standard library functions
 *
 * Provides kernel-compatible implementations of standard library functions
 * that are not available in the kernel environment.
 */

#pragma once

#ifndef KERNEL_COMPAT_H
#define KERNEL_COMPAT_H

#ifdef __KERNEL__

/* Atomic operations compatibility */
#define _Atomic volatile
#define atomic_load(ptr) __atomic_load_n(ptr, __ATOMIC_SEQ_CST)
#define atomic_store(ptr, val) __atomic_store_n(ptr, val, __ATOMIC_SEQ_CST)
#define atomic_exchange(ptr, val) __atomic_exchange_n(ptr, val, __ATOMIC_SEQ_CST)
#define atomic_compare_exchange_strong(ptr, expected, desired) \
    __atomic_compare_exchange_n(ptr, expected, desired, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST)
#define atomic_fetch_add(ptr, val) __atomic_fetch_add(ptr, val, __ATOMIC_SEQ_CST)
#define atomic_fetch_sub(ptr, val) __atomic_fetch_sub(ptr, val, __ATOMIC_SEQ_CST)
#define atomic_fetch_add_explicit(ptr, val, order) __atomic_fetch_add(ptr, val, order)
#define atomic_fetch_sub_explicit(ptr, val, order) __atomic_fetch_sub(ptr, val, order)
#define atomic_store_explicit(ptr, val, order) __atomic_store_n(ptr, val, order)
#define atomic_load_explicit(ptr, order) __atomic_load_n(ptr, order)

/* Memory ordering constants */
#define memory_order_relaxed __ATOMIC_RELAXED
#define memory_order_acquire __ATOMIC_ACQUIRE
#define memory_order_release __ATOMIC_RELEASE
#define memory_order_acq_rel __ATOMIC_ACQ_REL
#define memory_order_seq_cst __ATOMIC_SEQ_CST

/* Boolean compatibility */
#ifndef __cplusplus
#if !defined(bool) && !defined(__bool_true_false_are_defined)
#ifdef __STDC_VERSION__
#if __STDC_VERSION__ >= 202311L
#define bool _Bool
#define true 1
#define false 0
#else
typedef int bool;
#define true 1
#define false 0
#endif
#else
typedef int bool;
#define true 1
#define false 0
#endif
#define __bool_true_false_are_defined 1
#endif
#endif

/* noreturn compatibility */
#ifdef __STDC_VERSION__
#if __STDC_VERSION__ >= 202311L
#define noreturn _Noreturn
#elif __STDC_VERSION__ >= 201112L
#define noreturn _Noreturn
#else
#define noreturn __attribute__((noreturn))
#endif
#else
#define noreturn __attribute__((noreturn))
#endif

/* Math functions */
static inline double kernel_sqrt(double x) {
    if (x <= 0.0) return 0.0;
    double guess = x / 2.0;
    for (int i = 0; i < 10; i++) {
        guess = (guess + x / guess) / 2.0;
    }
    return guess;
}

static inline double kernel_fabs(double x) {
    return x < 0.0 ? -x : x;
}

#define sqrt kernel_sqrt
#define fabs kernel_fabs

/* Memory management */
extern void *kalloc(void);
extern void kfree(char *);
#define malloc(size) kalloc()
#define free(ptr) kfree((char*)ptr)

/* String functions */
extern int memcmp(const void *s1, const void *s2, size_t n);

#endif /* __KERNEL__ */

#endif /* KERNEL_COMPAT_H */
