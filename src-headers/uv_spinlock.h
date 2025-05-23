#pragma once

#include <stdint.h>

/* Simple spinlock implementation inspired by libuv's uv_spinlock_t. */

typedef struct {
    _Atomic int lock;
} uv_spinlock_t;

static inline void uv_spinlock_init(uv_spinlock_t *sl) {
    __atomic_store_n(&sl->lock, 0, __ATOMIC_RELAXED);
}

static inline int uv_spinlock_trylock(uv_spinlock_t *sl) {
    int expected = 0;
    return __atomic_compare_exchange_n(&sl->lock, &expected, 1, 0,
                                       __ATOMIC_ACQUIRE, __ATOMIC_RELAXED);
}

static inline void uv_spinlock_lock(uv_spinlock_t *sl) {
    while (!uv_spinlock_trylock(sl)) {
#ifdef __x86_64__
        __asm__ volatile("pause" ::: "memory");
#else
        __asm__ volatile("" ::: "memory");
#endif
    }
}

static inline void uv_spinlock_unlock(uv_spinlock_t *sl) {
    __atomic_store_n(&sl->lock, 0, __ATOMIC_RELEASE);
}

#define UV_SPINLOCK_INITIALIZER { 0 }

