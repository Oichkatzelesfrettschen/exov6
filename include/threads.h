/*
 * threads.h - C17 Threading Support
 *
 * ISO C17 standard threading primitives
 * This will be the foundation for POSIX pthreads
 */

#ifndef _THREADS_H
#define _THREADS_H

#include <stdint.h>
#include <stddef.h>
#include <time.h>

/* Thread types */
typedef uintptr_t thrd_t;
typedef int (*thrd_start_t)(void *);

/* Mutex types */
typedef struct {
    _Atomic(uint32_t) lock;
    _Atomic(uint32_t) owner;
    uint32_t type;
    char padding[52];  /* Cache-line alignment */
} mtx_t;

/* Condition variable type */
typedef struct {
    _Atomic(uint32_t) waiters;
    _Atomic(uint32_t) signal_pending;
    char padding[56];
} cnd_t;

/* Thread-specific storage */
typedef uint32_t tss_t;
typedef void (*tss_dtor_t)(void *);

/* Once-only initialization */
typedef _Atomic(uint32_t) once_flag;
#define ONCE_FLAG_INIT 0

/* Thread return values */
enum {
    thrd_success = 0,
    thrd_timedout = 1,
    thrd_busy = 2,
    thrd_error = 3,
    thrd_nomem = 4
};

/* Mutex types */
enum {
    mtx_plain = 0,
    mtx_recursive = 1,
    mtx_timed = 2
};

/* Thread functions */
int thrd_create(thrd_t *thr, thrd_start_t func, void *arg);
int thrd_equal(thrd_t lhs, thrd_t rhs);
thrd_t thrd_current(void);
int thrd_sleep(const struct timespec *duration, struct timespec *remaining);
void thrd_yield(void);
_Noreturn void thrd_exit(int res);
int thrd_detach(thrd_t thr);
int thrd_join(thrd_t thr, int *res);

/* Mutex functions */
int mtx_init(mtx_t *mtx, int type);
int mtx_lock(mtx_t *mtx);
int mtx_timedlock(mtx_t *restrict mtx, const struct timespec *restrict ts);
int mtx_trylock(mtx_t *mtx);
int mtx_unlock(mtx_t *mtx);
void mtx_destroy(mtx_t *mtx);

/* Condition variable functions */
int cnd_init(cnd_t *cond);
int cnd_signal(cnd_t *cond);
int cnd_broadcast(cnd_t *cond);
int cnd_wait(cnd_t *cond, mtx_t *mtx);
int cnd_timedwait(cnd_t *restrict cond, mtx_t *restrict mtx,
                  const struct timespec *restrict ts);
void cnd_destroy(cnd_t *cond);

/* Thread-specific storage */
int tss_create(tss_t *key, tss_dtor_t dtor);
void *tss_get(tss_t key);
int tss_set(tss_t key, void *val);
void tss_delete(tss_t key);

/* Once-only initialization */
void call_once(once_flag *flag, void (*func)(void));

/* Static assertions for ABI stability */
_Static_assert(sizeof(mtx_t) == 64, "mutex must be cache-line sized");
_Static_assert(sizeof(cnd_t) == 64, "condition variable must be cache-line sized");
_Static_assert(alignof(mtx_t) == 64, "mutex must be cache-line aligned");
_Static_assert(alignof(cnd_t) == 64, "condition variable must be cache-line aligned");

#endif /* _THREADS_H */