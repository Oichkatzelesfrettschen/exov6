#pragma once
#include "rspinlock.h"

/* C23 compatible bool definition for kernel */
#ifndef __cplusplus
#ifndef bool
#ifdef __STDC_VERSION__
#if __STDC_VERSION__ >= 202311L
/* C23 has built-in _Bool */
#define bool _Bool
#define true 1
#define false 0
#else
/* Pre-C23 fallback */
typedef int bool;
#define true 1
#define false 0
#endif
#else
/* Fallback for older compilers */
typedef int bool;
#define true 1
#define false 0
#endif
#endif
#endif

/**
 * @brief Quaternion spinlock providing recursive locking semantics.
 */
typedef struct quaternion_spinlock {
  struct rspinlock spin; /**< underlying recursive lock */
  int level;             /**< recursion level modulo four */
} quaternion_spinlock_t;

static inline void qlock_init(quaternion_spinlock_t *q, char *name) {
  rinitlock(&q->spin, name);
  q->level = 0;
}

static inline void qlock_acquire(quaternion_spinlock_t *q) {
  racquire(&q->spin);
  q->level = (q->level + 1) % 4;
}

static inline void qlock_release(quaternion_spinlock_t *q) {
  q->level = (q->level - 1 + 4) % 4;
  rrelease(&q->spin);
}

static inline bool qlock_holding(quaternion_spinlock_t *q) {
  return rholding(&q->spin);
}

#define WITH_QLOCK(q)                                                          \
  for (int _once = (qlock_acquire(q), 0); !_once; qlock_release(q), _once = 1)
