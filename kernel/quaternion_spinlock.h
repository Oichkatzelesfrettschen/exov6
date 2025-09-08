#pragma once
#include "rspinlock.h"
#include "kernel_compat.h"

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
