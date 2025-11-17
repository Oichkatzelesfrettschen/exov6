#pragma once
/**
 * @file qspinlock.h
 * @brief Modern NUMA-aware queued spinlock
 *
 * This header provides the kernel interface to the modern qspinlock
 * implementation. The actual definitions are in include/exo_lock.h.
 *
 * Use this header when you need:
 * - struct qspinlock (not struct spinlock!)
 * - qspin_init/lock/unlock/trylock functions
 * - NUMA-aware MCS-based queue spinlock
 *
 * @version 1.0 (Phase 1-7 implementation)
 */

#include <types.h>
#include "config.h"

/* Pull in modern qspinlock from unified header */
#ifndef __EXOLOCK_TYPES_DEFINED
#define __EXOLOCK_TYPES_DEFINED
#include "exo_lock.h"
#endif

/* Re-export the key types and functions for kernel use */

/* Type alias for compatibility */
typedef struct qspinlock qspinlock_t;

/* Lock hierarchy levels (from DAG) */
#ifndef LOCK_LEVEL_SCHEDULER
#define LOCK_LEVEL_SCHEDULER      10
#define LOCK_LEVEL_MEMORY         20
#define LOCK_LEVEL_IPC            30
#define LOCK_LEVEL_FILESYSTEM     40
#define LOCK_LEVEL_DEVICE         50
#define LOCK_LEVEL_NET            60
#define LOCK_LEVEL_CRYPTO         70
#define LOCK_LEVEL_USER           80
#endif

/* API functions are defined in exo_lock.h:
 *
 * void qspin_init(struct qspinlock *lock, const char *name, uint32_t dag_level);
 * void qspin_lock(struct qspinlock *lock);
 * int qspin_trylock(struct qspinlock *lock);
 * void qspin_unlock(struct qspinlock *lock);
 * void qspin_dump_stats(struct qspinlock *lock, const char *name);
 * void qspin_reset_stats(struct qspinlock *lock);
 */

#endif /* QSPINLOCK_H */
