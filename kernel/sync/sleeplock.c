// Sleeping locks

#include <types.h>
#include "defs.h"
#include "param.h"
#include "arch.h"
#include "memlayout.h"
#include "mmu.h"
#include "proc.h"
#include "spinlock.h"
#include "exo_lock.h"  // Modern lock subsystem (Phase 6)
#include "sleeplock.h"

void
initsleeplock(struct sleeplock *lk, char *name, uint32_t dag_level)
{
  // Internal qspinlock at dag_level - 1 (must be lower than sleeplock itself)
  // This allows: acquire internal lock (level N-1) → then track sleeplock (level N)
  qspin_init(&lk->lk, "sleeplock_internal", dag_level > 0 ? dag_level - 1 : 0);
  lk->name = name;
  lk->dag_level = dag_level;
  lk->locked = 0;
  lk->pid = 0;
}

void
acquiresleep(struct sleeplock *lk)
{
#ifdef USE_DAG_CHECKING
  // Validate DAG ordering BEFORE acquiring (Phase 6)
  if (!dag_validate_acquisition(lk, lk->name, lk->dag_level,
                                LOCK_TYPE_SLEEP, __FILE__, __LINE__)) {
#ifdef DAG_PANIC_ON_VIOLATION
    panic("acquiresleep: DAG violation");
#else
    return;  // Skip acquisition on violation (warning mode)
#endif
  }
#endif

  qspin_lock(&lk->lk);  // Acquire internal qspinlock

  while (lk->locked) {
    ksleep(lk, &lk->lk);  // Sleep, releasing internal lock
  }

  lk->locked = 1;
  lk->pid = myproc()->pid;

#ifdef USE_DAG_CHECKING
  // Track acquisition in DAG (Phase 6)
  dag_lock_acquired(lk, lk->name, lk->dag_level,
                   LOCK_TYPE_SLEEP, __FILE__, __LINE__);
#endif

  qspin_unlock(&lk->lk);  // Release internal qspinlock
}

void
releasesleep(struct sleeplock *lk)
{
  qspin_lock(&lk->lk);  // Acquire internal qspinlock

#ifdef USE_DAG_CHECKING
  // Track release in DAG (Phase 6)
  dag_lock_released(lk);
#endif

  lk->locked = 0;
  lk->pid = 0;
  wakeup(lk);  // Wake any sleeping threads

  qspin_unlock(&lk->lk);  // Release internal qspinlock
}

int
holdingsleep(struct sleeplock *lk)
{
  int r;

  qspin_lock(&lk->lk);
  r = lk->locked && (lk->pid == myproc()->pid);
  qspin_unlock(&lk->lk);
  return r;
}
