#include "types.h"
#include "defs.h"
#include "spinlock.h"
#include "rspinlock.h"

void
rinitlock(struct rspinlock *rlk, char *name)
{
  initlock(&rlk->lk, name);
  rlk->owner = 0;
  rlk->depth = 0;
}

void
racquire(struct rspinlock *rlk)
{
  pushcli();
  if(rlk->owner == mycpu()){
    rlk->depth++;
    return;
  }
  acquire(&rlk->lk);
  rlk->owner = mycpu();
  rlk->depth = 1;
}

void
rrelease(struct rspinlock *rlk)
{
  if(rlk->owner != mycpu() || rlk->depth == 0)
    panic("rrelease");
  if(--rlk->depth == 0){
    rlk->owner = 0;
    release(&rlk->lk);
  }
  popcli();
}

int
rholding(struct rspinlock *rlk)
{
  pushcli();
  int r = rlk->owner == mycpu();
  popcli();
  return r;
}
