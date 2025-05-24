#pragma once
#include "../spinlock.h"

struct rspinlock {
  struct spinlock lk;  // underlying spinlock
  struct cpu *owner;   // current owner CPU
  int depth;           // recursion depth
};

void rinitlock(struct rspinlock *rlk, char *name);
void racquire(struct rspinlock *rlk);
void rrelease(struct rspinlock *rlk);
int rholding(struct rspinlock *rlk);

#define WITH_RSPINLOCK(rlk) \
  for(int _once = (racquire(rlk), 0); !_once; rrelease(rlk), _once = 1)
