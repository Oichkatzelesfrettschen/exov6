#include "rspinlock.h"
#include <compiler_attrs.h>
#if __has_include(<config.h>)
# include <config.h>
#endif

struct cpu;

extern struct cpu *mycpu(void);
extern void pushcli(void);
extern void popcli(void);
extern void acquire(struct spinlock *);
extern void release(struct spinlock *);
extern int holding(struct spinlock *);
extern void panic(char *);

#if CONFIG_SMP

void rinitlock(struct rspinlock *rlk, char *name) {
  rlk->owner = 0;
  rlk->depth = 0;
  initlock(&rlk->lk, name);
}

void racquire(struct rspinlock *rlk) {
  pushcli();
  if (rlk->owner == mycpu()) {
    rlk->depth++;
    return;
  }
  acquire(&rlk->lk);
  rlk->owner = mycpu();
  rlk->depth = 1;
}

void rrelease(struct rspinlock *rlk) {
  if (rlk->owner != mycpu() || rlk->depth < 1)
    panic("rrelease");
  rlk->depth--;
  if (rlk->depth == 0) {
    rlk->owner = 0;
    release(&rlk->lk);
  }
  popcli();
}

int rholding(struct rspinlock *rlk) {
  int r;
  pushcli();
  r = (rlk->owner == mycpu());
  popcli();
  return r;
}
#else
void rinitlock(struct rspinlock *rlk, char *name) {
  (void)rlk;
  (void)name;
}
void racquire(struct rspinlock *rlk) { (void)rlk; }
void rrelease(struct rspinlock *rlk) { (void)rlk; }
int rholding(struct rspinlock *rlk) {
  (void)rlk;
  return 1;
}
#endif
