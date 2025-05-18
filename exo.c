#include "defs.h"
#include "param.h"
#include "spinlock.h"
#include "proc.h"
#include "types.h"
#include "x86.h"

extern struct {
  struct spinlock lock;
  struct proc proc[NPROC];
} ptable;

void exo_pctr_transfer(struct trapframe *tf) {
  uint cap = tf->eax;
  struct proc *p;

  acquire(&ptable.lock);
  for (p = ptable.proc; p < &ptable.proc[NPROC]; p++) {
    if (p->state != UNUSED && p->pctr_cap == cap) {
      p->pctr_signal++;
      break;
    }
  }
  release(&ptable.lock);
}

int exo_yield_to(exo_cap target) {
  // For now, ignore the target capability and yield to the scheduler.
  yield();
  return 0;
}
