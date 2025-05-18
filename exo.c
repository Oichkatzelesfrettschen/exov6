#include "defs.h"
#include "param.h"
#include "proc.h"
#include "spinlock.h"
#include "types.h"
#include "x86.h"

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
