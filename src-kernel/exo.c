#include "defs.h"
#include "kernel/exo_cpu.h"
#include "kernel/exo_disk.h"
#include "kernel/exo_ipc.h"
#include "mmu.h"
#include "param.h"
#include "mmu.h"
#include "proc.h"
#include "spinlock.h"
#include "types.h"
#include "x86.h"

extern struct ptable ptable;

void exo_pctr_transfer(struct trapframe *tf) {
  uint cap = tf->eax;
  struct proc *p;

  acquire(&ptable.lock);
  p = pctr_lookup(cap);
  if (p && p->state != UNUSED)
    p->pctr_signal++;
  release(&ptable.lock);
}

