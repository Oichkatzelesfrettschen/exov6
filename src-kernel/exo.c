#include "defs.h"
#include "exo_cpu.h"
#include "exo_disk.h"
#include "exo_ipc.h"
#include "mmu.h"
#include "param.h"
#include "proc.h"
#include "spinlock.h"
#include "types.h"
#include "x86.h"

extern struct ptable ptable;

void exo_pctr_transfer(struct trapframe *tf) {
  uint32_t cap = tf->eax;
  struct proc *p;

  acquire(&ptable.lock);
  p = pctr_lookup(cap);
  if (p && p->state != UNUSED)
    p->pctr_signal++;
  release(&ptable.lock);
}
