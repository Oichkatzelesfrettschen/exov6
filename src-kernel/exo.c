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

// Stubs for capability syscalls. Real implementations may reside in
// platform-specific code, but we provide simple versions so that the
// kernel links successfully.
int
exo_yield_to(exo_cap target)
{
  (void)target;
  return -1;
}

int
exo_read_disk(exo_cap cap, void *dst, uint64_t off, uint64_t n)
{
  (void)cap;
  (void)dst;
  (void)off;
  (void)n;
  return -1;
}

int
exo_write_disk(exo_cap cap, const void *src, uint64_t off, uint64_t n)
{
  (void)cap;
  (void)src;
  (void)off;
  (void)n;
  return -1;
}
