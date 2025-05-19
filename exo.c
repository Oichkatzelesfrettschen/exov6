#include "defs.h"
#include "mmu.h"
#include "param.h"
#include "proc.h"
#include "spinlock.h"
#include "types.h"
#include "x86.h"

extern struct ptable ptable;

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

// Stubs for capability syscalls. Real implementations may reside in
// platform-specific code, but we provide simple versions so that the
// kernel links successfully.
int __attribute__((weak)) exo_yield_to(exo_cap target) {
  (void)target;
  return -1;
}

int __attribute__((weak)) exo_read_disk(exo_blockcap cap, void *dst,
                                        uint64_t off, uint64_t n) {
  (void)cap;
  (void)dst;
  (void)off;
  (void)n;
  return -1;
}

int __attribute__((weak)) exo_write_disk(exo_blockcap cap, const void *src,
                                         uint64_t off, uint64_t n) {
  (void)cap;
  (void)src;
  (void)off;
  (void)n;
  return -1;
}
