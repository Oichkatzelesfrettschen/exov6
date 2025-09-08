/**
 * @file    exo.c
 * @brief   Exokernel utility stubs and pctr transfer.
 */

#include "defs.h"
#include "exo_cpu.h"
#include "exo_disk.h"
#include "exo_ipc.h"
#include "mmu.h"
#include "param.h"
#include "proc.h"
#include "spinlock.h"
#include <types.h>
#include "arch.h"
#include "trapframe.h"

extern struct ptable ptable;
void exo_pctr_transfer(struct trapframe *tf) {
#ifdef __x86_64__
  uint32_t cap = tf->rax;
#else
  uint32_t cap = tf->eax;
#endif
  struct proc *p;

  acquire(&ptable.lock);
  p = pctr_lookup(cap);
  if (p && p->state != UNUSED)
    p->pctr_signal++;
  release(&ptable.lock);
}
/**
 * Stub syscalls: provide minimal implementations so the kernel links.
 */
int exo_yield_to(exo_cap target) { (void)target; return -1; }
int exo_read_disk(struct exo_blockcap cap, void *dst, uint64_t off, uint64_t n)
{ (void)cap.dev; (void)dst; (void)off; (void)n; return -1; }
int exo_write_disk(struct exo_blockcap cap, const void *src, uint64_t off, uint64_t n)
{ (void)cap.dev; (void)src; (void)off; (void)n; return -1; }
