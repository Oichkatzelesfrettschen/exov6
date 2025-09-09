#include "defs.h"
#include "proc.h"
#include "spinlock.h"
#include "cap.h"
#include "errno.h"

/* Ensure ENOSPC is defined */
#ifndef ENOSPC
#define ENOSPC 28
#endif

#define EXO_KERNEL
#include "exokernel.h"

#define IRQ_BUFSZ 32

struct irq_queue {
  struct spinlock lock;
  uint32_t buf[IRQ_BUFSZ];
  uint32_t r;
  uint32_t w;
  int inited;
} irq_q;

static void irq_init(void) {
  if (!irq_q.inited) {
    initlock(&irq_q.lock, "irqq");
    irq_q.r = irq_q.w = 0;
    irq_q.inited = 1;
  }
}

exo_cap exo_alloc_irq(uint32_t irq, uint32_t rights) {
  int id = cap_table_alloc(CAP_TYPE_IRQ, irq, rights, myproc()->pid);
  if (id < 0)
    return cap_new(0, 0, 0);
  return cap_new(id, rights, myproc()->pid);
}

static int check_irq_cap(exo_cap cap, uint32_t need) {
  if (!cap_verify(cap))
    return 0;
  struct cap_entry e;
  if (cap_table_lookup(cap.id, &e) < 0)
    return 0;
  if (e.type != CAP_TYPE_IRQ || e.owner != myproc()->pid)
    return 0;
  if (!cap_has_rights(e.rights, need))
    return 0;
  return 1;
}

[[nodiscard]] int exo_irq_wait(exo_cap cap, uint32_t *irq_out) {
  if (!check_irq_cap(cap, EXO_RIGHT_R))
    return -EPERM;
  irq_init();
  acquire(&irq_q.lock);
  while (irq_q.r == irq_q.w) {
    wakeup(&irq_q.w);
    sleep(&irq_q.r, &irq_q.lock);
  }
  uint32_t irq = irq_q.buf[irq_q.r % IRQ_BUFSZ];
  irq_q.r++;
  wakeup(&irq_q.w);
  release(&irq_q.lock);
  if (irq_out)
    *irq_out = irq;
  return 0;
}

[[nodiscard]] int exo_irq_ack(exo_cap cap) {
  if (!check_irq_cap(cap, EXO_RIGHT_W))
    return -EPERM;
  // Acknowledge the interrupt at the hardware level
  lapiceoi();
  return 0;
}

int irq_trigger(uint32_t irq) {
  irq_init();
  acquire(&irq_q.lock);
  int ret = 0;
  if (irq_q.w - irq_q.r < IRQ_BUFSZ) {
    irq_q.buf[irq_q.w % IRQ_BUFSZ] = irq;
    irq_q.w++;
    wakeup(&irq_q.r);
    ret = 0;
  } else {
    ret = -ENOSPC;
  }
  release(&irq_q.lock);
  return ret;
}
