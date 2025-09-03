#include <types.h>
#include "defs.h"
#include "mmu.h"
#include "proc.h"
#include "memlayout.h"
#include "exo_cpu.h"

int exo_yield_to(exo_cap target)
{
  if (target.pa == 0)
    return -1;
  if (!cap_verify(target))
    return -1;

  context_t *newctx = (context_t*)P2V(target.id);
  swtch(&myproc()->context, newctx);
  return 0;
}
