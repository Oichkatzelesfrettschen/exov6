#include "kernel/exo_cpu.h"
#include "defs.h"

int __attribute__((weak)) exo_yield_to(exo_cap target) {
  // TODO: implement context switch to the capability
  (void)target;
  return -1;
}
