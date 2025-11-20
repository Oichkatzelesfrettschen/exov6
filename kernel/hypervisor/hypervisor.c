/**
 * @file hypervisor.c
 * @brief Minimal hypervisor capability stubs.
 */

#include <types.h>
#include "defs.h"
#include "cap.h"
#define EXO_KERNEL
/* exo.h included via defs.h/proc.h (kernel API, not userspace exokernel.h) */
#include <errno.h>

/** Allocate a Hypervisor capability (stub). */
exo_cap exo_alloc_hypervisor(void)
{
  int id = cap_table_alloc(CAP_TYPE_HYPERVISOR, 0, 0, myproc()->pid);
  return (id < 0) ? cap_new(0, 0, 0) : cap_new((uint32_t)id, 0, myproc()->pid);
}

/** Launch a guest using a Hypervisor capability (not implemented). */
int hv_launch_guest(exo_cap cap, const char *path)
{
  cprintf("hv_launch_guest: stub. Cap ID=%u, path=%s\n", cap.id, path ? path : "(null)");
  return -ENOSYS;
}
