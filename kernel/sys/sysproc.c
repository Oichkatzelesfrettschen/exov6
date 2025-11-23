#include <types.h>
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "proc.h"

// Exokernel Purge: Removed high-level process management

int sys_exit(void) {
  int status;
  if (argint(0, &status) < 0)
    status = 0;
  exit(status);
  return 0; // not reached
}

// Keep wait for now, though it might need adjustment for Env model
int sys_wait(void) { return wait(); }

int sys_getpid(void) { return myproc()->pid; }

// sys_fork: GONE
// sys_sbrk: GONE
// sys_sleep: GONE
// sys_kill: GONE

int sys_uptime(void) {
  uint xticks;
  // TODO: Lock tickslock if needed, but it's external
  // For now just return ticks
  extern uint ticks;
  return ticks;
}

// Old exo stubs removed. See sys_exo.c
