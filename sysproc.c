#include "date.h"
#include "defs.h"
#include "memlayout.h"
#include "mmu.h"
#include "param.h"
#include "proc.h"
#include "types.h"
#include "x86.h"
#include "exo.h"


int sys_fork(void) { return fork(); }

int sys_exit(void) {
  exit();
  return 0; // not reached
}

int sys_wait(void) { return wait(); }

int sys_kill(void) {
  int pid;

  if (argint(0, &pid) < 0)
    return -1;
  return kill(pid);
}

int sys_getpid(void) { return myproc()->pid; }

int sys_sbrk(void) {
  int addr;
  int n;

  if (argint(0, &n) < 0)
    return -1;
  addr = myproc()->sz;
  if (growproc(n) < 0)
    return -1;
  return addr;
}

int sys_sleep(void) {
  int n;
  uint ticks0;

  if (argint(0, &n) < 0)
    return -1;
  acquire(&tickslock);
  ticks0 = ticks;
  while (ticks - ticks0 < n) {
    if (myproc()->killed) {
      release(&tickslock);
      return -1;
    }
    sleep(&ticks, &tickslock);
  }
  release(&tickslock);
  return 0;
}

// return how many clock tick interrupts have occurred
// since start.
int sys_uptime(void) {
  uint xticks;

  acquire(&tickslock);
  xticks = ticks;
  release(&tickslock);
  return xticks;
}


int sys_set_timer_upcall(void) {
  void (*handler)(void);
  if (argptr(0, (char **)&handler, sizeof(handler)) < 0)
    return -1;
  myproc()->timer_upcall = handler;
  return 0;

// allocate a physical page and return its capability
int
sys_exo_alloc_page(void)
{
  exo_cap cap = exo_alloc_page();
  return cap.pa;
}

// unbind and free a physical page by capability
int
sys_exo_unbind_page(void)
{
  exo_cap cap;
  if(argint(0, (int*)&cap.pa) < 0)
    return -1;
  return exo_unbind_page(cap);

}
