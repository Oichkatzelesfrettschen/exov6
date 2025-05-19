#include "defs.h"
#include "date.h"
#include "memlayout.h"
#include "mmu.h"
#include "param.h"
#include "proc.h"
#include "types.h"
#include "x86.h"
#include "exo.h"
#include "fs.h"
#include "spinlock.h"
#include "sleeplock.h"
#include "buf.h"


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

int
sys_mappte(void)
{
  int va, pa, perm;

  if (argint(0, &va) < 0 || argint(1, &pa) < 0 || argint(2, &perm) < 0)
    return -1;
  return insert_pte(myproc()->pgdir, (void *)va, pa, perm);
}

int sys_set_timer_upcall(void) {
  void (*handler)(void);
  if (argptr(0, (char **)&handler, sizeof(handler)) < 0)
    return -1;
  myproc()->timer_upcall = handler;
  return 0;
}

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

int sys_exo_alloc_block(void) {
  int dev;
  struct exo_blockcap *ucap;
  struct exo_blockcap cap;
  if (argint(0, &dev) < 0 || argptr(1, (void *)&ucap, sizeof(*ucap)) < 0)
    return -1;
  cap = exo_alloc_block(dev);
  ucap->dev = cap.dev;
  ucap->blockno = cap.blockno;
  return 0;
}

int sys_exo_bind_block(void) {
  struct exo_blockcap *ucap, cap;
  char *data;
  int write;
  struct buf b;

  if (argptr(0, (void *)&ucap, sizeof(cap)) < 0 ||
      argptr(1, &data, BSIZE) < 0 || argint(2, &write) < 0)
    return -1;

  cap = *ucap;
  memset(&b, 0, sizeof(b));
  initsleeplock(&b.lock, "exoblk");
  acquiresleep(&b.lock);
  if (write)
    memmove(b.data, data, BSIZE);
  exo_bind_block(&cap, &b, write);
  if (!write)
    memmove(data, b.data, BSIZE);
  releasesleep(&b.lock);
  return 0;
}

int sys_exo_yield_to(void) {
  exo_cap cap;
  if (argint(0, (int *)&cap.pa) < 0)
    return -1;
  return exo_yield_to(cap);
}

int sys_exo_read_disk(void) {
  exo_cap cap;
  char *dst;
  uint off, n;
  if (argint(0, (int *)&cap.pa) < 0 ||
      argint(2, (int *)&off) < 0 ||
      argint(3, (int *)&n) < 0 ||
      argptr(1, &dst, n) < 0)
    return -1;
  return exo_read_disk(cap, dst, off, n);
}

int sys_exo_write_disk(void) {
  exo_cap cap;
  char *src;
  uint off, n;
  if (argint(0, (int *)&cap.pa) < 0 ||
      argint(2, (int *)&off) < 0 ||
      argint(3, (int *)&n) < 0 ||
      argptr(1, &src, n) < 0)
    return -1;
  return exo_write_disk(cap, src, off, n);
}
