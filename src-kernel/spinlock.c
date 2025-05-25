// Mutual exclusion spin locks.

#include "types.h"
#include "defs.h"
#include "param.h"
#include "x86.h"
#include "memlayout.h"
#include "mmu.h"
#include "proc.h"
#include "spinlock.h"

#if CONFIG_SMP
void initlock(struct spinlock *lk, char *name) {
  lk->name = name;
  lk->ticket.head = 0;
  lk->ticket.tail = 0;
  lk->cpu = 0;
}

// Acquire the lock.
// Loops (spins) until the lock is acquired.
// Holding a lock for a long time may cause
// other CPUs to waste time spinning to acquire it.
void acquire(struct spinlock *lk) {
  pushcli(); // disable interrupts to avoid deadlock.
  if (holding(lk))
    panic("acquire");

  uint16_t ticket = __atomic_fetch_add(&lk->ticket.tail, 1, __ATOMIC_SEQ_CST);
  while (__atomic_load_n(&lk->ticket.head, __ATOMIC_SEQ_CST) != ticket)
    ;

  // Tell the C compiler and the processor to not move loads or stores
  // past this point, to ensure that the critical section's memory
  // references happen after the lock is acquired.
  __sync_synchronize();

  // Record info about lock acquisition for debugging.
  lk->cpu = mycpu();
  getcallerpcs(&lk, lk->pcs);
}

// Release the lock.
void release(struct spinlock *lk) {
  if (!holding(lk))
    panic("release");

  lk->pcs[0] = 0;
  lk->cpu = 0;

  // Tell the C compiler and the processor to not move loads or stores
  // past this point, to ensure that all the stores in the critical
  // section are visible to other cores before the lock is released.
  // Both the C compiler and the hardware may re-order loads and
  // stores; __sync_synchronize() tells them both not to.
  __sync_synchronize();

  __atomic_fetch_add(&lk->ticket.head, 1, __ATOMIC_SEQ_CST);

  popcli();
}
#else
void initlock(struct spinlock *lk, char *name) {
  (void)lk;
  (void)name;
}
void acquire(struct spinlock *lk) { (void)lk; }
void release(struct spinlock *lk) { (void)lk; }
#endif

// Record the current call stack in pcs[] by following the %ebp chain.
void getcallerpcs(void *v, uint pcs[]) {
#ifdef __x86_64__
  unsigned long *rbp;
  int i;

  rbp = (unsigned long *)v - 2;
  for (i = 0; i < 10; i++) {
    if (rbp == 0 || rbp < (unsigned long *)KERNBASE ||
        rbp == (unsigned long *)-1)
      break;
    pcs[i] = rbp[1];               // saved %rip
    rbp = (unsigned long *)rbp[0]; // saved %rbp
  }
  for (; i < 10; i++)
    pcs[i] = 0;
#else
  uint *ebp;
  int i;

  ebp = (uint *)v - 2;
  for (i = 0; i < 10; i++) {
    if (ebp == 0 || ebp < (uint *)KERNBASE || ebp == (uint *)0xffffffff)
      break;
    pcs[i] = ebp[1];      // saved %eip
    ebp = (uint *)ebp[0]; // saved %ebp
  }
  for (; i < 10; i++)
    pcs[i] = 0;
#endif
}

// Check whether this cpu is holding the lock.
#if CONFIG_SMP
int holding(struct spinlock *lock) {
  int r;
  pushcli();
  r = lock->cpu == mycpu();
  popcli();
  return r;
}
#else
int holding(struct spinlock *lock) {
  (void)lock;
  return 1;
}
#endif

// Pushcli/popcli are like cli/sti except that they are matched:
// it takes two popcli to undo two pushcli.  Also, if interrupts
// are off, then pushcli, popcli leaves them off.

void pushcli(void) {
  int eflags;

  eflags = readeflags();
  cli();
  if (mycpu()->ncli == 0)
    mycpu()->intena = eflags & FL_IF;
  mycpu()->ncli += 1;
}

void popcli(void) {
  if (readeflags() & FL_IF)
    panic("popcli - interruptible");
  if (--mycpu()->ncli < 0)
    panic("popcli");
  if (mycpu()->ncli == 0 && mycpu()->intena)
    sti();
}
