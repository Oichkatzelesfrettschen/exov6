#pragma once

#include <stddef.h>

struct ticketlock {
  _Atomic unsigned short head;
  _Atomic unsigned short tail;
};

struct cpu; // forward declaration

struct spinlock {
  struct ticketlock ticket;
  char *name;
  struct cpu *cpu;
  unsigned int pcs[10];
};

#ifdef SPINLOCK_NO_STUBS

static inline void initlock(struct spinlock *lk, const char *name) {
  lk->name = (char *)name;
  lk->ticket.head = 0;
  lk->ticket.tail = 0;
  lk->cpu = 0;
}

static inline void acquire(struct spinlock *lk) {
  pushcli();
  if (holding(lk))
    panic("acquire");

  unsigned short ticket =
      __atomic_fetch_add(&lk->ticket.tail, 1, __ATOMIC_SEQ_CST);
  while (__atomic_load_n(&lk->ticket.head, __ATOMIC_SEQ_CST) != ticket)
    ;

  __sync_synchronize();
  lk->cpu = mycpu();
  getcallerpcs(&lk, lk->pcs);
}

static inline void release(struct spinlock *lk) {
  if (!holding(lk))
    panic("release");

  lk->pcs[0] = 0;
  lk->cpu = 0;
  __sync_synchronize();
  __atomic_fetch_add(&lk->ticket.head, 1, __ATOMIC_SEQ_CST);
  popcli();
}

#else
static inline void initlock(struct spinlock *l, const char *name) {
  (void)l;
  (void)name;
}
static inline void acquire(struct spinlock *l) { (void)l; }
static inline void release(struct spinlock *l) { (void)l; }
#endif

static inline size_t spinlock_optimal_alignment(void) {
  return __alignof__(struct spinlock);
}
