#pragma once
#ifndef CONFIG_SMP
#define CONFIG_SMP 1
#endif

#include <stddef.h>
#include <stdint.h>

struct spinlock; // forward declaration for prototypes below
#if defined(SPINLOCK_NO_STUBS) && !defined(USE_TICKET_LOCK)
void qspin_lock(struct spinlock *lk);
void qspin_unlock(struct spinlock *lk);
#endif

struct ticketlock {
  _Atomic unsigned short head;
  _Atomic unsigned short tail;
};

struct cpu; // forward declaration

struct spinlock {
  struct ticketlock ticket;
  char *name;
  struct cpu *cpu;
  uint32_t pcs[10];
};

#if defined(SPINLOCK_NO_STUBS) && CONFIG_SMP && !defined(SPINLOCK_UNIPROCESSOR)

static inline void initlock(struct spinlock *lk, const char *name) {
  lk->name = (char *)name;
  lk->ticket.head = 0;
  lk->ticket.tail = 0;
  lk->cpu = 0;
}

static inline void acquire(struct spinlock *lk) {
#ifdef USE_TICKET_LOCK
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
#else
  qspin_lock(lk);
#endif
}

static inline void release(struct spinlock *lk) {
#ifdef USE_TICKET_LOCK
  if (!holding(lk))
    panic("release");

  lk->pcs[0] = 0;
  lk->cpu = 0;
  __sync_synchronize();
  __atomic_fetch_add(&lk->ticket.head, 1, __ATOMIC_SEQ_CST);
  popcli();
#else
  qspin_unlock(lk);
#endif
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
