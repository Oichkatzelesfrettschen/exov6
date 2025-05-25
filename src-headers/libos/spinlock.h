#pragma once


#include <stddef.h>
#include <smp_lock.h>

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

#if CONFIG_SMP
void initlock(struct spinlock *l, const char *name);
void acquire(struct spinlock *l);
void release(struct spinlock *l);
#else
static inline void initlock(struct spinlock *l, const char *name) { (void)l; (void)name; }
static inline void acquire(struct spinlock *l) { (void)l; }
static inline void release(struct spinlock *l) { (void)l; }
#endif
static inline size_t spinlock_optimal_alignment(void) { return __alignof__(struct spinlock); }
