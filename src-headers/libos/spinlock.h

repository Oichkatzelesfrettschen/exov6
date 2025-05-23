#pragma once


struct ticketlock {
  _Atomic unsigned short head;
  _Atomic unsigned short tail;
};
struct spinlock { struct ticketlock ticket; };
static inline void initlock(struct spinlock *l, const char *name) { (void)l; (void)name; }
static inline void acquire(struct spinlock *l) { (void)l; }
static inline void release(struct spinlock *l) { (void)l; }
