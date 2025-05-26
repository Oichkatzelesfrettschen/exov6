#include "qspinlock.h"
#include <stdint.h>
#include <compiler_attrs.h>
#if __has_include(<config.h>)
# include <config.h>
#endif

struct cpu;

extern struct cpu *mycpu(void);
extern void getcallerpcs(void *, unsigned int *);
extern void pushcli(void);
extern void popcli(void);
extern int holding(struct spinlock *);
extern void panic(char *);

#if CONFIG_SMP

static uint32_t lcg_rand(void) {
  static uint32_t seed = 123456789;
  seed = seed * 1103515245 + 12345;
  return seed;
}

void qspin_lock(struct spinlock *lk) {
  pushcli();
  if (holding(lk))
    panic("qspin_lock");

  uint16_t ticket = __atomic_fetch_add(&lk->ticket.tail, 1, __ATOMIC_SEQ_CST);
  while (__atomic_load_n(&lk->ticket.head, __ATOMIC_SEQ_CST) != ticket) {
    unsigned delay = (lcg_rand() & 0xff) + 1;
    while (delay--)
      __asm__ volatile("pause");
  }

  __sync_synchronize();
  lk->cpu = mycpu();
  getcallerpcs(&lk, lk->pcs);
}

void qspin_unlock(struct spinlock *lk) {
  if (!holding(lk))
    panic("qspin_unlock");
  lk->pcs[0] = 0;
  lk->cpu = 0;
  __sync_synchronize();
  __atomic_fetch_add(&lk->ticket.head, 1, __ATOMIC_SEQ_CST);
  popcli();
}

int qspin_trylock(struct spinlock *lk) {
  pushcli();
  if (holding(lk))
    panic("qspin_trylock");

  uint16_t head = __atomic_load_n(&lk->ticket.head, __ATOMIC_SEQ_CST);
  uint16_t tail = __atomic_load_n(&lk->ticket.tail, __ATOMIC_SEQ_CST);
  if (head != tail) {
    popcli();
    return 0;
  }
  uint16_t expected = tail;
  if (!__atomic_compare_exchange_n(&lk->ticket.tail, &expected, tail + 1, 0,
                                   __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST)) {
    popcli();
    return 0;
  }

  __sync_synchronize();
  lk->cpu = mycpu();
  getcallerpcs(&lk, lk->pcs);
  return 1;
}
#else
void qspin_lock(struct spinlock *lk) { (void)lk; }
void qspin_unlock(struct spinlock *lk) { (void)lk; }
int qspin_trylock(struct spinlock *lk) {
  (void)lk;
  return 1;
}
#endif
