#include "types.h"
#include "defs.h"
#include "param.h"
#if defined(__aarch64__)
#include "aarch64.h"
#else
#include "x86.h"
#endif
#include "spinlock.h"
#include "qspinlock.h"

#if defined(__x86_64__) || defined(__i386__)
#include <x86intrin.h>
#endif

static inline uint32_t rand32(void) {
#if defined(__x86_64__) || defined(__i386__)
  unsigned int r;
  if (__builtin_ia32_rdrand32_step(&r))
    return r;
#endif
  static uint32_t seed = 2463534242U;
  seed = seed * 1103515245 + 12345;
  return seed;
}

void qspin_lock(struct spinlock *lk) {
  pushcli();
  if (holding(lk))
    panic("qspin_lock");

  uint16_t ticket = __atomic_fetch_add(&lk->ticket.tail, 1, __ATOMIC_SEQ_CST);
  while (__atomic_load_n(&lk->ticket.head, __ATOMIC_SEQ_CST) != ticket) {
    uint32_t delay = rand32() & 0xff;
    while (delay--)
      cpu_relax();
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
  uint16_t expected = head;
  if (!__atomic_compare_exchange_n(&lk->ticket.tail, &expected, head + 1, false,
                                   __ATOMIC_SEQ_CST, __ATOMIC_RELAXED)) {
    popcli();
    return 0;
  }
  __sync_synchronize();
  lk->cpu = mycpu();
  getcallerpcs(&lk, lk->pcs);
  return 1;
}
