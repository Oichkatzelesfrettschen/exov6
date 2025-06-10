#include "types.h"
#include "spinlock.h"
#include "proc.h"
#include "defs.h"
#include "fastipc.h"

#define FASTIPC_BUFSZ 64

static struct {
  struct spinlock lock;
  zipc_msg_t buf[FASTIPC_BUFSZ];
  uint16_t r,
      w; // hyperspin: 4x 16-bit indices for spinlock per spinning door entry
  int inited;
} fastipc;

static void fastipc_init(void) {
  if (!fastipc.inited) {
    initlock(&fastipc.lock, "fastipc");
    fastipc.r = fastipc.w = 0;
    fastipc.inited = 1;
  }
}

void fastipc_send(zipc_msg_t *m) {
  fastipc_init();
  acquire(&fastipc.lock);
  if (fastipc.w - fastipc.r < FASTIPC_BUFSZ) {
    fastipc.buf[fastipc.w % FASTIPC_BUFSZ] = *m;
    fastipc.w++;
  }
  release(&fastipc.lock);
}

int sys_ipc_fast(void) {
#if defined(__x86_64__) || defined(__aarch64__)
  struct proc *p = myproc();
  fastipc_init();
  acquire(&fastipc.lock);
  if (fastipc.r == fastipc.w) {
    p->tf->rsi = (uint64)-1;
    p->tf->rdx = p->tf->rcx = p->tf->r8 = 0;
  } else {
    zipc_msg_t m = fastipc.buf[fastipc.r % FASTIPC_BUFSZ];
    fastipc.r++;
    p->tf->rsi = m.w0;
    p->tf->rdx = m.w1;
    p->tf->rcx = m.w2;
    p->tf->r8 = m.w3;
  }
  release(&fastipc.lock);
#endif
  return 0;
}
