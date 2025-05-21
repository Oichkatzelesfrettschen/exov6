#include "types.h"
#include "defs.h"
#include "proc.h"
#include "kernel/exo_ipc.h"
#include "spinlock.h"

// Shared IPC frame allocated at boot
char *exo_ipc_frame;
static uint64_t exo_ipc_len;

int exo_send(exo_cap dest, const void *buf, uint64_t len) {
  struct ipc_endpoint *ep = (struct ipc_endpoint*)P2V(dest.pa);
  struct proc *p;

  acquire(&ptable.lock);
  p = ep->waiting;
  if(p == 0){
    release(&ptable.lock);
    return -1;
  }
  ep->waiting = 0;
  release(&ptable.lock);

  if(len > 4*sizeof(uintptr_t))
    memmove(exo_ipc_frame, buf, len);
  else
    memmove(exo_ipc_frame, buf, len);

  exo_ipc_len = len;
  wakeup(p);
  return 0;
}

int exo_recv(exo_cap src, void *buf, uint64_t len) {
  struct ipc_endpoint *ep = (struct ipc_endpoint*)P2V(src.pa);
  struct proc *p = myproc();

  acquire(&ptable.lock);
  ep->waiting = p;
  sleep(ep, &ptable.lock);
  release(&ptable.lock);

  if(len > exo_ipc_len)
    len = exo_ipc_len;
  memmove(buf, exo_ipc_frame, len);
  return len;
}
