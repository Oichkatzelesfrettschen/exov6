#include "types.h"
#include "defs.h"
#include "spinlock.h"
#include "proc.h"
#include "kernel/exo_ipc.h"

#define IPC_BUFSZ 128

struct ipc_state {
  struct spinlock lock;
  char buf[IPC_BUFSZ];
  size_t r;
  size_t w;
  int inited;
};

static struct ipc_state ipcs;

static void
ipc_init(void)
{
  if(!ipcs.inited){
    initlock(&ipcs.lock, "exoipc");
    ipcs.r = ipcs.w = 0;
    ipcs.inited = 1;
  }
}

int
exo_send(exo_cap dest, const void *buf, uint64_t len)
{
  (void)dest;
  ipc_init();
  acquire(&ipcs.lock);
  for(size_t i = 0; i < len; i++){
    while(ipcs.w - ipcs.r == IPC_BUFSZ){
      wakeup(&ipcs.r);
      sleep(&ipcs.w, &ipcs.lock);
    }
    ipcs.buf[ipcs.w % IPC_BUFSZ] = ((const char*)buf)[i];
    ipcs.w++;
  }
  wakeup(&ipcs.r);
  release(&ipcs.lock);
  return (int)len;
}

int
exo_recv(exo_cap src, void *buf, uint64_t len)
{
  (void)src;
  ipc_init();
  acquire(&ipcs.lock);
  for(size_t i = 0; i < len; i++){
    while(ipcs.r == ipcs.w){
      wakeup(&ipcs.w);
      sleep(&ipcs.r, &ipcs.lock);
    }
    ((char*)buf)[i] = ipcs.buf[ipcs.r % IPC_BUFSZ];
    ipcs.r++;
  }
  wakeup(&ipcs.w);
  release(&ipcs.lock);
  return (int)len;
}
