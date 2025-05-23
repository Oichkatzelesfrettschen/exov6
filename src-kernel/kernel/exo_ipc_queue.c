#include "exo_ipc.h"
#include "defs.h"
#include "ipc.h"
#include "proc.h"
#include "spinlock.h"
#include "types.h"
#include <errno.h>
#define EXO_KERNEL
#include "include/exokernel.h"

#define IPC_BUFSZ 64

struct ipc_entry {
  zipc_msg_t msg;
  exo_cap frame;
};

static struct {
  struct spinlock lock;
  struct ipc_entry buf[IPC_BUFSZ];
  uint r;
  uint w;
  int inited;
} ipcs;

static void ipc_init(void) {
  if (!ipcs.inited) {
    initlock(&ipcs.lock, "exoipc");
    ipcs.r = ipcs.w = 0;
    ipcs.inited = 1;
  }
}

int exo_ipc_queue_send(exo_cap dest, const void *buf, uint64_t len) {
  ipc_init();
  if(!cap_has_rights(dest.rights, EXO_RIGHT_W))
    return -EPERM;
  if (len > sizeof(zipc_msg_t) + sizeof(exo_cap))
    len = sizeof(zipc_msg_t) + sizeof(exo_cap);

  zipc_msg_t m = {0};
  size_t mlen = len < sizeof(zipc_msg_t) ? len : sizeof(zipc_msg_t);
  memmove(&m, buf, mlen);

  exo_cap fr = {0};
  if (len > sizeof(zipc_msg_t)) {
    memmove(&fr, (const char *)buf + sizeof(zipc_msg_t), sizeof(exo_cap));
    if (!cap_verify(fr))
      return -EPERM;
    if(!cap_has_rights(fr.rights, EXO_RIGHT_R))
      return -EPERM;
    if (dest.owner)
      fr.owner = dest.owner;
  }

  acquire(&ipcs.lock);
  while (ipcs.w - ipcs.r == IPC_BUFSZ) {
    wakeup(&ipcs.r);
    sleep(&ipcs.w, &ipcs.lock);
  }
  ipcs.buf[ipcs.w % IPC_BUFSZ].msg = m;
  ipcs.buf[ipcs.w % IPC_BUFSZ].frame = fr;
  ipcs.w++;
  wakeup(&ipcs.r);
  release(&ipcs.lock);

  return (int)len;
}

int exo_ipc_queue_recv(exo_cap src, void *buf, uint64_t len) {
  if(!cap_has_rights(src.rights, EXO_RIGHT_R))
    return -EPERM;
  ipc_init();
  acquire(&ipcs.lock);
  while (ipcs.r == ipcs.w) {
    wakeup(&ipcs.w);
    sleep(&ipcs.r, &ipcs.lock);
  }
  struct ipc_entry e = ipcs.buf[ipcs.r % IPC_BUFSZ];
  ipcs.r++;
  wakeup(&ipcs.w);
  release(&ipcs.lock);

  if (e.frame.pa && (!cap_verify(e.frame) ||
                     !cap_has_rights(e.frame.rights, EXO_RIGHT_R)))
    e.frame.pa = 0;

  size_t total = sizeof(zipc_msg_t);
  if (e.frame.id)
    total += sizeof(exo_cap);

  if (len > sizeof(zipc_msg_t))
    len = len < total ? len : total;
  else
    len = len < sizeof(zipc_msg_t) ? len : sizeof(zipc_msg_t);

  size_t cplen = len < sizeof(zipc_msg_t) ? len : sizeof(zipc_msg_t);
  memmove(buf, &e.msg, cplen);
  if (cplen < len) {
    memmove((char *)buf + sizeof(zipc_msg_t), &e.frame,
            len - sizeof(zipc_msg_t));
  }

  return (int)len;
}

struct exo_ipc_ops exo_ipc_queue_ops = {
  .send = exo_ipc_queue_send,
  .recv = exo_ipc_queue_recv,
};
