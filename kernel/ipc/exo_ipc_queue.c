#include "exo_ipc.h"
#include "defs.h"
#include "ipc.h"
#include "proc.h"
#include "spinlock.h"
#include <types.h>
#include <errno.h>
#include <string.h>
#include "ipc_debug.h"
#define EXO_KERNEL
#include "include/exokernel.h"
#include "ipc_queue.h"

struct mailbox ipcs;

static void ipc_init(struct mailbox *mb) {
  if (!mb->inited) {
    initlock(&mb->lock, "exoipc");
    mb->r = mb->w = 0;
    mb->inited = 1;
  }
}

void ipc_timed_init(void) { ipc_init(&ipcs); }

int exo_ipc_queue_send(exo_cap dest, const void *buf, uint64_t len) {
  struct mailbox *mb = myproc()->mailbox;
  ipc_init(mb);
  IPC_LOG("send attempt dest=%u len=%llu", dest.id, (unsigned long long)len);
  if (!cap_has_rights(dest.rights, EXO_RIGHT_W))
    {
      IPC_LOG("send fail: no write rights");
    return -EPERM;
    }
  if (len > sizeof(zipc_msg_t) + sizeof(exo_cap))
    len = sizeof(zipc_msg_t) + sizeof(exo_cap);

  zipc_msg_t m = {0};
  size_t mlen = len < sizeof(zipc_msg_t) ? len : sizeof(zipc_msg_t);
  memcpy(&m, buf, mlen);

  exo_cap fr = {0};
  if (len > sizeof(zipc_msg_t)) {
    memcpy(&fr, (const char *)buf + sizeof(zipc_msg_t), sizeof(exo_cap));
    if (!cap_verify(fr))
      {
        IPC_LOG("send fail: invalid frame cap");
      return -EPERM;
      }
    if (!cap_has_rights(fr.rights, EXO_RIGHT_R))
      {
        IPC_LOG("send fail: frame lacks read rights");
        return -EPERM;
      }
    if (dest.owner)
      fr.owner = dest.owner;
  }

  acquire(&mb->lock);
  while (mb->w - mb->r == MAILBOX_BUFSZ) {
    IPC_LOG("send waiting: mailbox full");
    wakeup(&mb->r);
    sleep(&mb->w, &mb->lock);
  }
  mb->buf[mb->w % MAILBOX_BUFSZ].msg = m;
  mb->buf[mb->w % MAILBOX_BUFSZ].frame = fr;
  mb->w++;
  wakeup(&mb->r);
  release(&mb->lock);

  IPC_LOG("send complete len=%llu", (unsigned long long)len);

  return (int)len;
}

int exo_ipc_queue_recv(exo_cap src, void *buf, uint64_t len) {
  IPC_LOG("recv attempt src=%u", src.id);
  if (!cap_has_rights(src.rights, EXO_RIGHT_R)) {
    IPC_LOG("recv fail: no read rights");
    return -EPERM;
  }
  struct mailbox *mb = myproc()->mailbox;
  ipc_init(mb);
  acquire(&mb->lock);
  while (mb->r == mb->w) {
    IPC_LOG("recv waiting: mailbox empty");
    wakeup(&mb->w);
    sleep(&mb->r, &mb->lock);
  }
  struct ipc_entry e = mb->buf[mb->r % MAILBOX_BUFSZ];
  mb->r++;
  wakeup(&mb->w);
  release(&mb->lock);

  if (e.frame.pa &&
      (!cap_verify(e.frame) || !cap_has_rights(e.frame.rights, EXO_RIGHT_R)))
    e.frame.pa = 0;

  size_t total = sizeof(zipc_msg_t);
  if (e.frame.id)
    total += sizeof(exo_cap);

  if (len > sizeof(zipc_msg_t))
    len = len < total ? len : total;
  else
    len = len < sizeof(zipc_msg_t) ? len : sizeof(zipc_msg_t);

  size_t cplen = len < sizeof(zipc_msg_t) ? len : sizeof(zipc_msg_t);
  memcpy(buf, &e.msg, cplen);
  if (cplen < len) {
    memcpy((char *)buf + sizeof(zipc_msg_t), &e.frame,
           len - sizeof(zipc_msg_t));
  }

  IPC_LOG("recv complete len=%llu", (unsigned long long)len);

  return (int)len;
}

int exo_ipc_queue_recv_timed(exo_cap src, void *buf, uint64_t len,
                             unsigned timeout) {
  IPC_LOG("recv_timed attempt src=%u to=%u", src.id, timeout);
  if (!cap_has_rights(src.rights, EXO_RIGHT_R)) {
    IPC_LOG("recv_timed fail: no read rights");
    return -EPERM;
  }
  ipc_init(&ipcs);
  acquire(&ipcs.lock);
  while (ipcs.r == ipcs.w && timeout > 0) {
    IPC_LOG("recv_timed waiting");
    wakeup(&ipcs.w);
    sleep(&ipcs.r, &ipcs.lock);
    timeout--;
  }
  if (ipcs.r == ipcs.w) {
    IPC_LOG("recv_timed timeout");
    release(&ipcs.lock);
    return -ETIMEDOUT;
  }
  struct ipc_entry e = ipcs.buf[ipcs.r % MAILBOX_BUFSZ];
  ipcs.r++;
  wakeup(&ipcs.w);
  release(&ipcs.lock);

  if (e.frame.pa &&
      (!cap_verify(e.frame) || !cap_has_rights(e.frame.rights, EXO_RIGHT_R)))
    e.frame.pa = 0;

  size_t total = sizeof(zipc_msg_t);
  if (e.frame.id)
    total += sizeof(exo_cap);

  if (len > sizeof(zipc_msg_t))
    len = len < total ? len : total;
  else
    len = len < sizeof(zipc_msg_t) ? len : sizeof(zipc_msg_t);

  size_t cplen = len < sizeof(zipc_msg_t) ? len : sizeof(zipc_msg_t);
  memcpy(buf, &e.msg, cplen);
  if (cplen < len)
    memcpy((char *)buf + sizeof(zipc_msg_t), &e.frame, len - sizeof(zipc_msg_t));

  IPC_LOG("recv_timed complete len=%llu", (unsigned long long)len);

  return (int)len;
}

struct exo_ipc_ops exo_ipc_queue_ops = {
    .send = exo_ipc_queue_send,
    .recv = exo_ipc_queue_recv,
};
