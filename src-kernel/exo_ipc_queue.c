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

static struct proc *lookup_pid(int pid) {
  struct proc *p;
  acquire(&ptable.lock);
  for (p = ptable.proc; p < &ptable.proc[NPROC]; p++) {
    if (p->pid == pid && p->state != UNUSED) {
      release(&ptable.lock);
      return p;
    }
  }
  release(&ptable.lock);
  return 0;
}

static void mbox_init(struct exo_mailbox *mb) {
  initlock(&mb->lock, "mbox");
  mb->r = mb->w = 0;
}

static void mbox_enqueue(struct exo_mailbox *mb, struct ipc_entry *e) {
  acquire(&mb->lock);
  while (mb->w - mb->r == IPC_BUFSZ) {
    wakeup(&mb->r);
    sleep(&mb->w, &mb->lock);
  }
  mb->buf[mb->w % IPC_BUFSZ] = *e;
  mb->w++;
  wakeup(&mb->r);
  release(&mb->lock);
}

static void mbox_dequeue(struct exo_mailbox *mb, struct ipc_entry *out) {
  acquire(&mb->lock);
  while (mb->r == mb->w) {
    wakeup(&mb->w);
    sleep(&mb->r, &mb->lock);
  }
  *out = mb->buf[mb->r % IPC_BUFSZ];
  mb->r++;
  wakeup(&mb->w);
  release(&mb->lock);
}

int exo_ipc_queue_send(exo_cap dest, const void *buf, uint64_t len) {
  if(!cap_has_rights(dest.rights, EXO_RIGHT_W))
    return -EPERM;
  struct proc *p = lookup_pid(dest.owner);
  if (!p)
    return -EINVAL;
  struct exo_mailbox *mb = &p->mbox;
  if (mb->r == 0 && mb->w == 0) // uninitialized check
    mbox_init(mb);
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

  struct ipc_entry e = { .msg = m, .frame = fr };
  mbox_enqueue(mb, &e);

  return (int)len;
}

int exo_ipc_queue_recv(exo_cap src, void *buf, uint64_t len) {
  if(!cap_has_rights(src.rights, EXO_RIGHT_R))
    return -EPERM;
  struct proc *p = lookup_pid(src.owner);
  if (!p)
    return -EINVAL;
  struct exo_mailbox *mb = &p->mbox;
  if (mb->r == 0 && mb->w == 0)
    mbox_init(mb);
  struct ipc_entry e;
  mbox_dequeue(mb, &e);

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
