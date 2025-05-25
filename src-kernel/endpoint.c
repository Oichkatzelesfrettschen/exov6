#include "types.h"
#include "spinlock.h"
#include "proc.h"
#include "defs.h"
#include "endpoint.h"

static struct endpoint global_ep;

void endpoint_init(struct endpoint *ep) {
  if (!ep->inited) {
    initlock(&ep->lock, "endpoint");
    ep->r = ep->w = 0;
    ep->inited = 1;
    ep->desc = 0;
  }
}

void endpoint_config(struct endpoint *ep, zipc_msg_t *buf, uint size,
                     const struct msg_type_desc *desc) {
  endpoint_init(ep);
  acquire(&ep->lock);
  ep->q = buf;
  ep->size = size;
  ep->desc = desc;
  ep->r = ep->w = 0;
  release(&ep->lock);
}

void endpoint_send(struct endpoint *ep, zipc_msg_t *m) {
  endpoint_init(ep);
  acquire(&ep->lock);
  if (ep->q && ep->size && ep->w - ep->r < ep->size) {
    size_t sz = msg_desc_size(ep->desc);
    const uchar *p = (const uchar *)m;
    for (size_t i = sz; i < sizeof(zipc_msg_t); i++)
      if (p[i]) {
        release(&ep->lock);
        return;
      }
    zipc_msg_t tmp = {0};
    memmove(&tmp, m, sz);
    ep->q[ep->w % ep->size] = tmp;
    ep->w++;
    wakeup(&ep->r);
  }
  release(&ep->lock);
}

[[nodiscard]] int endpoint_recv(struct endpoint *ep, zipc_msg_t *m) {
  endpoint_init(ep);
  acquire(&ep->lock);
  while (ep->q && ep->r == ep->w) {
    sleep(&ep->r, &ep->lock);
  }
  if (!ep->q) {
    release(&ep->lock);
    return -1;
  }
  zipc_msg_t t = ep->q[ep->r % ep->size];
  ep->r++;
  size_t sz = msg_desc_size(ep->desc);
  memmove(m, &t, sz);
  memset((char *)m + sz, 0, sizeof(zipc_msg_t) - sz);
  release(&ep->lock);
  return 0;
}

int sys_endpoint_send(void) {
  zipc_msg_t *umsg;
  if (argptr(0, (void *)&umsg, sizeof(*umsg)) < 0)
    return -1;
  endpoint_send(&global_ep, umsg);
  return 0;
}

int sys_endpoint_recv(void) {
  zipc_msg_t *udst;
  zipc_msg_t m;
  if (argptr(0, (void *)&udst, sizeof(*udst)) < 0)
    return -1;
  endpoint_recv(&global_ep, &m);
  memmove(udst, &m, sizeof(m));
  return 0;
}
