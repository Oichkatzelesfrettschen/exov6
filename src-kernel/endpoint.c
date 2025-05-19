#include "types.h"
#include "spinlock.h"
#include "proc.h"
#include "defs.h"
#include "endpoint.h"

static struct endpoint global_ep;

void
endpoint_init(struct endpoint *ep)
{
    if(!ep->inited){
        initlock(&ep->lock, "endpoint");
        ep->r = ep->w = 0;
        ep->inited = 1;
    }
}

void
endpoint_send(struct endpoint *ep, zipc_msg_t *m)
{
    endpoint_init(ep);
    acquire(&ep->lock);
    if(ep->w - ep->r < ENDPOINT_BUFSZ){
        ep->q[ep->w % ENDPOINT_BUFSZ] = *m;
        ep->w++;
        wakeup(&ep->r);
    }
    release(&ep->lock);
}

int
endpoint_recv(struct endpoint *ep, zipc_msg_t *m)
{
    endpoint_init(ep);
    acquire(&ep->lock);
    while(ep->r == ep->w){
        sleep(&ep->r, &ep->lock);
    }
    *m = ep->q[ep->r % ENDPOINT_BUFSZ];
    ep->r++;
    release(&ep->lock);
    return 0;
}

int
sys_endpoint_send(void)
{
    zipc_msg_t *umsg;
    if(argptr(0, (void*)&umsg, sizeof(*umsg)) < 0)
        return -1;
    endpoint_send(&global_ep, umsg);
    return 0;
}

int
sys_endpoint_recv(void)
{
    zipc_msg_t *udst;
    zipc_msg_t m;
    if(argptr(0, (void*)&udst, sizeof(*udst)) < 0)
        return -1;
    endpoint_recv(&global_ep, &m);
    memmove(udst, &m, sizeof(m));
    return 0;
}
