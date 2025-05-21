#include "types.h"
#include "spinlock.h"
#include "proc.h"
#include "defs.h"
#include "endpoint.h"

static struct endpoint global_ep;

static int
check_msg(struct endpoint *ep, const zipc_msg_t *m)
{
    if(!ep->type)
        return -1;
    uint8_t sizes[4] = {
        ep->type->w0_sz,
        ep->type->w1_sz,
        ep->type->w2_sz,
        ep->type->w3_sz
    };
    const uint64_t words[4] = {m->w0, m->w1, m->w2, m->w3};
    for(int i = 0; i < 4; i++){
        if(sizes[i] > 8)
            return -1;
        if(sizes[i] < 8){
            uint64_t mask = ~((1ULL << (sizes[i]*8)) - 1);
            if(words[i] & mask)
                return -1;
        }
    }
    return 0;
}

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
endpoint_config(struct endpoint *ep, zipc_msg_t *buf, uint size,
                struct msg_type_desc *type)
{
    endpoint_init(ep);
    acquire(&ep->lock);
    ep->q = buf;
    ep->size = size;
    ep->type = type;
    ep->r = ep->w = 0;
    release(&ep->lock);
}

int
endpoint_send(struct endpoint *ep, zipc_msg_t *m)
{
    endpoint_init(ep);
    acquire(&ep->lock);
    int ok = -1;
    if(ep->q && ep->size && ep->w - ep->r < ep->size &&
       check_msg(ep, m) == 0){
        ep->q[ep->w % ep->size] = *m;
        ep->w++;
        wakeup(&ep->r);
        ok = 0;
    }
    release(&ep->lock);
    return ok;
}

int
endpoint_recv(struct endpoint *ep, zipc_msg_t *m)
{
    endpoint_init(ep);
    acquire(&ep->lock);
    while(ep->q && ep->r == ep->w){
        sleep(&ep->r, &ep->lock);
    }
    if(!ep->q || !ep->type){
        release(&ep->lock);
        return -1;
    }
    zipc_msg_t tmp = ep->q[ep->r % ep->size];
    if(check_msg(ep, &tmp) < 0){
        release(&ep->lock);
        return -1;
    }
    *m = tmp;
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
    return endpoint_send(&global_ep, umsg);
}

int
sys_endpoint_recv(void)
{
    zipc_msg_t *udst;
    zipc_msg_t m;
    if(argptr(0, (void*)&udst, sizeof(*udst)) < 0)
        return -1;
    if(endpoint_recv(&global_ep, &m) < 0)
        return -1;
    memmove(udst, &m, sizeof(m));
    return 0;
}
