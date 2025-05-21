#include "chan.h"
#include "user.h"

chan_t *
chan_create(size_t msg_size)
{
    chan_t *c = malloc(sizeof(chan_t));
    if(c){
        c->msg_size = msg_size;
        size_t n = msg_size;
        c->desc.w0_sz = n > 8 ? 8 : n;
        n = n > 8 ? n - 8 : 0;
        c->desc.w1_sz = n > 8 ? 8 : n;
        n = n > 8 ? n - 8 : 0;
        c->desc.w2_sz = n > 8 ? 8 : n;
        n = n > 8 ? n - 8 : 0;
        c->desc.w3_sz = n > 8 ? 8 : n;
    }
    return c;
}

void
chan_destroy(chan_t *c)
{
    free(c);
}

int
chan_endpoint_send(chan_t *c, exo_cap dest, const void *msg)
{
    return cap_send(dest, msg, c->msg_size);
}

int
chan_endpoint_recv(chan_t *c, exo_cap src, void *msg)
{
    return cap_recv(src, msg, c->msg_size);
}

