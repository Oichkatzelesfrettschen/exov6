#include "chan.h"
#include "user.h"

chan_t *
chan_create(const struct msg_type_desc *desc)
{
    chan_t *c = malloc(sizeof(chan_t));
    if(c){
        c->desc = desc;
        c->msg_size = desc ? desc->msg_size : 0;
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

