#pragma once
#include "ipc.h"
#include "spinlock.h"

struct endpoint {
    struct spinlock lock;
    zipc_msg_t *q;
    uint size;
    uint r, w;
    int inited;
};

void endpoint_init(struct endpoint *ep);
void endpoint_config(struct endpoint *ep, zipc_msg_t *buf, uint size);
void endpoint_send(struct endpoint *ep, zipc_msg_t *m);
int endpoint_recv(struct endpoint *ep, zipc_msg_t *m);
