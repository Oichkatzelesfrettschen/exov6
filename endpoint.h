#pragma once
#include "ipc.h"
#include "spinlock.h"

#define ENDPOINT_BUFSZ 16

struct endpoint {
    struct spinlock lock;
    zipc_msg_t q[ENDPOINT_BUFSZ];
    uint r, w;
    int inited;
};

void endpoint_init(struct endpoint *ep);
void endpoint_send(struct endpoint *ep, zipc_msg_t *m);
int endpoint_recv(struct endpoint *ep, zipc_msg_t *m);
