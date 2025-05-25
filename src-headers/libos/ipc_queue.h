#pragma once
#include "exo_ipc.h"
#include "uv_spinlock.h"

#define IPC_BUFSZ 64

struct ipc_entry {
    zipc_msg_t msg;
    exo_cap frame;
};

struct exo_mailbox {
    uv_spinlock_t lock;
    struct ipc_entry buf[IPC_BUFSZ];
    unsigned r, w;
};

int ipc_queue_send(struct exo_mailbox *mb, exo_cap dest, const void *buf,
                   uint64_t len);
int ipc_queue_recv(struct exo_mailbox *mb, exo_cap src, void *buf,
                   uint64_t len);
