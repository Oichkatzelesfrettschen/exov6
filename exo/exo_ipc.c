#include "defs.h"
#include "kernel/exo_ipc.h"

int exo_send(exo_cap dest, const void *buf, uint64_t len) {
    // TODO: implement IPC send
    (void)dest; (void)buf; (void)len;
    return -1;
}

int exo_recv(exo_cap src, void *buf, uint64_t len) {
    // TODO: implement IPC receive
    (void)src; (void)buf; (void)len;
    return -1;
}
