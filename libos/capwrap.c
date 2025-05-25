#include "capwrap.h"

exo_cap capwrap_alloc_page(void) {
    exo_cap c = {0};
    return c;
}

enum exo_ipc_status capwrap_send(exo_cap dest, const void *buf, size_t len) {
    (void)dest; (void)buf; (void)len;
    return EXO_IPC_INVALID;
}

enum exo_ipc_status capwrap_recv(exo_cap src, void *buf, size_t len) {
    (void)src; (void)buf; (void)len;
    return EXO_IPC_INVALID;
}
