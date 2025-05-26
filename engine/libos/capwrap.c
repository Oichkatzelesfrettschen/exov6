#include "capwrap.h"

exo_cap capwrap_alloc_page(void) {
    exo_cap c = {0};
    return c;
}

int capwrap_send(exo_cap dest, const void *buf, size_t len) {
    (void)dest; (void)buf; (void)len;
    return -1;
}

int capwrap_recv(exo_cap src, void *buf, size_t len) {
    (void)src; (void)buf; (void)len;
    return -1;
}
