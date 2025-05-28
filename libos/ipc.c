#include "posix.h"
#include "exo_ipc.h"
#include "exokernel.h"

int libos_msgq_send(exo_cap dest, const void *buf, size_t len) {
    return exo_send(dest, buf, len);
}

int libos_msgq_recv(exo_cap src, void *buf, size_t len) {
    return exo_recv(src, buf, len);
}

int libos_sem_post(exo_cap sem) {
    return exo_send(sem, NULL, 0);
}

int libos_sem_wait(exo_cap sem) {
    char tmp;
    int r = exo_recv(sem, &tmp, 1);
    return r < 0 ? r : 0;
}

exo_cap libos_shm_alloc(void) {
    return exo_alloc_page();
}

int libos_shm_free(exo_cap cap) {
    return exo_unbind_page(cap);
}
