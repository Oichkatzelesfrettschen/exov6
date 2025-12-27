/**
 * User-space endpoint stubs for IPC
 * These are minimal implementations for user-space endpoint management.
 * Note: endpoint_send and endpoint_recv are defined in usys.S as syscalls.
 */
#include "types.h"
#include "user.h"
#include "ipc.h"

/* Forward declaration - struct endpoint defined in endpoint.h */
struct endpoint;

void endpoint_init(struct endpoint *ep) {
    (void)ep;
    /* User-space stub - initialization done by kernel */
}

void endpoint_config(struct endpoint *ep, zipc_msg_t *buf, uint32_t size,
                     const void *desc) {
    (void)ep;
    (void)buf;
    (void)size;
    (void)desc;
    /* User-space stub - configuration handled by syscall */
}

/* endpoint_send and endpoint_recv are syscall stubs in usys.S */
