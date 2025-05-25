#include "microkernel/microkernel.h"

int mk_route_message(exo_cap dest, const void *buf, size_t len) {
    return cap_send(dest, buf, len);
}

int mk_register_endpoint(exo_cap ep) {
    (void)ep;
    return 0;
}

int mk_unregister_endpoint(exo_cap ep) {
    (void)ep;
    return 0;
}
