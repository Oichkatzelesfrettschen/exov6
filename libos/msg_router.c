#include "../include/exokernel.h"

#define MAX_ENDPOINTS 16
static exo_cap endpoints[MAX_ENDPOINTS];
static int endpoint_count;

int mk_route_message(exo_cap dest, const void *buf, size_t len) {
    for (int i = 0; i < endpoint_count; i++) {
        if (endpoints[i].id == dest.id)
            return exo_send(dest, buf, len);
    }
    return -1;
}

int mk_register_endpoint(exo_cap ep) {
    if (endpoint_count >= MAX_ENDPOINTS)
        return -1;
    endpoints[endpoint_count++] = ep;
    return 0;
}

int mk_unregister_endpoint(exo_cap ep) {
    for (int i = 0; i < endpoint_count; i++) {
        if (endpoints[i].id == ep.id) {
            endpoints[i] = endpoints[--endpoint_count];
            return 0;
        }
    }
    return -1;
}
