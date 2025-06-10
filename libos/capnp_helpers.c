#include "capnp_helpers.h"
#include <string.h>

size_t capnp_encode(const void *msg, size_t len, unsigned char *buf) {
    memcpy(buf, msg, len);
    return len;
}

size_t capnp_decode(void *msg, size_t len, const unsigned char *buf) {
    memcpy(msg, buf, len);
    return len;
}
