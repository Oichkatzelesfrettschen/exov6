#pragma once
#include <stddef.h>
#ifdef __cplusplus
extern "C" {
#endif
size_t capnp_encode(const void *msg, size_t len, unsigned char *buf);
size_t capnp_decode(void *msg, size_t len, const unsigned char *buf);
#ifdef __cplusplus
}
#endif
