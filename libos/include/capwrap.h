#pragma once
#ifdef __cplusplus
extern "C" {
#endif
#include <stddef.h>
#include "caplib.h"

exo_cap capwrap_alloc_page(void);
int capwrap_send(exo_cap dest, const void *buf, size_t len);
int capwrap_recv(exo_cap src, void *buf, size_t len);
#ifdef __cplusplus
}
#endif
