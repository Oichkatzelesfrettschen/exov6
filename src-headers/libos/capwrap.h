#pragma once
#include "caplib.h"

#ifdef __cplusplus
extern "C" {
#endif

exo_cap cap_page_alloc(void);
int cap_page_free(exo_cap cap);
int cap_send_simple(exo_cap dest, const void *buf, size_t len);
int cap_recv_simple(exo_cap src, void *buf, size_t len);

#ifdef __cplusplus
}
#endif
