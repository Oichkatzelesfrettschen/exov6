#pragma once
#include "include/exokernel.h"

/* Basic capability helpers used by DDEKit and libOS */

exo_cap cap_alloc_page(void);
int cap_unbind_page(exo_cap cap);
int cap_send(exo_cap dest, const void *buf, uint64 len);
int cap_recv(exo_cap src, void *buf, uint64 len);

