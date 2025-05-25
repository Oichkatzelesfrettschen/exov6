#pragma once
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

void ddekit_init(void);
int ddekit_request_irq(int irq);
void ddekit_print(const char *fmt, ...);

#ifdef __cplusplus
}
#endif
