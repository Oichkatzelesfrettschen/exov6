#pragma once
#ifdef __cplusplus
extern "C" {
#endif
#include "exo_irq.h"

int irq_wait(exo_cap cap, unsigned *irq_no);
int irq_ack(exo_cap cap);
#ifdef __cplusplus
}
#endif
