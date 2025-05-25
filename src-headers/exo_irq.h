#pragma once
#include <stdint.h>
#include "exo_mem.h"
#include "../exo.h"

#ifdef __cplusplus
extern "C" {
#endif

exo_cap exo_alloc_irq(uint irq, uint rights);
int exo_irq_wait(exo_cap cap, uint *irq);
int exo_irq_ack(exo_cap cap);
int irq_trigger(uint irq);

#ifdef __cplusplus
}
#endif
