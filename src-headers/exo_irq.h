#pragma once
#include <stdint.h>
#include "exo_mem.h"
#include "../exo.h"

#ifdef __cplusplus
extern "C" {
#endif

exo_cap exo_alloc_irq(uint32_t irq, uint32_t rights);
[[nodiscard]] int exo_irq_wait(exo_cap cap, uint32_t *irq);
[[nodiscard]] int exo_irq_ack(exo_cap cap);
int irq_trigger(uint32_t irq);

#ifdef __cplusplus
}
#endif
