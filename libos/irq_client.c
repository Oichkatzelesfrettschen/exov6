#include "exokernel.h"
#include "libos/irq_client.h"

int irq_wait(exo_cap cap, unsigned *irq_no) {
    return exo_irq_wait(cap, irq_no);
}

int irq_ack(exo_cap cap) {
    return exo_irq_ack(cap);
}
