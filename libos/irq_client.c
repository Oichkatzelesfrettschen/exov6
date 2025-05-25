#include "libos/irq_client.h"
#include "../src-headers/irq.h"

static void (*user_handler_fn)(void);

static void trampoline(void)
{
    if(user_handler_fn)
        user_handler_fn();
}

int irq_client_bind(exo_cap cap, void (*handler)(void))
{
    user_handler_fn = handler;
    return irq_bind(cap, trampoline);
}

void irq_client_simulate(int irq)
{
    irq_simulate(irq);
}
