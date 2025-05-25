#include "ddekit.h"
#include "user.h"

void ddekit_init(void)
{
    /* No special initialization for stub implementation */
}

int ddekit_request_irq(int irq)
{
    (void)irq;
    /* Stub always succeeds */
    return 0;
}

void ddekit_print(const char *fmt, ...)
{
    printf(1, "%s", fmt);
}
