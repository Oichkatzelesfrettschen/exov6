#include "include/capwrap.h"

exo_cap cap_alloc_page(void)
{
    return exo_alloc_page();
}

int cap_unbind_page(exo_cap cap)
{
    return exo_unbind_page(cap);
}

int cap_send(exo_cap dest, const void *buf, uint64 len)
{
    return exo_send(dest, buf, len);
}

int cap_recv(exo_cap src, void *buf, uint64 len)
{
    return exo_recv(src, buf, len);
}
