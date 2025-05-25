#include "capwrap.h"
#include "caplib.h"

exo_cap cap_page_alloc(void)
{
    return cap_alloc_page();
}

int cap_page_free(exo_cap cap)
{
    return cap_unbind_page(cap);
}

int cap_send_simple(exo_cap dest, const void *buf, size_t len)
{
    return cap_send(dest, buf, len);
}

int cap_recv_simple(exo_cap src, void *buf, size_t len)
{
    return cap_recv(src, buf, len);
}
