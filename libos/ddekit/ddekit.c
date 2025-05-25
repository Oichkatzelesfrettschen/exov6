#include "ddekit.h"
#include "user.h"

int ddekit_init(void)
{
    return 0; /* nothing to do for stub */
}

int ddekit_start_driver(const char *path, char *const argv[], exo_cap *drv_ep)
{
    int pid = proc_spawn(path, argv);
    if(pid < 0)
        return -1;
    if(drv_ep)
        *drv_ep = (exo_cap){0};
    return pid;
}

int ddekit_handoff_cap(exo_cap ep, exo_cap cap)
{
    /* send capability to driver over provided endpoint */
    return cap_send(ep, &cap, sizeof(cap));
}
