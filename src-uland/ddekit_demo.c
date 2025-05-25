#include "ddekit/ddekit.h"
#include "user.h"

int main(void)
{
    ddekit_init();
    char *argv[] = {"pingdriver", 0};
    exo_cap ep;
    int pid = ddekit_start_driver("pingdriver", argv, &ep);
    if(pid < 0) {
        printf(1, "ddekit_demo: spawn failed\n");
        exit();
    }
    exo_cap page = cap_alloc_page();
    ddekit_handoff_cap(ep, page);
    printf(1, "ddekit_demo: capability sent to driver\n");
    exit();
}
