#include <stdio.h>
#include "procwrap.h"
#include "capwrap.h"

int main(void) {
    proc_handle_t p;
    char *argv[] = {"/bin/true", NULL};
    proc_spawn(&p, "/bin/true", argv);
    proc_wait(&p);

    exo_cap c = capwrap_alloc_page();
    char buf[4] = {'t','e','s','t'};
    capwrap_send(c, buf, sizeof(buf));
    capwrap_recv(c, buf, sizeof(buf));
    printf("proc_cap_test ok\n");
    return 0;
}
