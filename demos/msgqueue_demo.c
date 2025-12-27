#include "libos/posix.h"
#include "exo_ipc.h"
#include "exokernel.h"
#include "user.h"

int
main(void)
{
    int pid = libos_fork();
    if(pid == 0){
        exo_cap rcap = { .id = 0, .rights = EXO_RIGHT_R };
        char buf[6];
        libos_msgq_recv(rcap, buf, 5);
        buf[5] = '\0';
        printf(1, "child received: %s\n", buf);
        return 0;
    }
    exo_cap wcap = { .id = 0, .rights = EXO_RIGHT_W };
    const char *msg = "hello";
    libos_msgq_send(wcap, msg, 5);
    libos_waitpid(pid, 0, 0);  /* Wait for child, no status, no flags */
    return 0;
}
