#include "types.h"
#include "user.h"
#include "ipc.h"

#define PING 1
#define PONG 2
#define PING_DELAY 20

int
main(void)
{
    char *argv[] = {"pingdriver", 0};
    for(;;){
        int pid = fork();
        if(pid == 0){
            exec("pingdriver", argv);
            exit();
        }

        int mon = fork();
        if(mon == 0){
            zipc_msg_t ping = {.w0 = PING};
            zipc_msg_t pong;
            for(;;){
                endpoint_send(&ping);
                if(endpoint_recv(&pong) < 0 || pong.w0 != PONG)
                    exit();
                sleep(PING_DELAY);
            }
        }

        int died = wait();
        if(died == mon){
            printf(1, "supervisor: restarting driver (timeout)\n");
            kill(pid);
            wait();
        } else {
            printf(1, "supervisor: driver exited\n");
            kill(mon);
            wait();
        }
    }
    return 0;
}
