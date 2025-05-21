#include "types.h"
#include "user.h"
#include "ipc.h"

#define PING 1
#define PONG 2

int
main(int argc, char *argv[])
{
    (void)argc; (void)argv;
    zipc_msg_t m;
    for(;;){
        if(endpoint_recv(&m) < 0)
            continue;
        if(m.w0 == PING){
            m.w0 = PONG;
            endpoint_send(&m);
        }
    }
    return 0;
}
