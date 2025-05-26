#include "types.h"
#include "user.h"
#include "ipc.h"
#include "capnp_helpers.h"
#include "proto/driver.capnp.h"

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
        DriverPing req = {0};
        capnp_decode(&req, sizeof(req), (unsigned char *)&m);
        if(req.value == PING){
            DriverPing resp = { .value = PONG };
            capnp_encode(&resp, sizeof(resp), (unsigned char *)&m);
            endpoint_send(&m);
        }
    }
    return 0;
}
