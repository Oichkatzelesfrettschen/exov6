#include "exokernel.h"
#include "ipc.h"
#include "syscall.h"
#include "user.h"

#define MK_MSG_REGISTER 3

// Forward declaration for endpoint_send function
int endpoint_send(void* endpoint, const void* msg);

int microkernel_register(void) {
    zipc_msg_t m = {0};
    m.w0 = MK_MSG_REGISTER;
    m.w1 = getpid();
    endpoint_send(NULL, &m);  // TODO: provide proper endpoint
    return 0;
}
