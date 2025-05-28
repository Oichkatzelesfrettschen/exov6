#include "microkernel/microkernel.h"
#include "ipc.h"
#include "syscall.h"
#include "user.h"

#define MK_MSG_REGISTER 3

int microkernel_register(void) {
    zipc_msg_t m = {0};
    m.w0 = MK_MSG_REGISTER;
    m.w1 = getpid();
    endpoint_send(&m);
    return 0;
}
