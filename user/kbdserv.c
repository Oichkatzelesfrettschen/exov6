#include "types.h"
#include "user.h"
#include "ipc.h"
#include "fcntl.h"

int
main(int argc, char *argv[])
{
    (void)argc; (void)argv;
    int fd = open("console", O_WRONLY);
    if(fd < 0)
        fd = 1;
    zipc_msg_t m;
    for(;;){
        m.badge = 1;
        zipc_call(&m);
        if((int64_t)m.w0 >= 0){
            char c = m.w0;
            write(fd, &c, 1);
        }
    }
    return 0;
}
