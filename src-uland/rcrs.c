#include "types.h"
#include "user.h"

int
main(void)
{
    char *argv[] = {"kbdserv", 0};
    for(;;){
        int pid = fork();
        if(pid == 0){
            exec("kbdserv", argv);
            exit();
        }
        wait();
    }
    return 0;
}
