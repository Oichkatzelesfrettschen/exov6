#include "types.h"
#include "user.h"

int main(int argc, char *argv[])
{
    (void)argc; (void)argv;
    printf(1, "filesrv: started user-mode file service\n");
    for(;;){
        sleep(100);
    }
    return 0;
}
