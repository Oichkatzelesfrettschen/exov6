#include "types.h"
#include "user.h"
#include "fcntl.h"
#include "signal.h"

int main(void){
    int p[2];
    if(pipe(p) < 0){
        printf(1, "pipe failed\n");
        exit();
    }
    if(fcntl(p[0], F_SETFL, O_NONBLOCK) < 0){
        printf(1, "fcntl failed\n");
        exit();
    }
    char buf[4];
    int r = read(p[0], buf, sizeof(buf));
    printf(1, "read=%d\n", r);
    sigsend(getpid(), SIGUSR1);
    int s = sigcheck();
    printf(1, "sig=%d\n", s);
    printf(1, "nbtest done\n");
    exit();
}
