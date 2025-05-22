#include "libos/posix.h"
#include "user.h"
#include "string.h"
#include "signal.h"

int main(void) {
    // test pipe
    int p[2];
    if(libos_pipe(p) < 0){
        printf(1, "pipe failed\n");
        exit();
    }
    const char *msg = "x";
    write(p[1], msg, 1);
    char buf[2];
    int r = read(p[0], buf, 1);
    buf[r] = '\0';
    if(r != 1 || buf[0] != 'x'){
        printf(1, "pipe mismatch\n");
        exit();
    }
    close(p[0]);
    close(p[1]);

    // test dup with libos fds
    int fd = libos_open("dupfile", 0);
    if(fd < 0){
        printf(1, "open failed\n");
        exit();
    }
    int fd2 = libos_dup(fd);
    if(fd2 < 0){
        printf(1, "dup failed\n");
        exit();
    }
    libos_write(fd, "A", 1);
    libos_write(fd2, "B", 1);
    libos_close(fd);
    libos_close(fd2);
    fd = libos_open("dupfile", 0);
    char rbuf[3];
    r = libos_read(fd, rbuf, 2);
    rbuf[r] = '\0';
    if(r != 2 || strcmp(rbuf, "AB") != 0){
        printf(1, "dup check failed: %s\n", rbuf);
        exit();
    }
    libos_close(fd);

    // test fork and waitpid
    int pid = libos_fork();
    if(pid == 0){
        exit();
    }
    if(libos_waitpid(pid) != pid){
        printf(1, "waitpid failed\n");
        exit();
    }

    // test signals
    if(libos_sigsend(getpid(), SIGUSR1) < 0){
        printf(1, "sigsend failed\n");
        exit();
    }
    int s = libos_sigcheck();
    if((s & (1<<SIGUSR1)) == 0){
        printf(1, "signal missing\n");
        exit();
    }

    printf(1, "libos_posix_extra_test passed\n");
    exit();
}
