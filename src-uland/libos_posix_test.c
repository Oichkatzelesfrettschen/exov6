#include "libos/posix.h"
#include "user.h"
#include "string.h"
#include "libos/libfs.h"

int main(void) {
    const char *msg = "hello";
    int fd = libos_open("testfile", 0, 0);
    if(fd < 0){
        printf(1, "posix_test: open failed\n");
        exit();
    }
    if(libos_write(fd, msg, strlen(msg)) != (int)strlen(msg)) {
        printf(1, "posix_test: write failed\n");
        exit();
    }
    libos_close(fd);

    fd = libos_open("testfile", 0, 0);
    char buf[16];
    int n = libos_read(fd, buf, sizeof(buf)-1);
    if(n < 0){
        printf(1, "posix_test: read failed\n");
        exit();
    }
    buf[n] = '\0';
    if(strcmp(buf, msg) != 0){
        printf(1, "posix_test: mismatch %s\n", buf);
        exit();
    }
    libos_close(fd);

    char *argv[] = {"echo", "spawn", 0};
    int pid = libos_spawn("echo", argv);
    if(pid < 0){
        printf(1, "posix_test: spawn failed\n");
        exit();
    }
    wait();

    printf(1, "libos_posix_test passed\n");
    exit();
}
