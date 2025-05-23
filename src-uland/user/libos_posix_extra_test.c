#include "libos/posix.h"
#include "user.h"

int main(void) {
    int fd = libos_open("extra", 0);
    if (fd < 0)
        fd = libos_open("extra", O_CREATE);
    libos_write(fd, "x", 1);
    libos_close(fd);
    char *argv[] = {"echo", "extra", 0};
    libos_spawn("echo", argv);
    wait();
    printf(1, "libos_posix_extra_test done\n");
    exit();
}
