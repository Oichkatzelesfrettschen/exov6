#include "libos/posix.h"
#include "user.h"
#include "stat.h"
#include "signal.h"

int main(void) {
    int fd = libos_open("extra", 0);
    if (fd < 0)
        fd = libos_open("extra", O_CREATE);
    libos_write(fd, "x", 1);
    libos_lseek(fd, 0, 0);
    struct stat st;
    libos_stat("extra", &st);
    void *p = libos_mmap(0, 128, 0, 0, -1, 0);
    libos_munmap(p, 128);
    libos_getpgrp();
    libos_setpgid(0, 0);
    libos_socket(0, 0, 0);
    libos_sigset_t ss;
    libos_sigemptyset(&ss);
    libos_sigaddset(&ss, SIGUSR1);
    libos_close(fd);
    char *argv[] = {"echo", "extra", 0};
    libos_spawn("echo", argv);
    wait();
    printf(1, "libos_posix_extra_test done\n");
    exit();
}
