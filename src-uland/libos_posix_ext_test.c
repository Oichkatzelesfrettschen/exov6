#include "libos/posix.h"
#include "user.h"
#include "string.h"

int main(void) {
    const char *name = "extfile";
    int fd = libos_open(name, 0);
    if(fd < 0){
        printf(1, "ext_test: open failed\n");
        exit();
    }
    const char *msg = "abcdef";
    if(libos_write(fd, msg, strlen(msg)) != (int)strlen(msg)){
        printf(1, "ext_test: write failed\n");
        exit();
    }
    if(libos_lseek(fd, 0, 0) < 0){
        printf(1, "ext_test: lseek failed\n");
        exit();
    }
    char buf[8];
    int n = libos_read(fd, buf, sizeof(buf));
    if(n != (int)strlen(msg) || memcmp(buf, msg, strlen(msg)) != 0){
        printf(1, "ext_test: read mismatch\n");
        exit();
    }
    struct stat st;
    if(libos_fstat(fd, &st) < 0){
        printf(1, "ext_test: fstat failed\n");
        exit();
    }
    libos_close(fd);

    if(libos_stat(name, &st) < 0){
        printf(1, "ext_test: stat failed\n");
        exit();
    }
    if(libos_unlink(name) < 0){
        printf(1, "ext_test: unlink failed\n");
        exit();
    }
    if(libos_stat(name, &st) >= 0){
        printf(1, "ext_test: file still exists\n");
        exit();
    }

    printf(1, "libos_posix_ext_test passed\n");
    exit();
}
