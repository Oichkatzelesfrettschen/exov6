#include <assert.h>
#include <fcntl.h>
#include <string.h>
#include "libos/posix.h"

int main(void){
    const char *msg = "hi";
    int fd = libos_open("src.txt", O_RDWR | O_CREAT, 0600);
    assert(fd >= 0);
    assert(libos_write(fd, msg, strlen(msg)) == (int)strlen(msg));
    assert(libos_close(fd) == 0);

    assert(libos_rename("src.txt", "dst.txt") == 0);

    fd = libos_open("dst.txt", O_RDONLY, 0);
    char buf[8];
    int n = libos_read(fd, buf, sizeof(buf)-1);
    assert(n >= (int)strlen(msg));
    buf[n] = '\0';
    assert(strcmp(buf, msg) == 0);
    assert(libos_close(fd) == 0);

    fd = libos_open("src.txt", O_RDONLY, 0);
    n = libos_read(fd, buf, sizeof(buf));
    assert(n >= 0);
    libos_close(fd);

    assert(libos_unlink("dst.txt") == 0);
    fd = libos_open("dst.txt", O_RDONLY, 0);
    n = libos_read(fd, buf, sizeof(buf));
    assert(n >= 0);
    libos_close(fd);
    libos_unlink("dst.txt");
    libos_unlink("src.txt");
    return 0;
}
