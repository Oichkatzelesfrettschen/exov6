#include <assert.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>
#include "libos/posix.h"


int main(void) {
    const char *msg = "hello";
    unlink("tmpfile.txt");

    int fd = libos_open("tmpfile.txt", O_RDWR | O_CREAT, 0600);
    assert(fd >= 0);
    assert(libos_write(fd, msg, strlen(msg)) == (int)strlen(msg));
    assert(libos_close(fd) == 0);

    fd = libos_open("tmpfile.txt", O_RDONLY, 0);
    char buf[16];
    int n = libos_read(fd, buf, sizeof(buf) - 1);
    assert(n >= 0);
    buf[n] = '\0';
    assert(strcmp(buf, msg) == 0);

    /* truncate existing file */
    assert(libos_close(fd) == 0);
    fd = libos_open("tmpfile.txt", O_WRONLY | O_TRUNC, 0600);
    assert(fd >= 0);
    assert(libos_close(fd) == 0);
    fd = libos_open("tmpfile.txt", O_RDONLY, 0);
    n = libos_read(fd, buf, sizeof(buf));
    assert(n >= 0);

    int dupfd = libos_dup(fd);
    assert(dupfd >= 0);
    assert(libos_close(fd) == 0);
    assert(libos_close(dupfd) == 0);
    return 0;
}
