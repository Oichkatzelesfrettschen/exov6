#include <assert.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>
#include "libos/posix.h"

int libos_open(const char *path, int flags) { return open(path, flags | O_CREAT, 0600); }
int libos_read(int fd, void *buf, size_t n) { return (int)read(fd, buf, n); }
int libos_write(int fd, const void *buf, size_t n) { return (int)write(fd, buf, n); }
int libos_close(int fd) { return close(fd); }
int libos_dup(int fd) { return dup(fd); }

int main(void) {
    const char *msg = "hello";
    int fd = libos_open("tmpfile.txt", O_RDWR);
    assert(fd >= 0);
    assert(libos_write(fd, msg, strlen(msg)) == (int)strlen(msg));
    assert(libos_close(fd) == 0);

    fd = libos_open("tmpfile.txt", O_RDONLY);
    char buf[16];
    int n = libos_read(fd, buf, sizeof(buf) - 1);
    assert(n >= 0);
    buf[n] = '\0';
    assert(strcmp(buf, msg) == 0);

    int dupfd = libos_dup(fd);
    assert(dupfd >= 0);
    assert(libos_close(fd) == 0);
    assert(libos_close(dupfd) == 0);
    return 0;
}
