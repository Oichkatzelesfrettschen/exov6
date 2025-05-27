#include <assert.h>
#include <fcntl.h>
#include <string.h>
#include <unistd.h>
#include "libos/posix.h"

int main(void){
    const char *msg = "abcdef";
    int fd = libos_open("ft.tmp", O_RDWR | O_CREAT, 0600);
    assert(fd >= 0);
    assert(libos_write(fd, msg, strlen(msg)) == (int)strlen(msg));
    assert(libos_ftruncate(fd, 3) == 0);
    libos_lseek(fd, 0, SEEK_SET);
    char buf[8];
    int n = libos_read(fd, buf, sizeof(buf)-1);
    buf[n] = '\0';
    assert(strcmp(buf, "abc") == 0);
    assert(libos_ftruncate(-1, 1) == -1);
    assert(libos_close(fd) == 0);
    libos_unlink("ft.tmp");
    return 0;
}
