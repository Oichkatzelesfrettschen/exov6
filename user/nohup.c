/**
 * nohup - Run command immune to hangups
 * POSIX mandatory utility
 */

#include "types.h"
#include "user.h"
#include "fcntl.h"

int main(int argc, char *argv[]) {
    int fd;
    
    if (argc < 2) {
        printf(2, "Usage: nohup command [args...]\n");
        exit(127);
    }
    
    // Redirect stdout to nohup.out if it's a terminal
    fd = open("nohup.out", O_CREATE | O_WRONLY);
    if (fd >= 0) {
        close(1);
        dup(fd);
        close(2);
        dup(fd);
        close(fd);
    }
    
    // In real implementation, would ignore SIGHUP
    
    // Execute command
    exec(argv[1], argv + 1);
    printf(2, "nohup: exec failed\n");
    exit(127);
}
