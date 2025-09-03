/**
 * cron - Schedule command execution
 * POSIX mandatory utility
 */

#include "types.h"
#include "user.h"
#include "fcntl.h"

int main(int argc, char *argv[]) {
    // Simplified cron - just read and display crontab
    int fd;
    char buf[256];
    int n;
    
    fd = open("/var/cron/crontab", O_RDONLY);
    if (fd < 0) {
        printf(1, "No crontab for user\n");
        exit(0);
    }
    
    printf(1, "Current crontab:\n");
    while ((n = read(fd, buf, sizeof(buf))) > 0) {
        write(1, buf, n);
    }
    
    close(fd);
    exit(0);
}
