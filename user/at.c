/**
 * at - Schedule commands for later execution
 * POSIX mandatory utility
 */

#include "types.h"
#include "user.h"
#include "fcntl.h"

int main(int argc, char *argv[]) {
    char buf[256];
    int fd;
    
    if (argc < 2) {
        printf(2, "Usage: at time\n");
        exit(1);
    }
    
    // Create at job file
    fd = open("/var/at/job.at", O_CREATE | O_WRONLY);
    if (fd < 0) {
        printf(2, "at: cannot create job\n");
        exit(1);
    }
    
    // Write time
    printf(fd, "TIME: %s\n", argv[1]);
    
    // Read commands from stdin
    printf(1, "at> ");
    while (gets(buf, sizeof(buf)) != 0) {
        if (strcmp(buf, "EOT") == 0) break;
        write(fd, buf, strlen(buf));
        write(fd, "\n", 1);
        printf(1, "at> ");
    }
    
    close(fd);
    printf(1, "job scheduled for %s\n", argv[1]);
    exit(0);
}
