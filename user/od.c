/**
 * od - Octal dump
 * POSIX mandatory utility
 */

#include "types.h"
#include "user.h"
#include "fcntl.h"

int main(int argc, char *argv[]) {
    int fd = 0;
    unsigned char buf[16];
    int n, addr = 0;
    int format = 'o';  // Default octal
    
    // Parse options
    if (argc > 1 && argv[1][0] == '-') {
        switch(argv[1][1]) {
            case 'x': format = 'x'; break;
            case 'd': format = 'd'; break;
            case 'c': format = 'c'; break;
        }
        argv++;
        argc--;
    }
    
    // Open file if specified
    if (argc > 1) {
        fd = open(argv[1], O_RDONLY);
        if (fd < 0) {
            printf(2, "od: cannot open %s\n", argv[1]);
            exit(1);
        }
    }
    
    // Dump data
    while ((n = read(fd, buf, 16)) > 0) {
        printf(1, "%07o", addr);
        
        for (int i = 0; i < n; i++) {
            if (format == 'o')
                printf(1, " %03o", buf[i]);
            else if (format == 'x')
                printf(1, " %02x", buf[i]);
            else if (format == 'd')
                printf(1, " %3d", buf[i]);
            else if (format == 'c') {
                if (buf[i] >= 32 && buf[i] < 127)
                    printf(1, "  %c", buf[i]);
                else
                    printf(1, " \\%02x", buf[i]);
            }
        }
        
        printf(1, "\n");
        addr += n;
    }
    
    if (fd > 0) close(fd);
    exit(0);
}
