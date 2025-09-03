/**
 * cat - Concatenate and print files
 * POSIX mandatory utility per SUSv5
 */

#include "types.h"
#include "stat.h"
#include "user.h"
#include "fcntl.h"

char buf[512];

void cat_file(int fd) {
    int n;
    
    while ((n = read(fd, buf, sizeof(buf))) > 0) {
        if (write(1, buf, n) != n) {
            printf(2, "cat: write error\n");
            exit(1);
        }
    }
    
    if (n < 0) {
        printf(2, "cat: read error\n");
        exit(1);
    }
}

int main(int argc, char *argv[]) {
    int fd;
    
    // No files specified - read from stdin
    if (argc == 1) {
        cat_file(0);
        exit(0);
    }
    
    // Process each file argument
    for (int i = 1; i < argc; i++) {
        // "-" means stdin per POSIX
        if (strcmp(argv[i], "-") == 0) {
            cat_file(0);
        } else {
            fd = open(argv[i], O_RDONLY);
            if (fd < 0) {
                printf(2, "cat: cannot open %s\n", argv[i]);
                exit(1);
            }
            cat_file(fd);
            close(fd);
        }
    }
    
    exit(0);
}
