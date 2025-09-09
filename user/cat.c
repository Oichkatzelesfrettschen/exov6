#include <types.h>
#include "user.h"
#include "fcntl.h"

// Working cat implementation - replaces cat_real.c stub

void cat_file(int fd) {
    int n;
    char buf[512];
    
    // Read from file descriptor and write to stdout
    while ((n = read(fd, buf, sizeof(buf))) > 0) {
        if (write(1, buf, n) != n) {
            printf(2, "cat: write error\n");
            exit(0);
        }
    }
    
    if (n < 0) {
        printf(2, "cat: read error\n");
        exit(0);
    }
}

int main(int argc, char *argv[]) {
    int fd, i;
    
    // If no arguments, read from stdin
    if (argc <= 1) {
        cat_file(0);  // stdin
        exit(0);
    }
    
    // Process each file argument
    for (i = 1; i < argc; i++) {
        if ((fd = open(argv[i], 0)) < 0) {  // 0 = O_RDONLY
            printf(2, "cat: cannot open %s\n", argv[i]);
            exit(0);
        }
        cat_file(fd);
        close(fd);
    }
    
    exit(0);
}