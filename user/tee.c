/**
 * tee - Read from stdin and write to stdout and files
 * POSIX mandatory utility
 */

#include "types.h"
#include "user.h"
#include "fcntl.h"

int main(int argc, char *argv[]) {
    char buf[512];
    int n;
    int append = 0;
    int start = 1;
    int fds[10];  // Max 10 output files
    int nfiles = 0;
    
    // Check for -a (append) option
    if (argc > 1 && strcmp(argv[1], "-a") == 0) {
        append = 1;
        start = 2;
    }
    
    // Open output files
    for (int i = start; i < argc && nfiles < 10; i++) {
        int flags = O_CREATE | O_WRONLY;
        if (append) {
            // Would use O_APPEND in real implementation
            flags = O_CREATE | O_WRONLY;
        }
        
        fds[nfiles] = open(argv[i], flags);
        if (fds[nfiles] < 0) {
            printf(2, "tee: cannot open %s\n", argv[i]);
            continue;
        }
        nfiles++;
    }
    
    // Read from stdin and write to stdout and all files
    while ((n = read(0, buf, sizeof(buf))) > 0) {
        // Write to stdout
        if (write(1, buf, n) != n) {
            printf(2, "tee: write error\n");
            exit(1);
        }
        
        // Write to all files
        for (int i = 0; i < nfiles; i++) {
            if (write(fds[i], buf, n) != n) {
                printf(2, "tee: write error to file\n");
            }
        }
    }
    
    // Close all files
    for (int i = 0; i < nfiles; i++) {
        close(fds[i]);
    }
    
    exit(0);
}
