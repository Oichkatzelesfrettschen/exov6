/**
 * pr - Print files with formatting
 * POSIX mandatory utility
 */

#include "types.h"
#include "user.h"
#include "fcntl.h"

int main(int argc, char *argv[]) {
    int fd = 0;
    char buf[512];
    int n;
    int page = 1;
    int line = 0;
    int lines_per_page = 66;
    
    if (argc > 1) {
        fd = open(argv[1], O_RDONLY);
        if (fd < 0) {
            printf(2, "pr: cannot open %s\n", argv[1]);
            exit(1);
        }
    }
    
    // Print header
    printf(1, "\n\n     Page %d\n\n", page);
    
    // Print file with pagination
    while ((n = read(fd, buf, sizeof(buf))) > 0) {
        for (int i = 0; i < n; i++) {
            write(1, &buf[i], 1);
            if (buf[i] == '\n') {
                line++;
                if (line >= lines_per_page - 5) {
                    printf(1, "\n\n     Page %d\n\n", ++page);
                    line = 0;
                }
            }
        }
    }
    
    if (fd > 0) close(fd);
    exit(0);
}
