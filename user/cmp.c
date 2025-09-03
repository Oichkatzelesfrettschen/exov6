/**
 * cmp - Compare two files
 * POSIX mandatory utility
 */

#include "types.h"
#include "user.h"
#include "fcntl.h"

int main(int argc, char *argv[]) {
    int fd1, fd2;
    char buf1[1], buf2[1];
    int n1, n2;
    int byte = 1, line = 1;
    int silent = 0;
    
    if (argc > 1 && strcmp(argv[1], "-s") == 0) {
        silent = 1;
        argv++;
        argc--;
    }
    
    if (argc != 3) {
        printf(2, "Usage: cmp [-s] file1 file2\n");
        exit(2);
    }
    
    fd1 = open(argv[1], O_RDONLY);
    fd2 = open(argv[2], O_RDONLY);
    
    if (fd1 < 0 || fd2 < 0) {
        if (!silent) printf(2, "cmp: cannot open file\n");
        exit(2);
    }
    
    while (1) {
        n1 = read(fd1, buf1, 1);
        n2 = read(fd2, buf2, 1);
        
        if (n1 <= 0 && n2 <= 0) {
            // Files are identical
            exit(0);
        }
        
        if (n1 <= 0 || n2 <= 0) {
            if (!silent) printf(1, "cmp: EOF on %s\n", n1 <= 0 ? argv[1] : argv[2]);
            exit(1);
        }
        
        if (buf1[0] != buf2[0]) {
            if (!silent) printf(1, "%s %s differ: byte %d, line %d\n", 
                               argv[1], argv[2], byte, line);
            exit(1);
        }
        
        if (buf1[0] == '\n') line++;
        byte++;
    }
}
