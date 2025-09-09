/**
 * file - Determine file type
 * POSIX mandatory utility
 */

#include "types.h"
#include "sys/stat.h"
#include "user.h"
#include "fcntl.h"

int main(int argc, char *argv[]) {
    struct stat st;
    int i;
    
    if (argc < 2) {
        printf(2, "Usage: file file...\n");
        exit(1);
    }
    
    for (i = 1; i < argc; i++) {
        if (stat(argv[i], &st) < 0) {
            printf(1, "%s: cannot stat\n", argv[i]);
            continue;
        }
        
        printf(1, "%s: ", argv[i]);
        
        switch(st.type) {
        case T_FILE:
            // Check if executable by looking at size/content
            if (st.size > 0) {
                int fd = open(argv[i], O_RDONLY);
                if (fd >= 0) {
                    char buf[4];
                    if (read(fd, buf, 4) == 4) {
                        if (buf[0] == 0x7f && buf[1] == 'E' && 
                            buf[2] == 'L' && buf[3] == 'F') {
                            printf(1, "ELF executable");
                        } else if (buf[0] == '#' && buf[1] == '!') {
                            printf(1, "shell script");
                        } else {
                            printf(1, "regular file");
                        }
                    } else {
                        printf(1, "empty file");
                    }
                    close(fd);
                }
            } else {
                printf(1, "empty file");
            }
            break;
        case T_DIR:
            printf(1, "directory");
            break;
        case T_DEV:
            printf(1, "character device");
            break;
        default:
            printf(1, "unknown type");
        }
        
        printf(1, "\n");
    }
    
    exit(0);
}
