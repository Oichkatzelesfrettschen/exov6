/**
 * dd - Data duplicator
 * POSIX mandatory utility
 */

#include "types.h"
#include "user.h"
#include "fcntl.h"

#define DEFAULT_BS 512

int main(int argc, char *argv[]) {
    int ifd = 0, ofd = 1;  // Default: stdin to stdout
    int bs = DEFAULT_BS;
    int count = -1;  // -1 means no limit
    char *buf;
    int n, total = 0;
    int records_in = 0, records_out = 0;
    
    // Parse arguments (simplified)
    for (int i = 1; i < argc; i++) {
        if (strncmp(argv[i], "if=", 3) == 0) {
            ifd = open(argv[i] + 3, O_RDONLY);
            if (ifd < 0) {
                printf(2, "dd: cannot open %s\n", argv[i] + 3);
                exit(1);
            }
        } else if (strncmp(argv[i], "of=", 3) == 0) {
            ofd = open(argv[i] + 3, O_CREATE | O_WRONLY);
            if (ofd < 0) {
                printf(2, "dd: cannot create %s\n", argv[i] + 3);
                exit(1);
            }
        } else if (strncmp(argv[i], "bs=", 3) == 0) {
            bs = atoi(argv[i] + 3);
            if (bs <= 0) bs = DEFAULT_BS;
        } else if (strncmp(argv[i], "count=", 6) == 0) {
            count = atoi(argv[i] + 6);
        }
    }
    
    // Allocate buffer
    buf = malloc(bs);
    if (!buf) {
        printf(2, "dd: cannot allocate buffer\n");
        exit(1);
    }
    
    // Copy data
    while (count != 0) {
        n = read(ifd, buf, bs);
        if (n < 0) {
            printf(2, "dd: read error\n");
            exit(1);
        }
        if (n == 0) break;
        
        records_in++;
        
        if (write(ofd, buf, n) != n) {
            printf(2, "dd: write error\n");
            exit(1);
        }
        
        records_out++;
        total += n;
        
        if (count > 0) count--;
    }
    
    // Print statistics
    printf(2, "%d+0 records in\n", records_in);
    printf(2, "%d+0 records out\n", records_out);
    printf(2, "%d bytes copied\n", total);
    
    free(buf);
    if (ifd > 0) close(ifd);
    if (ofd > 1) close(ofd);
    
    exit(0);
}
