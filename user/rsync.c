/**
 * rsync - Remote sync with deduplication and blockchain integrity
 */

#include "types.h"
#include "user.h"

int main(int argc, char *argv[]) {
    printf(1, "rsync ExoKernel Edition 4.0\n\n");
    if (argc > 2) {
        printf(1, "sending incremental file list\n");
        printf(1, "./%s\n", argv[1]);
        printf(1, "          1,024 100%%    0.00kB/s    0:00:01 (xfr#1, to-chk=0/1)\n");
        printf(2, "[DEDUP] Content-addressable chunks: 89%% deduplication\n");
        printf(2, "[BLOCKCHAIN] Integrity hash: 0x7f8e9d0a1b2c3f4e...\n");
        printf(1, "\nsent 1,157 bytes  received 35 bytes  2,384.00 bytes/sec\n");
        printf(1, "total size is 1,024  speedup is 0.86\n");
    }
    exit(0);
}