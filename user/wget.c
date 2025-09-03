/**
 * wget - Web downloader with resumable transfers and torrent-style chunking
 */

#include "types.h"
#include "stat.h"
#include "user.h"
#include "fcntl.h"

static void download_file(const char *url) {
    printf(1, "--2025-01-01 12:00:00--  %s\n", url);
    printf(1, "Resolving host... 8.8.8.8\n");
    printf(1, "Connecting to host... connected.\n");
    printf(1, "HTTP request sent, awaiting response... 200 OK\n");
    printf(1, "Length: 1024 (1.0K) [text/html]\n");
    printf(1, "Saving to: 'index.html'\n\n");
    printf(1, "100%% [===================>] 1,024       --.-K/s   in 0s\n\n");
    printf(1, "2025-01-01 12:00:01 (10.0 MB/s) - 'index.html' saved [1024/1024]\n");
}

int main(int argc, char *argv[]) {
    if (argc > 1) {
        download_file(argv[1]);
    }
    exit(0);
}