#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <sys/wait.h>

#define BUF_SIZE 4096
#define TOTAL_BYTES (1024 * 1024 * 100) // 100 MB

int main(void) {
    int p[2];
    char *buf = malloc(BUF_SIZE);

    if (pipe(p) == -1) {
        perror("pipe");
        return 1;
    }

    struct timespec s, e;
    clock_gettime(CLOCK_MONOTONIC, &s);

    if (fork() == 0) {
        // Child: reader
        long long bytes_read = 0;
        while (bytes_read < TOTAL_BYTES) {
            int n = read(p[0], buf, BUF_SIZE);
            if (n <= 0) break;
            bytes_read += n;
        }
        exit(0);
    } else {
        // Parent: writer
        long long bytes_written = 0;
        while (bytes_written < TOTAL_BYTES) {
            int n = write(p[1], buf, BUF_SIZE);
            if (n <= 0) break;
            bytes_written += n;
        }
        wait(NULL);
    }

    clock_gettime(CLOCK_MONOTONIC, &e);
    long long ns = (e.tv_sec - s.tv_sec) * 1000000000LL + (e.tv_nsec - s.tv_nsec);
    double seconds = (double)ns / 1000000000.0;
    double mb = (double)TOTAL_BYTES / (1024 * 1024);

    printf("IPC throughput (pipe): %.2f MB/s\n", mb / seconds);

    if ((mb / seconds) < 50.0) { // arbitrary threshold
         fprintf(stderr, "FAILURE: IPC throughput regression detected!\n");
         return 1;
    }

    free(buf);
    return 0;
}
