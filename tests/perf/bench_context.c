#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <sys/wait.h>

int main(void) {
    const int iters = 100000;
    int p1[2], p2[2];
    char c = 'a';

    if (pipe(p1) == -1 || pipe(p2) == -1) {
        perror("pipe");
        return 1;
    }

    struct timespec s, e;
    clock_gettime(CLOCK_MONOTONIC, &s);

    if (fork() == 0) {
        // Child
        for (int i = 0; i < iters; i++) {
            if (read(p1[0], &c, 1) != 1) exit(1);
            if (write(p2[1], &c, 1) != 1) exit(1);
        }
        exit(0);
    } else {
        // Parent
        for (int i = 0; i < iters; i++) {
            if (write(p1[1], &c, 1) != 1) exit(1);
            if (read(p2[0], &c, 1) != 1) exit(1);
        }
        wait(NULL);
    }

    clock_gettime(CLOCK_MONOTONIC, &e);
    long long ns = (e.tv_sec - s.tv_sec) * 1000000000LL + (e.tv_nsec - s.tv_nsec);
    // 2 context switches per iteration
    printf("context switch (pipe): %.2f ns\n", (double)ns / (iters * 2));

     if ((double)ns / (iters * 2) > 5000.0) {
        fprintf(stderr, "FAILURE: Context switch latency regression detected!\n");
        return 1;
    }

    return 0;
}
