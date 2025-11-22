#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <time.h>
#include <unistd.h>
#include <sys/types.h>

int main(void) {
    const int iters = 1000000;
    struct timespec s, e;

    clock_gettime(CLOCK_MONOTONIC, &s);
    for(int i = 0; i < iters; i++) {
        getpid();
    }
    clock_gettime(CLOCK_MONOTONIC, &e);

    long long ns = (e.tv_sec - s.tv_sec) * 1000000000LL + (e.tv_nsec - s.tv_nsec);
    printf("syscall (getpid): %.2f ns\n", (double)ns / iters);

    if ((double)ns / iters > 1000.0) {
        fprintf(stderr, "FAILURE: Syscall latency regression detected!\n");
        return 1;
    }

    return 0;
}
