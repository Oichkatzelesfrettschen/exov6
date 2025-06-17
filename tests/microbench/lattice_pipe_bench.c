#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include <time.h>

typedef struct { int id; int rights; } exo_cap;

static int pipefd[2];

static int exo_send(exo_cap dest, const void *buf, uint64_t len) {
    (void)dest; return (int)write(pipefd[1], buf, len);
}

static int exo_recv(exo_cap src, void *buf, uint64_t len) {
    (void)src; return (int)read(pipefd[0], buf, len);
}

static int lattice_send(exo_cap cap, const void *buf, uint64_t len) {
    return exo_send(cap, buf, len);
}

static int lattice_recv(exo_cap cap, void *buf, uint64_t len) {
    return exo_recv(cap, buf, len);
}

int main(void) {
    const int iters = 1000;
    const char msg[] = "hello";
    char buf[sizeof msg];
    exo_cap c = {0,0};

    if (pipe(pipefd) != 0) return 1;

    struct timespec s, e;

    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int i = 0; i < iters; ++i) {
        write(pipefd[1], msg, sizeof msg);
        read(pipefd[0], buf, sizeof buf);
    }
    clock_gettime(CLOCK_MONOTONIC, &e);
    long long ns_pipe = (e.tv_sec - s.tv_sec) * 1000000000LL + (e.tv_nsec - s.tv_nsec);

    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int i = 0; i < iters; ++i) {
        lattice_send(c, msg, sizeof msg);
        lattice_recv(c, buf, sizeof buf);
    }
    clock_gettime(CLOCK_MONOTONIC, &e);
    long long ns_lattice = (e.tv_sec - s.tv_sec) * 1000000000LL + (e.tv_nsec - s.tv_nsec);

    printf("pipe: %.2f ns/msg\n", (double)ns_pipe / (2 * iters));
    printf("lattice: %.2f ns/msg\n", (double)ns_lattice / (2 * iters));
    return 0;
}
