#include <stdio.h>
#include <stdint.h>
#include "../../include/linux_compat.h"

static inline uint64_t rdtsc(void) {
    uint32_t lo, hi;
    __asm__ volatile ("rdtsc" : "=a" (lo), "=d" (hi));
    return ((uint64_t)hi << 32) | lo;
}

/* Stubs */
int libos_getpid(void) { return 1; }
int libos_open(const char *path, int flags, int mode) { return -1; }
int libos_close(int fd) { return 0; }
int libos_read(int fd, void *buf, size_t count) { return 0; }
int libos_write(int fd, const void *buf, size_t count) { return 0; }
long libos_lseek(int fd, long offset, int whence) { return 0; }
int libos_stat(const char *path, void *st) { return 0; }
int libos_mkdir(const char *path) { return 0; }
int libos_rmdir(const char *path) { return 0; }
int libos_unlink(const char *path) { return 0; }
int libos_rename(const char *oldpath, const char *newpath) { return 0; }
int libos_fork(void) { return 0; }
int libos_execve(const char *path, char *const argv[], char *const envp[]) { return -1; }
void libos_exit(int status) { }
int libos_waitpid(int pid, int *status, int flags) { return -1; }
void *libos_mmap(void *addr, size_t length, int prot, int flags, int fd, long offset) { return (void*)-1; }
int libos_munmap(void *addr, size_t length) { return 0; }
int libos_socket(int domain, int type, int protocol) { return -1; }
int libos_bind(int fd, const void *addr, int len) { return -1; }
int libos_connect(int fd, const void *addr, int len) { return -1; }
int libos_listen(int fd, int backlog) { return -1; }
int libos_accept(int fd, void *addr, int *len) { return -1; }
int libos_send(int fd, const void *buf, size_t len, int flags) { return -1; }
int libos_recv(int fd, void *buf, size_t len, int flags) { return -1; }
int libos_chdir(const char *path) { return 0; }
char *libos_getcwd(char *buf, size_t size) { return buf; }
// Added stubs for sched
int libos_sched_setscheduler(void) { return 0; }

#include "../../libos/posix/linux_abi.c"

int main() {
    uint64_t start, end;
    long ret;
    int iterations = 1000000;

    printf("Benchmarking syscall dispatch (stubbed getpid, 1M iters)...\n");

    start = rdtsc();
    for (int i = 0; i < iterations; i++) {
        // Prevent compiler optimization of the loop
        __asm__ volatile ("" : : : "memory");
        ret = linux_syscall_dispatch(LINUX_SYS_getpid, 0, 0, 0, 0, 0, 0);
    }
    end = rdtsc();

    printf("Total cycles: %lu\n", end - start);
    printf("Cycles per syscall: %lu\n", (end - start) / iterations);

    return 0;
}
