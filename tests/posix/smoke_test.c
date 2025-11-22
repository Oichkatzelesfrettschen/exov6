/*
 * smoke_test.c - Basic POSIX Smoke Test for LibOS
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <sys/wait.h>
#include <assert.h>
#include "libos/posix.h"

int main() {
    // Disable buffering to avoid duplicate output after fork
    setvbuf(stdout, NULL, _IONBF, 0);

    printf("Starting LibOS POSIX Smoke Test...\n");

    // Test 1: Simple Print
    printf("Test 1: Standard I/O works.\n");

    // Test 2: Fork and Wait
    printf("Test 2: Forking...\n");
    int pid = libos_fork();

    if (pid < 0) {
        perror("fork failed");
        exit(1);
    } else if (pid == 0) {
        // Child
        printf("  Child process running (PID: %d)\n", libos_getpid());
        libos_exit(42);
    } else {
        // Parent
        printf("  Parent waiting for child (PID: %d)\n", pid);
        int status;
        libos_waitpid(pid, &status, 0);
        if (WIFEXITED(status)) {
            printf("  Child exited with status %d.\n", WEXITSTATUS(status));
            assert(WEXITSTATUS(status) == 42);
        } else {
            printf("  Child did not exit normally.\n");
            exit(1);
        }
    }

    // Test 3: Pipe
    printf("Test 3: Pipes...\n");
    int fds[2];
    if (libos_pipe(fds) < 0) {
        perror("pipe failed");
        exit(1);
    }

    char msg[] = "Hello from pipe";
    if (libos_write(fds[1], msg, sizeof(msg)) != sizeof(msg)) {
        perror("write failed");
        exit(1);
    }

    char buf[32];
    if (libos_read(fds[0], buf, sizeof(buf)) <= 0) {
        perror("read failed");
        exit(1);
    }

    printf("  Pipe read: %s\n", buf);
    assert(strcmp(msg, buf) == 0);

    libos_close(fds[0]);
    libos_close(fds[1]);

    printf("ALL TESTS PASSED.\n");
    return 0;
}
