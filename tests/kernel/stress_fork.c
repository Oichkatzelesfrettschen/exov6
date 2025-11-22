#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/wait.h>
#include <signal.h>

#define MAX_PROCS 100
#define ITERATIONS 50

int main(void) {
    printf("Starting fork stress test...\n");

    for (int i = 0; i < ITERATIONS; i++) {
        pid_t pids[MAX_PROCS];
        int num_procs = 0;

        for (int j = 0; j < MAX_PROCS; j++) {
            pid_t pid = fork();
            if (pid == 0) {
                // Child
                usleep(1000); // Do some work
                exit(0);
            } else if (pid > 0) {
                pids[num_procs++] = pid;
            } else {
                perror("fork failed");
                // Don't exit, just stop spawning for this iteration
                break;
            }
        }

        // Wait for all
        for (int j = 0; j < num_procs; j++) {
            waitpid(pids[j], NULL, 0);
        }

        if (i % 10 == 0) printf("Iteration %d completed\n", i);
    }

    printf("Fork stress test passed.\n");
    return 0;
}
