/**
 * wait - Wait for process completion
 * POSIX mandatory utility
 */

#include "types.h"
#include "user.h"

int main(int argc, char *argv[]) {
    int pid;
    int status;
    
    if (argc == 1) {
        // Wait for any child
        while ((pid = wait()) > 0) {
            // Child reaped
        }
    } else {
        // Wait for specific PIDs
        for (int i = 1; i < argc; i++) {
            pid = atoi(argv[i]);
            if (pid > 0) {
                // In real implementation, would wait for specific PID
                printf(1, "Waiting for pid %d\n", pid);
                wait();
            }
        }
    }
    
    exit(0);
}
