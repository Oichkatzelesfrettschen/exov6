/**
 * timeout - Run command with time limit
 * POSIX mandatory utility
 */

#include "types.h"
#include "user.h"

int main(int argc, char *argv[]) {
    int duration;
    int pid;
    
    if (argc < 3) {
        printf(2, "Usage: timeout duration command [args...]\n");
        exit(1);
    }
    
    duration = atoi(argv[1]);
    if (duration <= 0) {
        printf(2, "timeout: invalid duration\n");
        exit(1);
    }
    
    pid = fork();
    if (pid < 0) {
        printf(2, "timeout: fork failed\n");
        exit(1);
    }
    
    if (pid == 0) {
        // Child - execute command
        exec(argv[2], argv + 2);
        printf(2, "timeout: exec failed\n");
        exit(126);
    }
    
    // Parent - wait with timeout
    // Simplified - would use alarm() or similar
    for (int i = 0; i < duration * 100; i++) {
        if (wait() > 0) {
            // Command completed
            exit(0);
        }
        sleep(1);
    }
    
    // Timeout - kill child
    kill(pid);
    printf(2, "timeout: killed after %d seconds\n", duration);
    exit(124);
}
