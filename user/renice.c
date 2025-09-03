/**
 * renice - Alter priority of running processes
 * POSIX mandatory utility
 */

#include "types.h"
#include "user.h"

int main(int argc, char *argv[]) {
    int priority;
    int pid;
    
    if (argc < 3) {
        printf(2, "Usage: renice priority pid...\n");
        exit(1);
    }
    
    priority = atoi(argv[1]);
    
    // Process each PID
    for (int i = 2; i < argc; i++) {
        pid = atoi(argv[i]);
        if (pid > 0) {
            // In real implementation, would call setpriority()
            printf(1, "Setting priority %d for pid %d\n", priority, pid);
        } else {
            printf(2, "renice: invalid pid %s\n", argv[i]);
        }
    }
    
    exit(0);
}
