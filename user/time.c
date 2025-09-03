/**
 * time - Time command execution
 * POSIX mandatory utility
 */

#include "types.h"
#include "user.h"

int main(int argc, char *argv[]) {
    int pid;
    int start, end;
    
    if (argc < 2) {
        printf(2, "Usage: time command [args...]\n");
        exit(1);
    }
    
    // Get start time (simplified - would use uptime())
    start = uptime();
    
    pid = fork();
    if (pid < 0) {
        printf(2, "time: fork failed\n");
        exit(1);
    }
    
    if (pid == 0) {
        // Child - execute command
        exec(argv[1], argv + 1);
        printf(2, "time: exec %s failed\n", argv[1]);
        exit(1);
    }
    
    // Parent - wait for child
    wait();
    
    // Get end time
    end = uptime();
    
    // Print timing (in ticks, would convert to seconds)
    int elapsed = end - start;
    printf(2, "\nreal\t%d.%02ds\n", elapsed / 100, elapsed % 100);
    printf(2, "user\t0.00s\n");  // Simplified
    printf(2, "sys\t0.00s\n");   // Simplified
    
    exit(0);
}
