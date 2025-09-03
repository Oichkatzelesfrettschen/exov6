/**
 * nice - Run command with modified scheduling priority
 * POSIX mandatory utility
 */

#include "types.h"
#include "user.h"

int main(int argc, char *argv[]) {
    int adjustment = 10;  // Default nice value
    int start = 1;
    
    if (argc < 2) {
        // Just print current nice value
        printf(1, "0\n");
        exit(0);
    }
    
    // Parse -n option
    if (strcmp(argv[1], "-n") == 0 && argc > 2) {
        adjustment = atoi(argv[2]);
        start = 3;
    } else if (argv[1][0] == '-' || argv[1][0] == '+') {
        adjustment = atoi(argv[1]);
        start = 2;
    }
    
    if (start >= argc) {
        printf(2, "nice: no command specified\n");
        exit(1);
    }
    
    // In real implementation, would call nice(adjustment)
    printf(1, "Would run with nice value %d: %s\n", adjustment, argv[start]);
    
    // Execute command
    exec(argv[start], argv + start);
    printf(2, "nice: exec failed\n");
    exit(1);
}
