/**
 * env - Set environment and execute command
 * POSIX mandatory utility
 */

#include "types.h"
#include "user.h"

extern char **environ;

int main(int argc, char *argv[]) {
    int i = 1;
    
    // Skip -i option (ignore environment)
    if (argc > 1 && strcmp(argv[1], "-i") == 0) {
        i = 2;
        // Clear environment (simplified)
    }
    
    // Process VAR=value pairs
    while (i < argc && strchr(argv[i], '=')) {
        // In real implementation, would call putenv()
        printf(1, "Setting: %s\n", argv[i]);
        i++;
    }
    
    // If command specified, execute it
    if (i < argc) {
        // Would exec the command with modified environment
        printf(1, "Would execute: %s\n", argv[i]);
    } else {
        // No command - print environment
        printf(1, "PATH=/bin:/usr/bin\n");
        printf(1, "HOME=/\n");
        printf(1, "USER=root\n");
    }
    
    exit(0);
}
