/**
 * echo - Write arguments to standard output
 * POSIX mandatory utility per SUSv5
 */

#include "types.h"
#include "user.h"

int main(int argc, char *argv[]) {
    int no_newline = 0;
    int start = 1;
    
    // Check for -n option (no trailing newline)
    if (argc > 1 && strcmp(argv[1], "-n") == 0) {
        no_newline = 1;
        start = 2;
    }
    
    // Print all arguments separated by spaces
    for (int i = start; i < argc; i++) {
        printf(1, "%s", argv[i]);
        if (i < argc - 1) {
            printf(1, " ");
        }
    }
    
    // Print newline unless -n specified
    if (!no_newline) {
        printf(1, "\n");
    }
    
    exit(0);
}
