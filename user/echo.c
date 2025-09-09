#include <types.h>
#include "user_minimal.h"

// Working echo implementation - replaces echo_real.c stub

int main(int argc, char *argv[]) {
    int i;
    int newline = 1;  // Print newline by default
    int start_arg = 1;
    
    // Handle -n flag (don't print newline)
    if (argc > 1 && argv[1][0] == '-' && argv[1][1] == 'n' && argv[1][2] == '\0') {
        newline = 0;
        start_arg = 2;
    }
    
    // Print all arguments separated by spaces
    for (i = start_arg; i < argc; i++) {
        if (i > start_arg) {
            printf(1, " ");  // Space between arguments
        }
        printf(1, "%s", argv[i]);
    }
    
    // Print newline unless -n flag was used
    if (newline) {
        printf(1, "\n");
    }
    
    exit(0);
}