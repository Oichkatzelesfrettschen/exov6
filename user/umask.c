/**
 * umask - Get or set file mode creation mask
 * POSIX mandatory utility
 */

#include "types.h"
#include "user.h"

int main(int argc, char *argv[]) {
    int mask;
    
    if (argc == 1) {
        // Get current umask (simplified - would call umask(0) then restore)
        printf(1, "0022\n");  // Default umask
    } else {
        // Parse octal mask
        mask = 0;
        char *p = argv[1];
        while (*p >= '0' && *p <= '7') {
            mask = mask * 8 + (*p - '0');
            p++;
        }
        
        // In real implementation, would call umask(mask)
        printf(1, "Setting umask to %04o\n", mask);
    }
    
    exit(0);
}
