/**
 * fg - Resume jobs in foreground
 * POSIX shell builtin (also required as utility)
 */

#include "types.h"
#include "user.h"

int main(int argc, char *argv[]) {
    // Shell builtin implementation
    // In a real system, this would be handled by the shell
    printf(1, "fg: shell builtin (POSIX mandatory)\n");
    
    // Exit with appropriate status
    exit(0);
}
