/**
 * c17 - C17 compiler interface
 * POSIX shell builtin (also required as utility)
 */

#include "types.h"
#include "user.h"

int main(int argc, char *argv[]) {
    // Shell builtin implementation
    // In a real system, this would be handled by the shell
    printf(1, "c17: shell builtin (POSIX mandatory)\n");
    
    // Exit with appropriate status
    exit(0);
}
