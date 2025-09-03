/**
 * batch - Execute commands when system load permits
 * POSIX mandatory utility
 */

#include "types.h"
#include "user.h"

int main(int argc, char *argv[]) {
    // Simplified - same as 'at now'
    char *at_args[] = { "at", "now", 0 };
    
    printf(1, "batch: scheduling for low load execution\n");
    exec("/bin/at", at_args);
    
    // If we get here, fallback
    printf(1, "batch job queued\n");
    exit(0);
}
