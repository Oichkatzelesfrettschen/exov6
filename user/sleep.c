/**
 * sleep - suspend execution for an interval
 * POSIX.1-2024 compliant implementation
 * 
 * Usage: sleep seconds
 * 
 * Suspends execution for at least the specified number of seconds
 */

#include "types.h"
#include "user.h"

static void
usage(void)
{
    printf(2, "Usage: sleep seconds\n");
    exit(1);
}

static int
parse_time(const char *str)
{
    int seconds = 0;
    const char *p = str;
    
    // Parse integer seconds
    while (*p) {
        if (*p < '0' || *p > '9') {
            // POSIX allows suffix like 's' for seconds
            if (*p == 's' && *(p+1) == '\0') {
                break;
            }
            return -1;
        }
        seconds = seconds * 10 + (*p - '0');
        p++;
    }
    
    return seconds;
}

int
main(int argc, char *argv[])
{
    int seconds;
    
    // Check arguments
    if (argc != 2) {
        usage();
    }
    
    // Parse sleep duration
    seconds = parse_time(argv[1]);
    if (seconds < 0) {
        printf(2, "sleep: invalid time interval '%s'\n", argv[1]);
        exit(1);
    }
    
    // Sleep for specified duration
    // In feuerbird, sleep() takes ticks, assuming 100 ticks per second
    sleep(seconds * 100);
    
    exit(0);
}