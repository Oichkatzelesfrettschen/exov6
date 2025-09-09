/**
 * dirname - strip last component from file path
 * POSIX.1-2024 compliant implementation
 * 
 * Usage: dirname string
 * 
 * Removes the last component from a pathname.
 * 
 * Examples:
 *   dirname /usr/bin/sort  -> /usr/bin
 *   dirname stdio.h        -> .
 *   dirname /usr/bin/      -> /usr
 *   dirname /              -> /
 *   dirname //             -> /
 */

#include "types.h"
#include "sys/stat.h"
#include "user.h"

static void
usage(void)
{
    printf(2, "Usage: dirname string\n");
    exit(1);
}

/**
 * Extract directory name from path
 * Handles all POSIX edge cases:
 * - Multiple trailing slashes
 * - Root directory
 * - No directory component (returns ".")
 * - Empty string (returns ".")
 * - Multiple consecutive slashes
 */
static void
print_dirname(const char *path)
{
    char result[256];
    int len;
    int last_slash = -1;
    int i;
    
    // Handle NULL or empty string
    if (!path || !*path) {
        printf(1, ".\n");
        return;
    }
    
    // Copy path to working buffer
    len = strlen(path);
    if (len >= sizeof(result)) {
        len = sizeof(result) - 1;
    }
    memcpy(result, path, len);
    result[len] = '\0';
    
    // Step 1: Remove trailing slashes (except for root)
    while (len > 1 && result[len - 1] == '/') {
        result[--len] = '\0';
    }
    
    // Step 2: If string is // or /, return /
    if (len == 1 && result[0] == '/') {
        printf(1, "/\n");
        return;
    }
    
    // Step 3: Remove trailing non-slash characters
    // Find the last slash
    for (i = len - 1; i >= 0; i--) {
        if (result[i] == '/') {
            last_slash = i;
            break;
        }
    }
    
    // Step 4: If no slash found, return "."
    if (last_slash == -1) {
        printf(1, ".\n");
        return;
    }
    
    // Step 5: Remove trailing non-slash chars
    result[last_slash] = '\0';
    len = last_slash;
    
    // Step 6: Remove trailing slashes again (except for root)
    while (len > 1 && result[len - 1] == '/') {
        result[--len] = '\0';
    }
    
    // Step 7: If empty, we had only slashes, return /
    if (len == 0) {
        printf(1, "/\n");
        return;
    }
    
    printf(1, "%s\n", result);
}

int
main(int argc, char *argv[])
{
    // dirname takes exactly one argument
    if (argc != 2) {
        if (argc < 2) {
            printf(2, "dirname: missing operand\n");
        } else {
            printf(2, "dirname: too many arguments\n");
        }
        usage();
    }
    
    // Process the path
    print_dirname(argv[1]);
    
    exit(0);
}