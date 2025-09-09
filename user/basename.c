/**
 * basename - strip directory and suffix from filenames
 * POSIX.1-2024 compliant implementation
 * 
 * Usage: basename string [suffix]
 *        basename -a [-s suffix] string...
 *        basename -s suffix [-a] string...
 * 
 * Options:
 *   -a  Support multiple arguments
 *   -s  Remove suffix from all arguments
 *   -z  End each output with NUL instead of newline
 */

#include "types.h"
#include "sys/stat.h"
#include "user.h"

static int aflag = 0;     // Multiple arguments
static int zflag = 0;     // NUL terminator
static char *suffix = 0;  // Suffix to remove

static void
usage(void)
{
    printf(2, "Usage: basename string [suffix]\n");
    printf(2, "       basename -a [-s suffix] string...\n");
    printf(2, "       basename -s suffix [-a] string...\n");
    exit(1);
}

/**
 * Extract basename from path
 * Handles all edge cases per POSIX:
 * - Multiple trailing slashes
 * - Root directory "/"
 * - Empty string
 * - Paths with no directory component
 */
static void
print_basename(const char *path, const char *suffix_to_remove)
{
    char result[256];
    int len;
    const char *p;
    const char *base;
    
    // Handle empty string
    if (!path || !*path) {
        printf(1, ".");
        printf(1, "%c", zflag ? '\0' : '\n');
        return;
    }
    
    // Make a working copy
    len = strlen(path);
    if (len >= sizeof(result)) {
        len = sizeof(result) - 1;
    }
    memcpy(result, path, len);
    result[len] = '\0';
    
    // Remove trailing slashes (except for root)
    while (len > 1 && result[len - 1] == '/') {
        result[--len] = '\0';
    }
    
    // Handle root directory
    if (len == 1 && result[0] == '/') {
        printf(1, "/");
        printf(1, "%c", zflag ? '\0' : '\n');
        return;
    }
    
    // Find last component
    base = result;
    for (p = result; *p; p++) {
        if (*p == '/' && *(p + 1)) {
            base = p + 1;
        }
    }
    
    // Copy basename to start of result
    if (base != result) {
        len = strlen(base);
        memmove(result, base, len + 1);
    }
    
    // Remove suffix if specified and matches
    if (suffix_to_remove && *suffix_to_remove) {
        int base_len = strlen(result);
        int suf_len = strlen(suffix_to_remove);
        
        if (base_len > suf_len && 
            strcmp(result + base_len - suf_len, suffix_to_remove) == 0) {
            result[base_len - suf_len] = '\0';
        }
    }
    
    // Print result
    printf(1, "%s", result);
    printf(1, "%c", zflag ? '\0' : '\n');
}

int
main(int argc, char *argv[])
{
    int i;
    int path_start = 1;
    char *single_suffix = 0;
    
    // Parse options
    for (i = 1; i < argc && argv[i][0] == '-'; i++) {
        char *p = argv[i] + 1;
        
        // Handle -- (end of options)
        if (strcmp(p, "-") == 0) {
            path_start = i + 1;
            break;
        }
        
        // Handle -s with separate argument
        if (strcmp(p, "s") == 0) {
            i++;
            if (i >= argc) {
                usage();
            }
            suffix = argv[i];
            path_start = i + 1;
            continue;
        }
        
        // Process flags
        while (*p) {
            switch (*p) {
            case 'a':
                aflag = 1;
                break;
            case 's':
                // -s with attached argument
                if (*(p + 1)) {
                    suffix = p + 1;
                    goto next_arg;
                } else {
                    // Separate argument
                    i++;
                    if (i >= argc) {
                        usage();
                    }
                    suffix = argv[i];
                    goto next_arg;
                }
                break;
            case 'z':
                zflag = 1;
                break;
            default:
                printf(2, "basename: invalid option -- '%c'\n", *p);
                usage();
            }
            p++;
        }
        next_arg:
        path_start = i + 1;
    }
    
    // Check for required arguments
    if (path_start >= argc) {
        printf(2, "basename: missing operand\n");
        usage();
    }
    
    // Handle traditional two-argument form: basename string suffix
    if (!aflag && !suffix && path_start + 1 < argc) {
        // Only valid if exactly 2 arguments
        if (path_start + 2 == argc) {
            print_basename(argv[path_start], argv[path_start + 1]);
            exit(0);
        }
    }
    
    // Process paths
    for (i = path_start; i < argc; i++) {
        print_basename(argv[i], suffix);
        
        // Only process first path unless -a flag
        if (!aflag) {
            break;
        }
    }
    
    exit(0);
}