/**
 * test - Evaluate conditional expression
 * POSIX mandatory utility per SUSv5
 */

#include "types.h"
#include "sys/stat.h"
#include "user.h"
#include "fcntl.h"

// Test operators
#define TEST_EQ  1  // -eq
#define TEST_NE  2  // -ne
#define TEST_LT  3  // -lt
#define TEST_LE  4  // -le
#define TEST_GT  5  // -gt
#define TEST_GE  6  // -ge

int is_number(char *s) {
    if (*s == '-') s++;
    while (*s) {
        if (*s < '0' || *s > '9') return 0;
        s++;
    }
    return 1;
}

int main(int argc, char *argv[]) {
    struct stat st;
    
    // Handle [ ] form
    if (strcmp(argv[0], "[") == 0) {
        if (strcmp(argv[argc-1], "]") != 0) {
            exit(1);
        }
        argc--;
    }
    
    // No arguments = false
    if (argc == 1) {
        exit(1);
    }
    
    // Single argument = true if non-empty
    if (argc == 2) {
        exit(strlen(argv[1]) == 0 ? 1 : 0);
    }
    
    // File tests
    if (argc == 3 && argv[1][0] == '-') {
        switch (argv[1][1]) {
            case 'e': // File exists
                exit(stat(argv[2], &st) < 0 ? 1 : 0);
            case 'f': // Regular file
                if (stat(argv[2], &st) < 0) exit(1);
                exit(st.type == T_FILE ? 0 : 1);
            case 'd': // Directory
                if (stat(argv[2], &st) < 0) exit(1);
                exit(st.type == T_DIR ? 0 : 1);
            case 'r': // Readable
            case 'w': // Writable
            case 'x': // Executable
                // Simplified - assume all files have rwx
                exit(stat(argv[2], &st) < 0 ? 1 : 0);
            case 's': // Non-zero size
                if (stat(argv[2], &st) < 0) exit(1);
                exit(st.size > 0 ? 0 : 1);
            case 'z': // Zero length string
                exit(strlen(argv[2]) == 0 ? 0 : 1);
            case 'n': // Non-zero length string
                exit(strlen(argv[2]) > 0 ? 0 : 1);
        }
    }
    
    // Binary operators
    if (argc == 4) {
        // String comparison
        if (strcmp(argv[2], "=") == 0) {
            exit(strcmp(argv[1], argv[3]) == 0 ? 0 : 1);
        }
        if (strcmp(argv[2], "!=") == 0) {
            exit(strcmp(argv[1], argv[3]) != 0 ? 0 : 1);
        }
        
        // Numeric comparison
        if (is_number(argv[1]) && is_number(argv[3])) {
            int a = atoi(argv[1]);
            int b = atoi(argv[3]);
            
            if (strcmp(argv[2], "-eq") == 0) exit(a == b ? 0 : 1);
            if (strcmp(argv[2], "-ne") == 0) exit(a != b ? 0 : 1);
            if (strcmp(argv[2], "-lt") == 0) exit(a < b ? 0 : 1);
            if (strcmp(argv[2], "-le") == 0) exit(a <= b ? 0 : 1);
            if (strcmp(argv[2], "-gt") == 0) exit(a > b ? 0 : 1);
            if (strcmp(argv[2], "-ge") == 0) exit(a >= b ? 0 : 1);
        }
    }
    
    // Unknown expression
    exit(2);
}
