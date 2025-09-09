#include <types.h>
#include "user.h"
#include "sys/stat.h"

// Working test implementation - replaces test_real.c stub

// Helper function to convert string to integer
int atoi(const char *s) {
    int n = 0;
    int sign = 1;
    
    if (*s == '-') {
        sign = -1;
        s++;
    } else if (*s == '+') {
        s++;
    }
    
    while (*s >= '0' && *s <= '9') {
        n = n * 10 + (*s - '0');
        s++;
    }
    
    return sign * n;
}

int main(int argc, char *argv[]) {
    // test with no arguments - always false
    if (argc == 1) {
        exit(1);  // false
    }
    
    // test STRING - true if STRING is not empty
    if (argc == 2) {
        if (strlen(argv[1]) == 0) {
            exit(1);  // false - empty string
        } else {
            exit(0);  // true - non-empty string
        }
    }
    
    // test EXPRESSION - various test expressions
    if (argc == 3) {
        char *op = argv[1];
        char *file = argv[2];
        struct stat st;
        
        if (strcmp(op, "-f") == 0) {
            // test -f FILE - true if FILE is a regular file
            if (stat(file, &st) < 0) {
                exit(1);  // File doesn't exist
            }
            exit((st.type == T_FILE) ? 0 : 1);
        }
        else if (strcmp(op, "-d") == 0) {
            // test -d FILE - true if FILE is a directory
            if (stat(file, &st) < 0) {
                exit(1);  // File doesn't exist
            }
            exit((st.type == T_DIR) ? 0 : 1);
        }
        else if (strcmp(op, "-e") == 0) {
            // test -e FILE - true if FILE exists
            exit((stat(file, &st) < 0) ? 1 : 0);
        }
        else if (strcmp(op, "-r") == 0) {
            // test -r FILE - true if FILE is readable
            if (stat(file, &st) < 0) {
                exit(1);  // File doesn't exist
            }
            // In our simple system, all files are readable if they exist
            exit(0);
        }
        else if (strcmp(op, "-w") == 0) {
            // test -w FILE - true if FILE is writable
            if (stat(file, &st) < 0) {
                exit(1);  // File doesn't exist
            }
            // In our simple system, all files are writable if they exist
            exit(0);
        }
        else if (strcmp(op, "-x") == 0) {
            // test -x FILE - true if FILE is executable
            if (stat(file, &st) < 0) {
                exit(1);  // File doesn't exist
            }
            // Check if it's a regular file (executables are regular files)
            exit((st.type == T_FILE) ? 0 : 1);
        }
    }
    
    // test EXPRESSION1 OP EXPRESSION2 - binary comparisons
    if (argc == 4) {
        char *arg1 = argv[1];
        char *op = argv[2];
        char *arg2 = argv[3];
        
        if (strcmp(op, "=") == 0) {
            // String equality
            exit((strcmp(arg1, arg2) == 0) ? 0 : 1);
        }
        else if (strcmp(op, "!=") == 0) {
            // String inequality
            exit((strcmp(arg1, arg2) != 0) ? 0 : 1);
        }
        else if (strcmp(op, "-eq") == 0) {
            // Numeric equality
            exit((atoi(arg1) == atoi(arg2)) ? 0 : 1);
        }
        else if (strcmp(op, "-ne") == 0) {
            // Numeric inequality
            exit((atoi(arg1) != atoi(arg2)) ? 0 : 1);
        }
        else if (strcmp(op, "-lt") == 0) {
            // Numeric less than
            exit((atoi(arg1) < atoi(arg2)) ? 0 : 1);
        }
        else if (strcmp(op, "-le") == 0) {
            // Numeric less than or equal
            exit((atoi(arg1) <= atoi(arg2)) ? 0 : 1);
        }
        else if (strcmp(op, "-gt") == 0) {
            // Numeric greater than
            exit((atoi(arg1) > atoi(arg2)) ? 0 : 1);
        }
        else if (strcmp(op, "-ge") == 0) {
            // Numeric greater than or equal
            exit((atoi(arg1) >= atoi(arg2)) ? 0 : 1);
        }
    }
    
    // Unknown test format
    printf(2, "test: unknown test format\n");
    exit(1);
}