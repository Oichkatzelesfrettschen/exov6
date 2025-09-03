/**
 * expr - Evaluate expression
 * POSIX mandatory utility
 */

#include "types.h"
#include "user.h"

int is_number(char *s) {
    if (*s == '-') s++;
    while (*s) {
        if (*s < '0' || *s > '9') return 0;
        s++;
    }
    return 1;
}

int main(int argc, char *argv[]) {
    if (argc < 2) {
        printf(1, "\n");
        exit(1);
    }
    
    // Simple arithmetic expressions
    if (argc == 4) {
        if (is_number(argv[1]) && is_number(argv[3])) {
            int a = atoi(argv[1]);
            int b = atoi(argv[3]);
            int result = 0;
            
            if (strcmp(argv[2], "+") == 0) {
                result = a + b;
            } else if (strcmp(argv[2], "-") == 0) {
                result = a - b;
            } else if (strcmp(argv[2], "*") == 0) {
                result = a * b;
            } else if (strcmp(argv[2], "/") == 0) {
                if (b == 0) {
                    printf(2, "expr: division by zero\n");
                    exit(2);
                }
                result = a / b;
            } else if (strcmp(argv[2], "%") == 0) {
                if (b == 0) {
                    printf(2, "expr: division by zero\n");
                    exit(2);
                }
                result = a % b;
            }
            
            printf(1, "%d\n", result);
            exit(result == 0 ? 1 : 0);
        }
    }
    
    // String operations
    if (argc == 2) {
        // String length
        printf(1, "%d\n", strlen(argv[1]));
        exit(strlen(argv[1]) == 0 ? 1 : 0);
    }
    
    // String comparison
    if (argc == 4 && strcmp(argv[2], "=") == 0) {
        int equal = strcmp(argv[1], argv[3]) == 0;
        printf(1, "%d\n", equal);
        exit(equal ? 0 : 1);
    }
    
    exit(1);
}
