/**
 * read - Read a line from standard input
 * POSIX mandatory utility
 */

#include "types.h"
#include "user.h"

int main(int argc, char *argv[]) {
    char buf[256];
    int n;
    int i = 0;
    char c;
    
    // Read one character at a time until newline
    while ((n = read(0, &c, 1)) > 0 && c != '\n' && i < 255) {
        buf[i++] = c;
    }
    buf[i] = '\0';
    
    if (n < 0) {
        exit(1);
    }
    
    // In shell context, would assign to variable
    // For now, just echo what was read
    if (argc > 1) {
        printf(1, "%s=%s\n", argv[1], buf);
    } else {
        printf(1, "%s\n", buf);
    }
    
    exit(0);
}
