// lib/print.c - Bootstrap console output for LibOS
// This gives the LibOS "eyes" before a full VFS/console is available

#include <types.h>

// Forward declaration - implemented in syscall.c
extern void sys_cputs(const char *s, int len);

// Calculate string length
static int strlen(const char *s) {
    int len = 0;
    while (s[len])
        len++;
    return len;
}

// Print a string to the console
void print(const char *s) {
    sys_cputs(s, strlen(s));
}

// Print a string with explicit length
void printn(const char *s, int len) {
    sys_cputs(s, len);
}

// Print a single character
void printc(char c) {
    sys_cputs(&c, 1);
}

// Print an unsigned integer in decimal
void print_uint(uint64 n) {
    char buf[21];  // Max 20 digits for uint64 + null
    int i = 20;
    buf[i] = '\0';

    if (n == 0) {
        sys_cputs("0", 1);
        return;
    }

    while (n > 0) {
        buf[--i] = '0' + (n % 10);
        n /= 10;
    }

    sys_cputs(&buf[i], 20 - i);
}

// Print an unsigned integer in hexadecimal
void print_hex(uint64 n) {
    static const char hex[] = "0123456789abcdef";
    char buf[19];  // "0x" + 16 hex digits + null
    int i = 18;
    buf[i] = '\0';

    if (n == 0) {
        sys_cputs("0x0", 3);
        return;
    }

    while (n > 0) {
        buf[--i] = hex[n & 0xf];
        n >>= 4;
    }
    buf[--i] = 'x';
    buf[--i] = '0';

    sys_cputs(&buf[i], 18 - i);
}
