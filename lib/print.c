// lib/print.c - Bootstrap console output and memory utilities for LibOS
// This gives the LibOS "eyes" before a full VFS/console is available
// Also provides compiler-required memory functions (memcpy, memset, memmove)

#include <types.h>
#include <stddef.h>
#include <stdint.h>

// Forward declaration - implemented in syscall.c
extern void sys_cputs(const char *s, int len);

/* ═══════════════════════════════════════════════════════════════════════════
 * Compiler-Required Memory Functions
 *
 * LESSON: The C compiler may generate implicit calls to memcpy, memset, etc.
 * for structure assignments, array initialization, etc. In a freestanding
 * environment (no libc), we must provide these.
 * ═══════════════════════════════════════════════════════════════════════════ */

void *memcpy(void *dst, const void *src, size_t n) {
    uint8_t *d = (uint8_t *)dst;
    const uint8_t *s = (const uint8_t *)src;
    while (n-- > 0) {
        *d++ = *s++;
    }
    return dst;
}

void *memset(void *dst, int c, size_t n) {
    uint8_t *d = (uint8_t *)dst;
    while (n-- > 0) {
        *d++ = (uint8_t)c;
    }
    return dst;
}

void *memmove(void *dst, const void *src, size_t n) {
    uint8_t *d = (uint8_t *)dst;
    const uint8_t *s = (const uint8_t *)src;

    if (d < s) {
        while (n-- > 0) {
            *d++ = *s++;
        }
    } else {
        d += n;
        s += n;
        while (n-- > 0) {
            *--d = *--s;
        }
    }
    return dst;
}

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
