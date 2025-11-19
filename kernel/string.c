/**
 * @file string.c
 * @brief Kernel string and memory functions
 *
 * Pure C17 implementations of standard C library functions for kernel use.
 * These are optimized for correctness and simplicity, not maximum performance.
 */

#include "types.h"
#include <stddef.h>
#include <stdint.h>

/**
 * Copy n bytes from src to dst
 * @param dst Destination buffer
 * @param src Source buffer
 * @param n Number of bytes to copy
 * @return Pointer to dst
 */
void *memcpy(void *dst, const void *src, size_t n) {
    const uint8_t *s = src;
    uint8_t *d = dst;

    while (n-- > 0) {
        *d++ = *s++;
    }

    return dst;
}

/**
 * Set n bytes of memory to value c
 * @param s Destination buffer
 * @param c Value to set (converted to unsigned char)
 * @param n Number of bytes to set
 * @return Pointer to s
 */
void *memset(void *s, int c, size_t n) {
    uint8_t *p = s;
    uint8_t val = (uint8_t)c;

    while (n-- > 0) {
        *p++ = val;
    }

    return s;
}

/**
 * Move n bytes from src to dst (handles overlapping regions)
 * @param dst Destination buffer
 * @param src Source buffer
 * @param n Number of bytes to move
 * @return Pointer to dst
 */
void *memmove(void *dst, const void *src, size_t n) {
    const uint8_t *s = src;
    uint8_t *d = dst;

    if (d < s) {
        /* Copy forward */
        while (n-- > 0) {
            *d++ = *s++;
        }
    } else if (d > s) {
        /* Copy backward */
        s += n;
        d += n;
        while (n-- > 0) {
            *--d = *--s;
        }
    }
    /* If d == s, nothing to do */

    return dst;
}

/**
 * Compare two memory regions
 * @param s1 First buffer
 * @param s2 Second buffer
 * @param n Number of bytes to compare
 * @return 0 if equal, <0 if s1 < s2, >0 if s1 > s2
 */
int memcmp(const void *s1, const void *s2, size_t n) {
    const uint8_t *p1 = s1;
    const uint8_t *p2 = s2;

    while (n-- > 0) {
        if (*p1 != *p2) {
            return *p1 - *p2;
        }
        p1++;
        p2++;
    }

    return 0;
}

/**
 * Compare two null-terminated strings
 * @param s1 First string
 * @param s2 Second string
 * @return 0 if equal, <0 if s1 < s2, >0 if s1 > s2
 */
int strcmp(const char *s1, const char *s2) {
    while (*s1 && (*s1 == *s2)) {
        s1++;
        s2++;
    }
    return *(const uint8_t *)s1 - *(const uint8_t *)s2;
}

/**
 * Compare at most n characters of two strings
 * @param s1 First string
 * @param s2 Second string
 * @param n Maximum number of characters to compare
 * @return 0 if equal, <0 if s1 < s2, >0 if s1 > s2
 */
int strncmp(const char *s1, const char *s2, size_t n) {
    while (n && *s1 && (*s1 == *s2)) {
        ++s1;
        ++s2;
        --n;
    }
    if (n == 0) {
        return 0;
    }
    return *(const uint8_t *)s1 - *(const uint8_t *)s2;
}

/**
 * Get length of null-terminated string
 * @param s String
 * @return Length (not including null terminator)
 */
size_t strlen(const char *s) {
    size_t n = 0;
    while (*s++) {
        n++;
    }
    return n;
}

/**
 * Copy null-terminated string
 * @param dst Destination buffer
 * @param src Source string
 * @return Pointer to dst
 */
char *strcpy(char *dst, const char *src) {
    char *d = dst;
    while ((*d++ = *src++)) {
        /* Empty body */
    }
    return dst;
}

/**
 * Copy at most n characters of string
 * @param dst Destination buffer
 * @param src Source string
 * @param n Maximum number of characters to copy
 * @return Pointer to dst
 */
char *strncpy(char *dst, const char *src, size_t n) {
    char *d = dst;
    while (n > 0 && *src) {
        *d++ = *src++;
        n--;
    }
    while (n > 0) {
        *d++ = '\0';
        n--;
    }
    return dst;
}
