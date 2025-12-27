/**
 * @file fib_big_demo.c
 * @brief Demonstration of big integer Fibonacci computation
 *
 * Uses 256-bit integers when compiler supports them, falls back to 64-bit.
 */
#include <stdio.h>
#include <stdint.h>

/* Check for big integer support */
#ifdef __BITINT_MAXWIDTH__
#if __BITINT_MAXWIDTH__ >= 256
typedef unsigned _BitInt(256) fib_big_t;
#define HAVE_BIG_INT 1
#endif
#endif

#ifndef HAVE_BIG_INT
typedef uint64_t fib_big_t;
#define HAVE_BIG_INT 0
#endif

/**
 * Compute Fibonacci number using big integers
 */
static fib_big_t fib_big(unsigned n) {
    if (n == 0) return 0;
    if (n == 1) return 1;

    fib_big_t a = 0, b = 1;
    for (unsigned i = 2; i <= n; i++) {
        fib_big_t t = a + b;
        a = b;
        b = t;
    }
    return b;
}

#if HAVE_BIG_INT
/**
 * Print 256-bit integer as hex
 */
static void print_big_hex(fib_big_t x) {
    printf("0x");
    for (int i = 3; i >= 0; i--) {
        uint64_t part = (uint64_t)(x >> (i * 64));
        printf("%016llx", (unsigned long long)part);
    }
    printf("\n");
}
#endif

int main(void) {
    unsigned n = 100;
    fib_big_t val = fib_big(n);

#if HAVE_BIG_INT
    printf("fib_big(%u) = ", n);
    print_big_hex(val);
#else
    printf("fib_big(%u) = %llu (64-bit fallback)\n", n, (unsigned long long)val);
#endif

    return 0;
}
