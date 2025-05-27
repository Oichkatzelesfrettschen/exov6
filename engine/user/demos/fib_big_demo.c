#include <stdio.h>
#include "math_core.h"

int main(void) {
    unsigned n = 100;
#ifdef __BITINT_MAXWIDTH__
    uint256_t val = fib_big(n);
    printf("fib_big(%u) = 0x", n);
    for (int i = 3; i >= 0; i--) {
        unsigned long long part = (unsigned long long)(val >> (i * 64));
        printf("%016llx", part);
    }
    printf("\n");
#else
    printf("fib_big(%u) = %llu (fallback)\n", n, (unsigned long long)fib_big(n));
#endif
    return 0;
}
