#pragma once
#include "types.h"

double phi(void);
uint64_t fib(uint32_t n);
uint64_t gcd(uint64_t a, uint64_t b);
size_t phi_align(size_t n);

#ifdef __BITINT_MAXWIDTH__
typedef unsigned _BitInt(256) fib_big_t;
fib_big_t fib_big(uint32_t n);
#else
uint64_t fib_big(uint32_t n);
#endif
