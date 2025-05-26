#pragma once
#include "types.h"

#ifdef HAVE_DECIMAL_FLOAT
_Decimal64 phi(void);
double dec64_to_double(_Decimal64 x);
_Decimal64 double_to_dec64(double x);
#else
double phi(void);
static inline double dec64_to_double(double x) { return x; }
static inline double double_to_dec64(double x) { return x; }
#endif
uint64_t fib(uint32_t n);

#ifdef __BITINT_MAXWIDTH__
typedef unsigned _BitInt(256) uint256_t;
uint256_t fib_big(uint32_t n);
#else
uint64_t fib_big(uint32_t n);
#endif
uint64_t gcd(uint64_t a, uint64_t b);
size_t phi_align(size_t n);

#ifdef __BITINT_MAXWIDTH__
typedef unsigned _BitInt(256) fib_big_t;
fib_big_t fib_big(uint32_t n);
#else
uint64_t fib_big(uint32_t n);
#endif
