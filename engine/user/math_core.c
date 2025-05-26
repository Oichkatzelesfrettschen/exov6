#include "math_core.h"

// Return the golden ratio constant.
double phi(void) { return 1.618033988749895; }

// Compute the n-th Fibonacci number with F(0) = 0 and F(1) = 1.
uint64_t fib(uint32_t n) {
  if (n == 0)
    return 0;
  uint64_t a = 0;
  uint64_t b = 1;
  for (uint32_t i = 1; i < n; i++) {
    uint64_t t = a + b;
    a = b;
    b = t;
  }
  return b;
}

#ifdef __BITINT_MAXWIDTH__
// 256-bit unsigned integer type for wide Fibonacci calculations.
typedef unsigned _BitInt(256) uint256_t;

uint256_t fib_big(uint32_t n) {
  if (n == 0)
    return 0;
  uint256_t a = 0;
  uint256_t b = 1;
  for (uint32_t i = 1; i < n; i++) {
    uint256_t t = a + b;
    a = b;
    b = t;
  }
  return b;
}
#else
// Fallback implementation using 64-bit integers when _BitInt is unavailable.
uint64_t fib_big(uint32_t n) {
  return fib(n);
}
#endif

// Compute the greatest common divisor using Euclid's algorithm.
uint64_t gcd(uint64_t a, uint64_t b) {
  // Euclid's algorithm without division to avoid libgcc helpers
  while (a != b) {
    if (a > b)
      a -= b;
    else
      b -= a;
  }
  return a;
}

// Round up to the nearest Fibonacci number or integer multiple of phi.
size_t phi_align(size_t n) {
  if (n == 0)
    return 0;

  // Next Fibonacci number >= n.
  size_t f1 = 1, f2 = 1;
  while (f2 < n) {
    size_t t = f2;
    f2 += f1;
    f1 = t;
  }
  size_t fib_val = f2;

  // Smallest integer >= n that is a multiple of phi.
  double phi_val = phi();
  double k = (double)n / phi_val;
  size_t ki = (size_t)k;
  if (k > (double)ki)
    ki += 1;
  double phi_mult = phi_val * (double)ki;
  size_t phi_val_int = (size_t)phi_mult;
  if (phi_mult > (double)phi_val_int)
    phi_val_int += 1;

  return fib_val < phi_val_int ? fib_val : phi_val_int;
}

#ifdef __BITINT_MAXWIDTH__
typedef unsigned _BitInt(256) fib_big_t;

// Compute the n-th Fibonacci number using 256-bit precision.
fib_big_t fib_big(uint32_t n) {
  if (n == 0)
    return 0;
  fib_big_t a = 0;
  fib_big_t b = 1;
  for (uint32_t i = 1; i < n; i++) {
    fib_big_t t = a + b;
    a = b;
    b = t;
  }
  return b;
}
#else
// Fallback when _BitInt is unsupported.
uint64_t fib_big(uint32_t n) { return fib(n); }
#endif
