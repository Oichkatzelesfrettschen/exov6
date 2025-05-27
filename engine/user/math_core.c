#include "math_core.h"

#ifdef HAVE_DECIMAL_FLOAT
// Return the golden ratio constant using a decimal floating literal when
// the compiler supports decimal floats.  The literal uses the `dd` suffix
// for `_Decimal64` precision.
_Decimal64 phi(void) { return 1.618033988749895dd; }

double dec64_to_double(_Decimal64 x) { return (double)x; }
_Decimal64 double_to_dec64(double x) { return (_Decimal64)x; }
#else
// Return the golden ratio constant using binary floating point.
double phi(void) { return 1.618033988749895; }
#endif

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
#ifdef HAVE_DECIMAL_FLOAT
  double phi_val = dec64_to_double(phi());
#else
  double phi_val = phi();
#endif
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
