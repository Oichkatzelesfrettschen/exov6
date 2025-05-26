#include "../simd_dispatch.h"

uint64_t fib_x87(uint32_t n) {
  if (n == 0)
    return 0;
  uint64_t a = 0, b = 1;
  for (uint32_t i = 1; i < n; i++) {
    uint64_t t = a + b;
    a = b;
    b = t;
  }
  return b;
}

uint64_t gcd_x87(uint64_t a, uint64_t b) {
  while (a != b) {
    if (a > b)
      a -= b;
    else
      b -= a;
  }
  return a;
}
