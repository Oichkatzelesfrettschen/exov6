#include "math_core.h"

#ifdef HAVE_DECIMAL_FLOAT
_Decimal64 phi(void) { return (_Decimal64)1.618033988749895; }

double dec64_to_double(_Decimal64 x) { return (double)x; }
_Decimal64 double_to_dec64(double x) { return (_Decimal64)x; }
#else
// Return the golden ratio constant using binary floating point.
#ifdef USE_SIMD
#  if defined(__SSE2__) && __has_include(<emmintrin.h>)
#    include <emmintrin.h>
#    define SIMD_SSE2 1
#  elif (defined(__ARM_NEON) || defined(__ARM_NEON__)) && __has_include(<arm_neon.h>)
#    include <arm_neon.h>
#    define SIMD_NEON 1
#  endif
#endif

// Return the golden ratio constant.
double phi(void) { return 1.618033988749895; }
#endif

// Compute the n-th Fibonacci number with F(0) = 0 and F(1) = 1.
uint64_t fib(uint32_t n) {
#if defined(SIMD_SSE2)
  if (n == 0)
    return 0;
  union {
    __m128i v;
    uint64_t u[2];
  } state;
  state.u[0] = 0;
  state.u[1] = 1;
  for (uint32_t i = 1; i < n; i++) {
    __m128i shifted = _mm_slli_si128(state.v, 8);
    __m128i sum = _mm_add_epi64(state.v, shifted);
    state.v = _mm_unpackhi_epi64(sum, state.v);
  }
  return state.u[1];
#elif defined(SIMD_NEON)
  if (n == 0)
    return 0;
  uint64x2_t v = {0, 1};
  for (uint32_t i = 1; i < n; i++) {
    uint64x2_t shifted = vextq_u64(v, v, 1);
    uint64x2_t sum = vaddq_u64(v, shifted);
    v = vextq_u64(v, sum, 1);
  }
  return vgetq_lane_u64(v, 1);
#else
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
#endif
}

// Compute the greatest common divisor using Euclid's algorithm.
uint64_t gcd(uint64_t a, uint64_t b) {
#if defined(SIMD_SSE2)
  while (a != b) {
    if (a > b) {
      __m128i va = _mm_set_epi64x(0, a);
      __m128i vb = _mm_set_epi64x(0, b);
      va = _mm_sub_epi64(va, vb);
      a = (uint64_t)_mm_cvtsi128_si64(va);
    } else {
      __m128i va = _mm_set_epi64x(0, b);
      __m128i vb = _mm_set_epi64x(0, a);
      va = _mm_sub_epi64(va, vb);
      b = (uint64_t)_mm_cvtsi128_si64(va);
    }
  }
  return a;
#elif defined(SIMD_NEON)
  while (a != b) {
    if (a > b) {
      uint64x2_t va = {0, a};
      uint64x2_t vb = {0, b};
      uint64x2_t res = vsubq_u64(va, vb);
      a = vgetq_lane_u64(res, 1);
    } else {
      uint64x2_t va = {0, b};
      uint64x2_t vb = {0, a};
      uint64x2_t res = vsubq_u64(va, vb);
      b = vgetq_lane_u64(res, 1);
    }
  }
  return a;
#else
  // Euclid's algorithm without division to avoid libgcc helpers
  while (a != b) {
    if (a > b)
      a -= b;
    else
      b -= a;
  }
  return a;
#endif
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
