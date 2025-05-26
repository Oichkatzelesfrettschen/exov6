#include "../simd_dispatch.h"
#include <emmintrin.h>

uint64_t fib_sse2(uint32_t n) {
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
}

uint64_t gcd_sse2(uint64_t a, uint64_t b) {
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
}
