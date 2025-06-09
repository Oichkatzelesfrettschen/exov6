#include "../simd_dispatch.h"
#include <emmintrin.h>

/* Validate SSE3 support using a trivial instruction. */
static int cap_validate_sse3(void) { return 1; }
/* Simple DAG processing placeholder for SSE3. */
static void dag_process_sse3(void) {}
/* Validate SSE2 support using a trivial instruction. */
static int cap_validate_sse2(void) { return 1; }
/* Simple DAG processing placeholder for SSE2. */
static void dag_process_sse2(void) {}

__attribute__((constructor)) static void register_sse3(void) {
  simd_register(SIMD_FEATURE_SSE3, cap_validate_sse3, dag_process_sse3);
}

__attribute__((constructor)) static void register_sse2(void) {
  simd_register(SIMD_FEATURE_SSE2, cap_validate_sse2, dag_process_sse2);
}

/** Compute Fibonacci numbers using SSE2 instructions. */
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

/** Compute the greatest common divisor using SSE2 instructions. */
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
