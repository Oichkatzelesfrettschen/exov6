#include <immintrin.h>

/**
 * @file simd_avx2_cap.c
 * @brief AVX2 capability checks and simple DAG example.
 */

/** Validate availability of AVX2 instructions. */
int cap_validate_avx2(void) {
  __m256i z = _mm256_setzero_si256();
  return _mm256_extract_epi32(z, 0);
}

/** Minimal DAG processing example for AVX2. */
void dag_process_avx2(void) {
  __m256i a = _mm256_set1_epi64x(1);
  __m256i b = _mm256_add_epi64(a, a);
  (void)b;
}
