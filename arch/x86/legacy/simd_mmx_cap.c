#include <mmintrin.h>
#include "../../simd_dispatch.h"

int cap_validate_mmx(void) {
  __m64 z = _mm_setzero_si64();
  return _mm_cvtsi64_si32(z);
}

void dag_process_mmx(void) {
  __m64 a = _mm_set1_pi16(1);
  __m64 b = _mm_add_pi16(a, a);
  (void)b;
  _mm_empty();
}

__attribute__((constructor))
static void register_mmx(void) {
  simd_register(SIMD_FEATURE_MMX, cap_validate_mmx, dag_process_mmx);
}
