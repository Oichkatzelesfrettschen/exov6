#include "../simd_dispatch.h"
#include <arm_neon.h>

static int cap_validate_neon(void) { return 1; }
static void dag_process_neon(void) {}

__attribute__((constructor))
static void register_neon(void) {
  simd_register(SIMD_FEATURE_NEON, cap_validate_neon, dag_process_neon);
}

uint64_t fib_neon(uint32_t n) {
  if (n == 0)
    return 0;
  uint64x2_t v = {0, 1};
  for (uint32_t i = 1; i < n; i++) {
    uint64x2_t shifted = vextq_u64(v, v, 1);
    uint64x2_t sum = vaddq_u64(v, shifted);
    v = vextq_u64(v, sum, 1);
  }
  return vgetq_lane_u64(v, 1);
}

uint64_t gcd_neon(uint64_t a, uint64_t b) {
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
}
