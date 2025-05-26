#include "../simd_dispatch.h"
#include <altivec.h>

typedef __vector unsigned long long v2u64;

uint64_t fib_altivec(uint32_t n) {
  if (n == 0)
    return 0;
  union {
    v2u64 v;
    uint64_t u[2];
  } state;
  state.u[0] = 0;
  state.u[1] = 1;
  for (uint32_t i = 1; i < n; i++) {
    v2u64 shifted = vec_sld(state.v, state.v, 8);
    v2u64 sum = vec_add(state.v, shifted);
    state.v = vec_sld(state.v, sum, 8);
  }
  return state.u[1];
}

uint64_t gcd_altivec(uint64_t a, uint64_t b) {
  while (a != b) {
    if (a > b) {
      v2u64 va = {0, a};
      v2u64 vb = {0, b};
      v2u64 res = vec_sub(va, vb);
      a = vec_extract(res, 1);
    } else {
      v2u64 va = {0, b};
      v2u64 vb = {0, a};
      v2u64 res = vec_sub(va, vb);
      b = vec_extract(res, 1);
    }
  }
  return a;
}
