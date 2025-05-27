#pragma once
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

enum simd_feature {
  SIMD_FEATURE_NONE = 0,
  SIMD_FEATURE_X87,
  SIMD_FEATURE_MMX,
  SIMD_FEATURE_SSE2,
  SIMD_FEATURE_SSE3,
  SIMD_FEATURE_AVX2_FMA,
  SIMD_FEATURE_AVX512,
  SIMD_FEATURE_NEON,
  SIMD_FEATURE_ALTIVEC,
};

typedef int (*cap_validate_fn_t)(void);
typedef void (*dag_process_fn_t)(void);

void simd_register(enum simd_feature feature,
                   cap_validate_fn_t cap_fn,
                   dag_process_fn_t dag_fn);

void simd_init(void);
uint64_t simd_fib(uint32_t n);
uint64_t simd_gcd(uint64_t a, uint64_t b);
int simd_cap_validate(void);
void simd_dag_process(void);

#ifdef __cplusplus
}
#endif
