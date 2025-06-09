#pragma once
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Available SIMD feature sets supported by the runtime.
 */
enum simd_feature {
  SIMD_FEATURE_NONE = 0, /**< Fallback scalar implementation. */
  SIMD_FEATURE_X87,      /**< x87 FPU instructions. */
  SIMD_FEATURE_MMX,      /**< MMX extension. */
  SIMD_FEATURE_SSE2,     /**< SSE2 instruction set. */
  SIMD_FEATURE_SSE3,     /**< SSE3 instruction set. */
  SIMD_FEATURE_AVX2_FMA, /**< AVX2 with FMA support. */
  SIMD_FEATURE_AVX512,   /**< AVX-512 instruction set. */
  SIMD_FEATURE_NEON,     /**< ARM NEON vector instructions. */
  SIMD_FEATURE_ALTIVEC,  /**< PowerPC AltiVec instructions. */
};

typedef int (*cap_validate_fn_t)(void);
typedef void (*dag_process_fn_t)(void);

/**
 * @brief Register capability and DAG handlers for a SIMD feature.
 *
 * @param feature  SIMD feature being registered.
 * @param cap_fn   Capability validation callback.
 * @param dag_fn   DAG processing callback.
 */
void simd_register(enum simd_feature feature, cap_validate_fn_t cap_fn,
                   dag_process_fn_t dag_fn);

/** Initialise SIMD support and choose the best implementation. */
void simd_init(void);

/** Compute Fibonacci using the best available SIMD implementation. */
uint64_t simd_fib(uint32_t n);

/** Compute greatest common divisor using SIMD when possible. */
uint64_t simd_gcd(uint64_t a, uint64_t b);

/** Validate capabilities for the detected SIMD feature. */
int simd_cap_validate(void);

/** Execute DAG processing for the current SIMD feature. */
void simd_dag_process(void);

#ifdef __cplusplus
}
#endif
