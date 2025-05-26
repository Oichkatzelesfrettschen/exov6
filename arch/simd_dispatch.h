#pragma once
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

void simd_init(void);
uint64_t simd_fib(uint32_t n);
uint64_t simd_gcd(uint64_t a, uint64_t b);

#ifdef __cplusplus
}
#endif
