#include "simd_dispatch.h"
#include <stddef.h>
#if defined(__linux__)
#include <sys/auxv.h>
#endif

typedef uint64_t (*fib_fn_t)(uint32_t);
typedef uint64_t (*gcd_fn_t)(uint64_t, uint64_t);

static uint64_t fib_scalar(uint32_t n) {
  if (n == 0)
    return 0;
  uint64_t a = 0, b = 1;
  for (uint32_t i = 1; i < n; i++) {
    uint64_t t = a + b;
    a = b;
    b = t;
  }
  return b;
}

static uint64_t gcd_scalar(uint64_t a, uint64_t b) {
  while (a != b) {
    if (a > b)
      a -= b;
    else
      b -= a;
  }
  return a;
}

/* Forward declarations for architecture specific implementations */
uint64_t fib_x87(uint32_t n);
uint64_t gcd_x87(uint64_t a, uint64_t b);
uint64_t fib_mmx(uint32_t n);
uint64_t gcd_mmx(uint64_t a, uint64_t b);
uint64_t fib_sse2(uint32_t n);
uint64_t gcd_sse2(uint64_t a, uint64_t b);
uint64_t fib_avx(uint32_t n);
uint64_t gcd_avx(uint64_t a, uint64_t b);
uint64_t fib_neon(uint32_t n);
uint64_t gcd_neon(uint64_t a, uint64_t b);
uint64_t fib_altivec(uint32_t n);
uint64_t gcd_altivec(uint64_t a, uint64_t b);

static fib_fn_t fib_impl = fib_scalar;
static gcd_fn_t gcd_impl = gcd_scalar;
static int simd_initialized = 0;

#if defined(__x86_64__) || defined(__i386__)
static inline void cpuid_inst(uint32_t leaf, uint32_t *a, uint32_t *b, uint32_t *c,
                              uint32_t *d) {
  __asm__ volatile("cpuid" : "=a"(*a), "=b"(*b), "=c"(*c), "=d"(*d)
                   : "0"(leaf));
}
#endif

static void simd_detect(void) {
  simd_initialized = 1;
#if defined(__x86_64__) || defined(__i386__)
  uint32_t a, b, c, d;
  cpuid_inst(1, &a, &b, &c, &d);
  if (c & (1u << 28)) {
    fib_impl = fib_avx;
    gcd_impl = gcd_avx;
    return;
  }
  if (d & (1u << 26)) {
    fib_impl = fib_sse2;
    gcd_impl = gcd_sse2;
    return;
  }
  if (d & (1u << 23)) {
    fib_impl = fib_mmx;
    gcd_impl = gcd_mmx;
    return;
  }
  fib_impl = fib_x87;
  gcd_impl = gcd_x87;
#elif defined(__arm__) || defined(__aarch64__)
#if defined(__linux__)
#ifndef AT_HWCAP
#define AT_HWCAP 16
#endif
#ifndef HWCAP_NEON
#define HWCAP_NEON (1 << 12)
#endif
  unsigned long hwcap = getauxval(AT_HWCAP);
  if (hwcap & HWCAP_NEON) {
    fib_impl = fib_neon;
    gcd_impl = gcd_neon;
    return;
  }
#endif
#elif defined(__powerpc__) || defined(__powerpc64__)
#if defined(__linux__)
#ifndef AT_HWCAP
#define AT_HWCAP 16
#endif
#ifndef HWCAP_ALTIVEC
#define HWCAP_ALTIVEC (1 << 28)
#endif
  unsigned long hwcap = getauxval(AT_HWCAP);
  if (hwcap & HWCAP_ALTIVEC) {
    fib_impl = fib_altivec;
    gcd_impl = gcd_altivec;
    return;
  }
#endif
#endif
  fib_impl = fib_scalar;
  gcd_impl = gcd_scalar;
}

void simd_init(void) {
  if (!simd_initialized)
    simd_detect();
}

uint64_t simd_fib(uint32_t n) {
  if (!simd_initialized)
    simd_detect();
  return fib_impl(n);
}

uint64_t simd_gcd(uint64_t a, uint64_t b) {
  if (!simd_initialized)
    simd_detect();
  return gcd_impl(a, b);
}
