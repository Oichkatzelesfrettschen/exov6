#include "simd_dispatch.h"
#include "../tools/phoenix_metrics.h"
#include <stddef.h>
#if defined(__linux__)
#include <sys/auxv.h>
#endif

typedef uint64_t (*fib_fn_t)(uint32_t);
typedef uint64_t (*gcd_fn_t)(uint64_t, uint64_t);

static int cap_validate_scalar(void) { return 0; }
static void dag_process_scalar(void) {}

typedef int (*cap_validate_ptr)(void);
typedef void (*dag_process_ptr)(void);

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
static enum simd_feature detected_feature = SIMD_FEATURE_NONE;

struct simd_entry {
  enum simd_feature feature;
  cap_validate_ptr cap_fn;
  dag_process_ptr dag_fn;
};

#define MAX_SIMD_ENTRIES 8
static struct simd_entry simd_table[MAX_SIMD_ENTRIES];
static unsigned simd_table_len;
static cap_validate_ptr cap_validate_impl = cap_validate_scalar;
static dag_process_ptr dag_process_impl = dag_process_scalar;

void simd_register(enum simd_feature feature,
                   cap_validate_ptr cap_fn,
                   dag_process_ptr dag_fn) {
  if (simd_table_len < MAX_SIMD_ENTRIES) {
    simd_table[simd_table_len].feature = feature;
    simd_table[simd_table_len].cap_fn = cap_fn;
    simd_table[simd_table_len].dag_fn = dag_fn;
    simd_table_len++;
  }
}

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
  int have_sse3 = c & 1u;
  int have_fma = c & (1u << 12);
  int have_avx = c & (1u << 28);
  cpuid_inst(7, &a, &b, &c, &d);
  int have_avx2 = b & (1u << 5);
  int have_avx512f = b & (1u << 16);
  if (have_avx512f) {
    fib_impl = fib_avx;
    gcd_impl = gcd_avx;
    detected_feature = SIMD_FEATURE_AVX512;
    return;
  }
  if (have_avx2 && have_fma && have_avx) {
    fib_impl = fib_avx;
    gcd_impl = gcd_avx;
    detected_feature = SIMD_FEATURE_AVX2_FMA;
    return;
  }
  if (have_sse3) {
    fib_impl = fib_sse2;
    gcd_impl = gcd_sse2;
    detected_feature = SIMD_FEATURE_SSE3;
    return;
  }
  if (d & (1u << 26)) {
    fib_impl = fib_sse2;
    gcd_impl = gcd_sse2;
    detected_feature = SIMD_FEATURE_SSE2;
    return;
  }
  if (d & (1u << 23)) {
    fib_impl = fib_mmx;
    gcd_impl = gcd_mmx;
    detected_feature = SIMD_FEATURE_MMX;
    return;
  }
  fib_impl = fib_x87;
  gcd_impl = gcd_x87;
  detected_feature = SIMD_FEATURE_X87;
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
    detected_feature = SIMD_FEATURE_NEON;
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
    detected_feature = SIMD_FEATURE_ALTIVEC;
    return;
  }
#endif
#endif
  fib_impl = fib_scalar;
  gcd_impl = gcd_scalar;
  detected_feature = SIMD_FEATURE_NONE;
}

void simd_init(void) {
  if (!simd_initialized)
    simd_detect();
  for (unsigned i = 0; i < simd_table_len; i++) {
    if (simd_table[i].feature == detected_feature) {
      cap_validate_impl = simd_table[i].cap_fn;
      dag_process_impl = simd_table[i].dag_fn;
      break;
    }
  }
}

uint64_t simd_fib(uint32_t n) {
  if (!simd_initialized)
    simd_detect();
  if (fib_impl == fib_scalar)
    phoenix_metrics_record_scalar(1);
  else
    phoenix_metrics_record_simd(1);
  return fib_impl(n);
}

uint64_t simd_gcd(uint64_t a, uint64_t b) {
  if (!simd_initialized)
    simd_detect();
  if (gcd_impl == gcd_scalar)
    phoenix_metrics_record_scalar(1);
  else
    phoenix_metrics_record_simd(1);
  return gcd_impl(a, b);
}

int simd_cap_validate(void) {
  if (!simd_initialized)
    simd_init();
  return cap_validate_impl();
}

void simd_dag_process(void) {
  if (!simd_initialized)
    simd_init();
  dag_process_impl();
}
