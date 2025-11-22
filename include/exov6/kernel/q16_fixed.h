/**
 * @file q16_fixed.h
 * @brief Q16.16 Fixed-Point Arithmetic Header
 * 
 * Public interface for kernel fixed-point arithmetic.
 * Provides safe, fast math without FPU dependencies.
 */

#ifndef Q16_FIXED_H
#define Q16_FIXED_H

#include <stdint.h>
#include <stdbool.h>

/* ============================================================================
 * Type Definitions
 * ============================================================================ */

typedef int32_t q16_t;      /* Q16.16 fixed-point (signed) */
typedef uint32_t uq16_t;    /* Q16.16 fixed-point (unsigned) */

/* Fixed-point constants */
#define Q16_ONE         (1 << 16)           /* 1.0 in Q16.16 */
#define Q16_HALF        (1 << 15)           /* 0.5 in Q16.16 */
#define Q16_SHIFT       16                   /* Fractional bits */

/* Mathematical constants */
#define Q16_PI          205887  /* π = 3.141592653... */
#define Q16_E           178145  /* e = 2.718281828... */
#define Q16_SQRT2       92682   /* √2 = 1.414213562... */
#define Q16_PHI         106039  /* φ = 1.618033988... (golden ratio) */
#define Q16_LN2         45426   /* ln(2) = 0.693147180... */

/* ============================================================================
 * Basic Operations (inline for performance)
 * ============================================================================ */

/* Convert integer to Q16.16 */
static inline q16_t q16_from_int(int32_t x) {
    return x << Q16_SHIFT;
}

/* Convert Q16.16 to integer (truncate) */
static inline int32_t q16_to_int(q16_t x) {
    return x >> Q16_SHIFT;
}

/* Convert Q16.16 to integer (round) */
static inline int32_t q16_to_int_round(q16_t x) {
    return (x + Q16_HALF) >> Q16_SHIFT;
}

/* Basic arithmetic */
static inline q16_t q16_add(q16_t a, q16_t b) { return a + b; }
static inline q16_t q16_sub(q16_t a, q16_t b) { return a - b; }
static inline q16_t q16_neg(q16_t x) { return -x; }

/* Multiply two Q16.16 numbers */
static inline q16_t q16_mul(q16_t a, q16_t b) {
    return (q16_t)(((int64_t)a * b) >> Q16_SHIFT);
}

/* Divide two Q16.16 numbers */
static inline q16_t q16_div(q16_t a, q16_t b) {
    if (b == 0) return 0;
    return (q16_t)(((int64_t)a << Q16_SHIFT) / b);
}

/* Absolute value (branch-free) */
static inline q16_t q16_abs(q16_t x) {
    int32_t mask = x >> 31;
    return (x + mask) ^ mask;
}

/* Min/Max operations */
static inline q16_t q16_min(q16_t a, q16_t b) {
    return (a < b) ? a : b;
}

static inline q16_t q16_max(q16_t a, q16_t b) {
    return (a > b) ? a : b;
}

/* ============================================================================
 * Advanced Functions (implemented in q16_fixed.c)
 * ============================================================================ */

/* Mathematical functions */
q16_t q16_sqrt(q16_t x);
q16_t q16_recip(q16_t x);
q16_t q16_sin(q16_t x);
q16_t q16_cos(q16_t x);
q16_t q16_exp(q16_t x);
q16_t q16_log2(q16_t x);
q16_t q16_pow(q16_t x, q16_t y);

/* Utility functions */
q16_t q16_lerp(q16_t a, q16_t b, q16_t t);
q16_t q16_clamp(q16_t x, q16_t min, q16_t max);
const char* q16_to_string(q16_t x);

/* Matrix operations */
void q16_mat2x2_mul(q16_t *result, const q16_t *a, const q16_t *b);
void q16_mat3x3_mul(q16_t *result, const q16_t *a, const q16_t *b);

/* SIMD operations (if available) */
#ifdef __SSE2__
void q16_add_vec4(q16_t *result, const q16_t *a, const q16_t *b);
void q16_mul_vec4(q16_t *result, const q16_t *a, const q16_t *b);
q16_t q16_dot_vec4(const q16_t *a, const q16_t *b);
#endif

/* ============================================================================
 * Conversion Macros
 * ============================================================================ */

/* Convert from float (compile-time only) */
#define Q16_FROM_FLOAT(f)   ((q16_t)((f) * Q16_ONE))

/* Convert to float (for debugging only - avoid in kernel) */
#define Q16_TO_FLOAT(x)     ((float)(x) / Q16_ONE)

/* Create Q16.16 from integer and fraction parts */
#define Q16_MAKE(i, f)      (((i) << Q16_SHIFT) | ((f) & 0xFFFF))

/* Extract integer part */
#define Q16_INT_PART(x)     ((x) >> Q16_SHIFT)

/* Extract fractional part */
#define Q16_FRAC_PART(x)    ((x) & 0xFFFF)

/* ============================================================================
 * Fast Approximations (for real-time use)
 * ============================================================================ */

/**
 * Fast reciprocal approximation (1-2 iterations)
 * Good for ~12 bits of precision
 */
static inline q16_t q16_fast_recip(q16_t x) {
    if (x == 0) return 0;
    
    /* Initial approximation */
    q16_t guess = (3 * Q16_ONE - x) >> 1;
    
    /* One Newton iteration */
    q16_t two = q16_from_int(2);
    q16_t ax = q16_mul(x, guess);
    q16_t factor = q16_sub(two, ax);
    return q16_mul(guess, factor);
}

/**
 * Fast square root approximation
 * Good for ~10 bits of precision
 */
static inline q16_t q16_fast_sqrt(q16_t x) {
    if (x <= 0) return 0;
    
    /* Approximate using bit manipulation */
    uint32_t n = (uint32_t)x;
    uint32_t guess = n;
    
    /* Fast convergence using bit shifts */
    guess = (guess + Q16_ONE) >> 1;
    guess = (guess + q16_div(x, guess)) >> 1;
    guess = (guess + q16_div(x, guess)) >> 1;
    
    return (q16_t)guess;
}

/* ============================================================================
 * Beatty Sequence Support (for scheduler)
 * ============================================================================ */

/**
 * Generate Beatty sequence element B_n = floor(n * φ)
 * where φ is the golden ratio
 */
static inline uint32_t q16_beatty_golden(uint32_t n) {
    q16_t n_fixed = q16_from_int(n);
    q16_t result = q16_mul(n_fixed, Q16_PHI);
    return (uint32_t)q16_to_int(result);
}

/**
 * Generate Beatty sequence with custom irrational
 */
static inline uint32_t q16_beatty(uint32_t n, q16_t alpha) {
    q16_t n_fixed = q16_from_int(n);
    q16_t result = q16_mul(n_fixed, alpha);
    return (uint32_t)q16_to_int(result);
}

/* ============================================================================
 * Testing Support
 * ============================================================================ */

#ifdef Q16_ENABLE_TESTS
void q16_run_tests(void);
#endif

#endif /* Q16_FIXED_H */
