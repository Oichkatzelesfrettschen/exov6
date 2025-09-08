/**
 * @file q16_fixed.c
 * @brief Q16.16 Fixed-Point Arithmetic for Kernel
 * 
 * Implements high-performance fixed-point arithmetic using Q16.16 format
 * (16 bits integer, 16 bits fraction) with SIMD optimizations.
 * 
 * Based on Intel x86_64 ISA for optimal performance:
 * - SSE2/AVX for parallel operations
 * - Careful cycle counting from Intel manual
 * - No FPU dependencies for kernel safety
 */

#include <stdint.h>
#include <stdbool.h>
#include "defs.h"
#include "types.h"

/* ============================================================================
 * Q16.16 Fixed-Point Type Definitions
 * ============================================================================ */

typedef int32_t q16_t;      /* Q16.16 fixed-point (signed) */
typedef uint32_t uq16_t;    /* Q16.16 fixed-point (unsigned) */
typedef int64_t q32_t;      /* Q32.32 for intermediate calculations */

/* Fixed-point constants */
#define Q16_ONE         (1 << 16)           /* 1.0 in Q16.16 */
#define Q16_HALF        (1 << 15)           /* 0.5 in Q16.16 */
#define Q16_FRAC_MASK   ((1 << 16) - 1)     /* Fractional part mask */
#define Q16_INT_MASK    (~Q16_FRAC_MASK)    /* Integer part mask */
#define Q16_SHIFT       16                   /* Fractional bits */

/* Mathematical constants in Q16.16 */
#define Q16_PI          205887  /* π = 3.141592653... */
#define Q16_E           178145  /* e = 2.718281828... */
#define Q16_SQRT2       92682   /* √2 = 1.414213562... */
#define Q16_PHI         106039  /* φ = 1.618033988... (golden ratio) */
#define Q16_LN2         45426   /* ln(2) = 0.693147180... */

/* ============================================================================
 * Basic Arithmetic Operations (3-10 cycles each)
 * ============================================================================ */

/**
 * Convert integer to Q16.16
 * Cost: 1 cycle (shift)
 */
static inline q16_t q16_from_int(int32_t x) {
    return x << Q16_SHIFT;
}

/**
 * Convert Q16.16 to integer (truncate)
 * Cost: 1 cycle (shift)
 */
static inline int32_t q16_to_int(q16_t x) {
    return x >> Q16_SHIFT;
}

/**
 * Convert Q16.16 to integer (round)
 * Cost: 3 cycles (add + shift)
 */
static inline int32_t q16_to_int_round(q16_t x) {
    return (x + Q16_HALF) >> Q16_SHIFT;
}

/**
 * Add two Q16.16 numbers
 * Cost: 1 cycle
 */
static inline q16_t q16_add(q16_t a, q16_t b) {
    return a + b;
}

/**
 * Subtract two Q16.16 numbers
 * Cost: 1 cycle
 */
static inline q16_t q16_sub(q16_t a, q16_t b) {
    return a - b;
}

/**
 * Multiply two Q16.16 numbers
 * Cost: 3-5 cycles (mul + shift)
 */
static inline q16_t q16_mul(q16_t a, q16_t b) {
    /* Use 64-bit intermediate to prevent overflow */
    int64_t result = ((int64_t)a * b) >> Q16_SHIFT;
    return (q16_t)result;
}

/**
 * Divide two Q16.16 numbers
 * Cost: 20-30 cycles (div is expensive)
 */
static inline q16_t q16_div(q16_t a, q16_t b) {
    if (b == 0) return 0;  /* Avoid division by zero */
    int64_t temp = ((int64_t)a << Q16_SHIFT) / b;
    return (q16_t)temp;
}

/**
 * Negate Q16.16 number
 * Cost: 1 cycle
 */
static inline q16_t q16_neg(q16_t x) {
    return -x;
}

/**
 * Absolute value
 * Cost: 2-3 cycles (branch-free)
 */
static inline q16_t q16_abs(q16_t x) {
    int32_t mask = x >> 31;  /* Sign extend */
    return (x + mask) ^ mask;
}

/* ============================================================================
 * Advanced Mathematical Functions
 * ============================================================================ */

/**
 * Square root using Newton-Raphson iteration
 * Cost: ~50 cycles
 */
q16_t q16_sqrt(q16_t x) {
    if (x <= 0) return 0;
    
    /* Initial guess: use integer square root as starting point */
    uint32_t n = (uint32_t)x;
    uint32_t guess = n >> 1;
    
    if (guess == 0) guess = 1;
    
    /* Newton-Raphson iterations (converges quickly) */
    for (int i = 0; i < 8; i++) {
        uint32_t new_guess = (guess + n / guess) >> 1;
        if (new_guess >= guess) break;
        guess = new_guess;
    }
    
    /* Scale result back to Q16.16 */
    return (q16_t)(guess << 8);  /* Approximation */
}

/**
 * Reciprocal (1/x) using Newton-Raphson
 * Cost: ~40 cycles
 */
q16_t q16_recip(q16_t x) {
    if (x == 0) return 0;
    
    /* Newton-Raphson for 1/x: x_{n+1} = x_n * (2 - a * x_n) */
    q16_t guess = Q16_ONE;  /* Initial guess = 1.0 */
    
    for (int i = 0; i < 4; i++) {
        q16_t two = q16_from_int(2);
        q16_t ax = q16_mul(x, guess);
        q16_t factor = q16_sub(two, ax);
        guess = q16_mul(guess, factor);
    }
    
    return guess;
}

/**
 * Sine approximation using Taylor series
 * Cost: ~100 cycles
 */
q16_t q16_sin(q16_t x) {
    /* Reduce angle to [-π, π] */
    while (x > Q16_PI) x -= 2 * Q16_PI;
    while (x < -Q16_PI) x += 2 * Q16_PI;
    
    /* Taylor series: sin(x) = x - x³/3! + x⁵/5! - x⁷/7! + ... */
    q16_t x2 = q16_mul(x, x);
    q16_t x3 = q16_mul(x2, x);
    q16_t x5 = q16_mul(x3, x2);
    q16_t x7 = q16_mul(x5, x2);
    
    /* Precomputed factorial reciprocals in Q16.16 */
    const q16_t inv3fact = 10923;   /* 1/6 */
    const q16_t inv5fact = 546;     /* 1/120 */
    const q16_t inv7fact = 13;      /* 1/5040 */
    
    q16_t result = x;
    result = q16_sub(result, q16_mul(x3, inv3fact));
    result = q16_add(result, q16_mul(x5, inv5fact));
    result = q16_sub(result, q16_mul(x7, inv7fact));
    
    return result;
}

/**
 * Cosine approximation
 * Cost: ~100 cycles
 */
q16_t q16_cos(q16_t x) {
    /* cos(x) = sin(x + π/2) */
    return q16_sin(x + (Q16_PI >> 1));
}

/**
 * Exponential using binary exponentiation
 * Cost: ~150 cycles
 */
q16_t q16_exp(q16_t x) {
    /* e^x using Taylor series for small x, otherwise decompose */
    if (x == 0) return Q16_ONE;
    
    /* For large values, use e^x = e^(n + f) = e^n * e^f */
    int32_t n = q16_to_int(x);
    q16_t frac = x & Q16_FRAC_MASK;
    
    /* Taylor series for e^f where f is fractional part */
    q16_t result = Q16_ONE;
    q16_t term = frac;
    
    for (int i = 1; i < 8; i++) {
        result = q16_add(result, term);
        term = q16_mul(term, q16_div(frac, q16_from_int(i + 1)));
    }
    
    /* Multiply by e^n using repeated squaring */
    if (n > 0) {
        q16_t e_power = Q16_E;
        while (n > 0) {
            if (n & 1) result = q16_mul(result, e_power);
            e_power = q16_mul(e_power, e_power);
            n >>= 1;
        }
    }
    
    return result;
}

/* ============================================================================
 * SIMD Optimized Operations (SSE2/AVX)
 * ============================================================================ */

#ifdef __SSE2__
#include <emmintrin.h>

/**
 * Add 4 Q16.16 values in parallel
 * Cost: 1 cycle throughput
 */
void q16_add_vec4(q16_t *result, const q16_t *a, const q16_t *b) {
    __m128i va = _mm_load_si128((__m128i*)a);
    __m128i vb = _mm_load_si128((__m128i*)b);
    __m128i vr = _mm_add_epi32(va, vb);
    _mm_store_si128((__m128i*)result, vr);
}

/**
 * Multiply 4 Q16.16 values in parallel
 * Cost: 3-5 cycles throughput
 */
void q16_mul_vec4(q16_t *result, const q16_t *a, const q16_t *b) {
    __m128i va = _mm_load_si128((__m128i*)a);
    __m128i vb = _mm_load_si128((__m128i*)b);
    
    /* Multiply and shift - requires some manipulation for Q16.16 */
    __m128i lo = _mm_mullo_epi32(va, vb);
    __m128i hi = _mm_mulhi_epi32(va, vb);
    
    /* Combine and shift right by 16 */
    __m128i result_lo = _mm_srli_epi32(lo, 16);
    __m128i result_hi = _mm_slli_epi32(hi, 16);
    __m128i vr = _mm_or_si128(result_lo, result_hi);
    
    _mm_store_si128((__m128i*)result, vr);
}

/**
 * Compute dot product of two Q16.16 vectors
 * Cost: ~10 cycles for 4 elements
 */
q16_t q16_dot_vec4(const q16_t *a, const q16_t *b) {
    __m128i va = _mm_load_si128((__m128i*)a);
    __m128i vb = _mm_load_si128((__m128i*)b);
    
    /* Multiply elements */
    __m128i prod = _mm_mullo_epi32(va, vb);
    
    /* Horizontal add to sum all elements */
    __m128i sum1 = _mm_hadd_epi32(prod, prod);
    __m128i sum2 = _mm_hadd_epi32(sum1, sum1);
    
    /* Extract result and shift for Q16.16 */
    int32_t result = _mm_cvtsi128_si32(sum2);
    return result >> Q16_SHIFT;
}

#endif /* __SSE2__ */

/* ============================================================================
 * Matrix Operations (for transforms and graphics)
 * ============================================================================ */

/**
 * 2x2 matrix multiply in Q16.16
 * Cost: ~20 cycles
 */
void q16_mat2x2_mul(q16_t *result, const q16_t *a, const q16_t *b) {
    /* result = a * b for 2x2 matrices */
    result[0] = q16_add(q16_mul(a[0], b[0]), q16_mul(a[1], b[2]));
    result[1] = q16_add(q16_mul(a[0], b[1]), q16_mul(a[1], b[3]));
    result[2] = q16_add(q16_mul(a[2], b[0]), q16_mul(a[3], b[2]));
    result[3] = q16_add(q16_mul(a[2], b[1]), q16_mul(a[3], b[3]));
}

/**
 * 3x3 matrix multiply in Q16.16
 * Cost: ~50 cycles
 */
void q16_mat3x3_mul(q16_t *result, const q16_t *a, const q16_t *b) {
    for (int i = 0; i < 3; i++) {
        for (int j = 0; j < 3; j++) {
            q16_t sum = 0;
            for (int k = 0; k < 3; k++) {
                sum = q16_add(sum, q16_mul(a[i*3 + k], b[k*3 + j]));
            }
            result[i*3 + j] = sum;
        }
    }
}

/* ============================================================================
 * Special Functions for Kernel Use
 * ============================================================================ */

/**
 * Linear interpolation (lerp)
 * Cost: 5 cycles
 */
q16_t q16_lerp(q16_t a, q16_t b, q16_t t) {
    /* result = a + t * (b - a) */
    q16_t diff = q16_sub(b, a);
    q16_t scaled = q16_mul(diff, t);
    return q16_add(a, scaled);
}

/**
 * Clamp value to range
 * Cost: 2-3 cycles (branch-free)
 */
q16_t q16_clamp(q16_t x, q16_t min, q16_t max) {
    x = (x < min) ? min : x;
    x = (x > max) ? max : x;
    return x;
}

/**
 * Fast log2 approximation
 * Cost: ~30 cycles
 */
q16_t q16_log2(q16_t x) {
    if (x <= 0) return 0;
    
    /* Count leading zeros to find integer part */
    int32_t int_part = 0;
    uint32_t val = (uint32_t)x;
    
    while (val >= (2 << Q16_SHIFT)) {
        val >>= 1;
        int_part++;
    }
    
    /* Linear approximation for fractional part */
    q16_t frac = (q16_t)(val - Q16_ONE);
    
    return q16_from_int(int_part) + frac;
}

/**
 * Power function x^y
 * Cost: ~200 cycles
 */
q16_t q16_pow(q16_t x, q16_t y) {
    /* x^y = exp(y * ln(x)) */
    if (x <= 0) return 0;
    
    /* Use log2 and exp2 for efficiency */
    q16_t log_x = q16_log2(x);
    q16_t y_log_x = q16_mul(y, log_x);
    
    /* exp2(x) = 2^x using binary exponentiation */
    int32_t int_part = q16_to_int(y_log_x);
    q16_t frac_part = y_log_x & Q16_FRAC_MASK;
    
    /* 2^frac using Taylor series */
    q16_t result = Q16_ONE;
    q16_t ln2_frac = q16_mul(Q16_LN2, frac_part);
    result = q16_exp(ln2_frac);
    
    /* Multiply by 2^int_part */
    if (int_part > 0) {
        result <<= int_part;
    } else if (int_part < 0) {
        result >>= -int_part;
    }
    
    return result;
}

/* ============================================================================
 * Conversion Utilities
 * ============================================================================ */

/**
 * Convert Q16.16 to string (for debugging)
 * Returns static buffer - not thread safe
 */
const char* q16_to_string(q16_t x) {
    static char buffer[32];
    int32_t integer = q16_to_int(x);
    uint32_t frac = (x & Q16_FRAC_MASK) * 10000 / Q16_ONE;
    
    /* Simple sprintf replacement for kernel */
    int pos = 0;
    if (x < 0) {
        buffer[pos++] = '-';
        integer = -integer;
        frac = Q16_ONE - frac;
    }
    
    /* Integer part */
    if (integer == 0) {
        buffer[pos++] = '0';
    } else {
        char temp[16];
        int i = 0;
        while (integer > 0) {
            temp[i++] = '0' + (integer % 10);
            integer /= 10;
        }
        while (i > 0) {
            buffer[pos++] = temp[--i];
        }
    }
    
    /* Decimal point and fraction */
    buffer[pos++] = '.';
    for (int i = 3; i >= 0; i--) {
        buffer[pos + i] = '0' + (frac % 10);
        frac /= 10;
    }
    pos += 4;
    
    buffer[pos] = '\0';
    return buffer;
}

/* ============================================================================
 * Test and Benchmark Functions
 * ============================================================================ */

#ifdef Q16_ENABLE_TESTS

void q16_run_tests(void) {
    /* Test basic arithmetic */
    q16_t a = q16_from_int(5);
    q16_t b = q16_from_int(3);
    
    q16_t sum = q16_add(a, b);  /* Should be 8 */
    q16_t diff = q16_sub(a, b); /* Should be 2 */
    q16_t prod = q16_mul(a, b); /* Should be 15 */
    q16_t quot = q16_div(a, b); /* Should be ~1.666 */
    
    /* Test trigonometric functions */
    q16_t angle = Q16_PI / 4;   /* 45 degrees */
    q16_t sine = q16_sin(angle);   /* Should be ~0.707 */
    q16_t cosine = q16_cos(angle); /* Should be ~0.707 */
    
    /* Test square root */
    q16_t four = q16_from_int(4);
    q16_t sqrt4 = q16_sqrt(four);  /* Should be 2 */
    
    /* Print results (would use kernel printf) */
    cprintf("Q16.16 Tests:\n");
    cprintf("  5 + 3 = %s\n", q16_to_string(sum));
    cprintf("  5 - 3 = %s\n", q16_to_string(diff));
    cprintf("  5 * 3 = %s\n", q16_to_string(prod));
    cprintf("  5 / 3 = %s\n", q16_to_string(quot));
    cprintf("  sin(π/4) = %s\n", q16_to_string(sine));
    cprintf("  cos(π/4) = %s\n", q16_to_string(cosine));
    cprintf("  sqrt(4) = %s\n", q16_to_string(sqrt4));
}

#endif /* Q16_ENABLE_TESTS */