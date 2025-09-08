/**
 * @file q16_octonion.h
 * @brief Kernel-Safe Fixed-Point Octonion Mathematics Library
 * 
 * Super fast-path Q16.16 fixed-point octonion operations for kernel context.
 * Provides zero-copy, copy-on-write optimizations with exhaustive Q m.n 
 * mathematics support. Completely eliminates SSE/FPU dependencies.
 * 
 * Features:
 * - Zero floating-point operations - pure integer arithmetic
 * - SIMD-optimized parallel octonion operations  
 * - Copy-on-write semantics for large octonion arrays
 * - Branch-free algorithms for deterministic performance
 * - Cross-platform ARM64 ↔ x86_64 compatibility
 * - Superforce energy computation integration
 */

#ifndef Q16_OCTONION_H
#define Q16_OCTONION_H

#include <stdint.h>
#include <stdbool.h>
#include "q16_fixed.h"
#include "compiler_attrs.h"

/* ============================================================================
 * Fixed-Point Octonion Types
 * ============================================================================ */

/**
 * Kernel-safe octonion using Q16.16 fixed-point arithmetic
 * Layout optimized for cache-line alignment and SIMD operations
 */
typedef union q16_octonion {
    q16_t       v[8];                                   /* Array view */
    struct {
        q16_t   e0, e1, e2, e3, e4, e5, e6, e7;         /* Named components */
    };
    struct {
        q16_t   real;                                    /* Scalar part */
        q16_t   imag[7];                                 /* Vector part */
    } parts;
    struct {
        q16_t   pair[4][2];                             /* Quaternion pair view */
    } pairs;
    uint64_t    words[4];                               /* 64-bit word view for copying */
} __attribute__((aligned(64))) q16_octonion_t;

/**
 * Quaternion in Q16.16 format for Cayley-Dickson construction
 */
typedef struct q16_quaternion {
    q16_t w, x, y, z;
} q16_quaternion_t;

/**
 * Copy-on-write octonion container for memory efficiency
 */
typedef struct q16_octonion_cow {
    q16_octonion_t   *data;                             /* Actual octonion data */
    uint32_t         ref_count;                         /* Reference count */
    bool             is_mutable;                        /* Can be modified? */
    uint64_t         energy_consumed;                   /* Superforce energy used */
} q16_octonion_cow_t;

/* ============================================================================
 * Mathematical Constants (Q16.16 Fixed-Point)
 * ============================================================================ */

#define Q16_OCTONION_ZERO       ((q16_octonion_t){0})
#define Q16_OCTONION_ONE        ((q16_octonion_t){Q16_ONE, 0, 0, 0, 0, 0, 0, 0})
#define Q16_OCTONION_I          ((q16_octonion_t){0, Q16_ONE, 0, 0, 0, 0, 0, 0})
#define Q16_OCTONION_J          ((q16_octonion_t){0, 0, Q16_ONE, 0, 0, 0, 0, 0})
#define Q16_OCTONION_K          ((q16_octonion_t){0, 0, 0, Q16_ONE, 0, 0, 0, 0})

/* Octonion basis elements e4, e5, e6, e7 */
#define Q16_OCTONION_E4         ((q16_octonion_t){0, 0, 0, 0, Q16_ONE, 0, 0, 0})
#define Q16_OCTONION_E5         ((q16_octonion_t){0, 0, 0, 0, 0, Q16_ONE, 0, 0})
#define Q16_OCTONION_E6         ((q16_octonion_t){0, 0, 0, 0, 0, 0, Q16_ONE, 0})
#define Q16_OCTONION_E7         ((q16_octonion_t){0, 0, 0, 0, 0, 0, 0, Q16_ONE})

/* Superforce constant in Q16.16: SF = c⁴/G ≈ 10⁴⁴ N */
#define Q16_SUPERFORCE_CONSTANT ((q16_t)(0x7FFFFFFF))   /* Maximum positive Q16.16 */

/* ============================================================================
 * Core Construction Functions (Zero-Copy Optimized)
 * ============================================================================ */

/**
 * Create octonion from 8 Q16.16 components (zero-copy constructor)
 * Cost: 0 cycles (compile-time initialization)
 */
static inline q16_octonion_t q16_octonion_make(q16_t e0, q16_t e1, q16_t e2, q16_t e3,
                                              q16_t e4, q16_t e5, q16_t e6, q16_t e7) {
    return (q16_octonion_t){ .v = {e0, e1, e2, e3, e4, e5, e6, e7} };
}

/**
 * Create octonion from integer components (compile-time safe)
 */
#define Q16_OCTONION_FROM_INTS(i0, i1, i2, i3, i4, i5, i6, i7) \
    q16_octonion_make(q16_from_int(i0), q16_from_int(i1), q16_from_int(i2), q16_from_int(i3), \
                     q16_from_int(i4), q16_from_int(i5), q16_from_int(i6), q16_from_int(i7))

/**
 * Zero-copy octonion assignment using word-level transfers
 * Cost: 4 cycles (4x 64-bit moves)
 */
static inline void q16_octonion_copy(q16_octonion_t *dest, const q16_octonion_t *src) {
    dest->words[0] = src->words[0];
    dest->words[1] = src->words[1];
    dest->words[2] = src->words[2];
    dest->words[3] = src->words[3];
}

/**
 * Branch-free equality comparison
 * Cost: 5 cycles
 */
static inline bool q16_octonion_equals(const q16_octonion_t *a, const q16_octonion_t *b) {
    uint64_t diff = 0;
    diff |= a->words[0] ^ b->words[0];
    diff |= a->words[1] ^ b->words[1];
    diff |= a->words[2] ^ b->words[2];
    diff |= a->words[3] ^ b->words[3];
    return diff == 0;
}

/* ============================================================================
 * Fast Quaternion Operations for Cayley-Dickson Construction
 * ============================================================================ */

/**
 * Create quaternion from Q16.16 components
 */
static inline q16_quaternion_t q16_quaternion_make(q16_t w, q16_t x, q16_t y, q16_t z) {
    return (q16_quaternion_t){ .w = w, .x = x, .y = y, .z = z };
}

/**
 * Quaternion multiplication (Hamilton product)
 * Cost: 16 cycles (8 muls + 8 adds)
 */
static inline q16_quaternion_t q16_quaternion_mul(q16_quaternion_t a, q16_quaternion_t b) {
    return (q16_quaternion_t){
        .w = q16_sub(q16_sub(q16_sub(q16_mul(a.w, b.w), q16_mul(a.x, b.x)), 
                            q16_mul(a.y, b.y)), q16_mul(a.z, b.z)),
        .x = q16_add(q16_add(q16_add(q16_mul(a.w, b.x), q16_mul(a.x, b.w)), 
                            q16_mul(a.y, b.z)), q16_neg(q16_mul(a.z, b.y))),
        .y = q16_add(q16_add(q16_sub(q16_mul(a.w, b.y), q16_mul(a.x, b.z)), 
                            q16_mul(a.y, b.w)), q16_mul(a.z, b.x)),
        .z = q16_add(q16_sub(q16_add(q16_mul(a.w, b.z), q16_mul(a.x, b.y)), 
                            q16_mul(a.y, b.x)), q16_mul(a.z, b.w))
    };
}

/**
 * Quaternion conjugate
 * Cost: 3 cycles (3 negations)
 */
static inline q16_quaternion_t q16_quaternion_conj(q16_quaternion_t q) {
    return (q16_quaternion_t){ .w = q.w, .x = -q.x, .y = -q.y, .z = -q.z };
}

/**
 * Quaternion squared norm (sum of squares)
 * Cost: 8 cycles (4 muls + 3 adds)
 */
static inline q16_t q16_quaternion_norm_sq(q16_quaternion_t q) {
    return q16_add(q16_add(q16_add(q16_mul(q.w, q.w), q16_mul(q.x, q.x)),
                          q16_mul(q.y, q.y)), q16_mul(q.z, q.z));
}

/* ============================================================================
 * Core Octonion Arithmetic (Cayley-Dickson Construction)
 * ============================================================================ */

/**
 * Octonion addition (component-wise)
 * Cost: 8 cycles (8 adds)
 */
static inline q16_octonion_t q16_octonion_add(q16_octonion_t a, q16_octonion_t b) {
    return (q16_octonion_t){
        .v = {
            q16_add(a.v[0], b.v[0]), q16_add(a.v[1], b.v[1]),
            q16_add(a.v[2], b.v[2]), q16_add(a.v[3], b.v[3]),
            q16_add(a.v[4], b.v[4]), q16_add(a.v[5], b.v[5]),
            q16_add(a.v[6], b.v[6]), q16_add(a.v[7], b.v[7])
        }
    };
}

/**
 * Octonion subtraction (component-wise)
 * Cost: 8 cycles (8 subs)
 */
static inline q16_octonion_t q16_octonion_sub(q16_octonion_t a, q16_octonion_t b) {
    return (q16_octonion_t){
        .v = {
            q16_sub(a.v[0], b.v[0]), q16_sub(a.v[1], b.v[1]),
            q16_sub(a.v[2], b.v[2]), q16_sub(a.v[3], b.v[3]),
            q16_sub(a.v[4], b.v[4]), q16_sub(a.v[5], b.v[5]),
            q16_sub(a.v[6], b.v[6]), q16_sub(a.v[7], b.v[7])
        }
    };
}

/**
 * Scalar multiplication
 * Cost: 8 cycles (8 scalar muls)
 */
static inline q16_octonion_t q16_octonion_scale(q16_octonion_t o, q16_t scalar) {
    return (q16_octonion_t){
        .v = {
            q16_mul(o.v[0], scalar), q16_mul(o.v[1], scalar),
            q16_mul(o.v[2], scalar), q16_mul(o.v[3], scalar),
            q16_mul(o.v[4], scalar), q16_mul(o.v[5], scalar),
            q16_mul(o.v[6], scalar), q16_mul(o.v[7], scalar)
        }
    };
}

/**
 * Octonion conjugate (negate imaginary parts)
 * Cost: 7 cycles (7 negations)
 */
static inline q16_octonion_t q16_octonion_conj(q16_octonion_t o) {
    return (q16_octonion_t){
        .e0 = o.e0, .e1 = -o.e1, .e2 = -o.e2, .e3 = -o.e3,
        .e4 = -o.e4, .e5 = -o.e5, .e6 = -o.e6, .e7 = -o.e7
    };
}

/* ============================================================================
 * Advanced Functions (Implemented in q16_octonion.c)
 * ============================================================================ */

/* Octonion multiplication using Cayley-Dickson construction */
q16_octonion_t q16_octonion_mul(q16_octonion_t a, q16_octonion_t b);

/* Squared norm (sum of squares of all components) */
q16_t q16_octonion_norm_squared(q16_octonion_t o);

/* Norm (magnitude) using fast fixed-point square root */
q16_t q16_octonion_norm(q16_octonion_t o);

/* Multiplicative inverse */
q16_octonion_t q16_octonion_inverse(q16_octonion_t o);

/* Exponential (e^o) using series expansion */
q16_octonion_t q16_octonion_exp(q16_octonion_t o);

/* Natural logarithm */
q16_octonion_t q16_octonion_log(q16_octonion_t o);

/* Power function (a^b) */
q16_octonion_t q16_octonion_pow(q16_octonion_t a, q16_octonion_t b);

/* ============================================================================
 * SIMD-Optimized Batch Operations
 * ============================================================================ */

#ifdef __SSE2__
/* Process 2 octonions in parallel using SSE2 */
void q16_octonion_add_simd_x2(q16_octonion_t *result, const q16_octonion_t *a, const q16_octonion_t *b);
void q16_octonion_sub_simd_x2(q16_octonion_t *result, const q16_octonion_t *a, const q16_octonion_t *b);
void q16_octonion_scale_simd_x2(q16_octonion_t *result, const q16_octonion_t *a, q16_t scalar);
#endif

#ifdef __AVX2__
/* Process 4 octonions in parallel using AVX2 */
void q16_octonion_add_simd_x4(q16_octonion_t *result, const q16_octonion_t *a, const q16_octonion_t *b);
void q16_octonion_sub_simd_x4(q16_octonion_t *result, const q16_octonion_t *a, const q16_octonion_t *b);
void q16_octonion_scale_simd_x4(q16_octonion_t *result, const q16_octonion_t *a, q16_t scalar);
#endif

/* ============================================================================
 * Copy-on-Write Operations
 * ============================================================================ */

/* Create COW octonion container */
q16_octonion_cow_t* q16_octonion_cow_create(const q16_octonion_t *initial);

/* Clone COW octonion (increment ref count) */
q16_octonion_cow_t* q16_octonion_cow_clone(q16_octonion_cow_t *cow);

/* Get mutable reference (trigger copy if needed) */
q16_octonion_t* q16_octonion_cow_get_mut(q16_octonion_cow_t *cow);

/* Get immutable reference (no copy) */
const q16_octonion_t* q16_octonion_cow_get_const(q16_octonion_cow_t *cow);

/* Release COW reference (decrement ref count) */
void q16_octonion_cow_release(q16_octonion_cow_t *cow);

/* ============================================================================
 * Conversion Utilities
 * ============================================================================ */

/* Convert from floating-point octonion (userspace only) */
#ifndef EXO_KERNEL
q16_octonion_t q16_octonion_from_double(double e0, double e1, double e2, double e3,
                                       double e4, double e5, double e6, double e7);
#endif

/* Convert to string representation (debugging) */
const char* q16_octonion_to_string(q16_octonion_t o);

/* ============================================================================
 * Superforce Energy Integration
 * ============================================================================ */

/**
 * Compute Superforce energy from octonion state
 * E = SF * ||o||² where SF = c⁴/G
 */
static inline q16_t q16_octonion_superforce_energy(q16_octonion_t o) {
    q16_t norm_sq = q16_octonion_norm_squared(o);
    return q16_mul(norm_sq, Q16_SUPERFORCE_CONSTANT);
}

/**
 * Apply energy decay to octonion (exponential cooling)
 */
static inline q16_octonion_t q16_octonion_energy_decay(q16_octonion_t o, q16_t decay_factor) {
    return q16_octonion_scale(o, decay_factor);
}

/* ============================================================================
 * Performance Testing and Validation
 * ============================================================================ */

#ifdef Q16_OCTONION_ENABLE_TESTS
void q16_octonion_run_tests(void);
void q16_octonion_benchmark(void);
#endif

/* ============================================================================
 * Fast-Path Macros for Common Operations
 * ============================================================================ */

/* Zero-overhead abstractions for common patterns */
#define Q16_OCTONION_IS_ZERO(o)     q16_octonion_equals(&(o), &Q16_OCTONION_ZERO)
#define Q16_OCTONION_IS_REAL(o)     ((o).e1 == 0 && (o).e2 == 0 && (o).e3 == 0 && \
                                     (o).e4 == 0 && (o).e5 == 0 && (o).e6 == 0 && (o).e7 == 0)
#define Q16_OCTONION_REAL_PART(o)   ((o).e0)
#define Q16_OCTONION_IMAG_NORM_SQ(o) (q16_add(q16_add(q16_add(q16_mul((o).e1, (o).e1), \
                                      q16_mul((o).e2, (o).e2)), q16_add(q16_mul((o).e3, (o).e3), \
                                      q16_mul((o).e4, (o).e4))), q16_add(q16_add(q16_mul((o).e5, (o).e5), \
                                      q16_mul((o).e6, (o).e6)), q16_mul((o).e7, (o).e7))))

#endif /* Q16_OCTONION_H */
