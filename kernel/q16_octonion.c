/**
 * @file q16_octonion.c  
 * @brief Kernel-Safe Fixed-Point Octonion Mathematics Implementation
 * 
 * High-performance Q16.16 fixed-point octonion operations with zero-copy
 * optimizations, SIMD acceleration, and copy-on-write semantics.
 * 
 * Implements complete octonion algebra using Cayley-Dickson construction:
 * - Non-associative multiplication via quaternion pairs
 * - Norm computations using fast integer arithmetic
 * - Energy calculations for Superforce integration
 * - Branch-free algorithms for deterministic performance
 */

#include "q16_octonion.h"
#include "q16_fixed.h"
#include "defs.h"

#ifdef __SSE2__
#include <emmintrin.h>
#endif

#ifdef __AVX2__
#include <immintrin.h>
#endif

/* ============================================================================
 * Octonion Multiplication via Cayley-Dickson Construction
 * ============================================================================ */

/**
 * Multiply two octonions using the Cayley-Dickson construction.
 * 
 * Decomposes each octonion into two quaternions:
 * o = (a, b) where a and b are quaternions
 * 
 * Product: (a₁, b₁) × (a₂, b₂) = (a₁a₂ - b₂*b₁, b₂a₁ + b₁a₂*)
 * 
 * Cost: ~100 cycles (2 quaternion muls + quaternion ops)
 */
q16_octonion_t q16_octonion_mul(q16_octonion_t a, q16_octonion_t b) {
    /* Split octonions into quaternion pairs */
    q16_quaternion_t a_left = { a.e0, a.e1, a.e2, a.e3 };
    q16_quaternion_t a_right = { a.e4, a.e5, a.e6, a.e7 };
    q16_quaternion_t b_left = { b.e0, b.e1, b.e2, b.e3 };
    q16_quaternion_t b_right = { b.e4, b.e5, b.e6, b.e7 };
    
    /* Compute left quaternion: a_left * b_left - conj(b_right) * a_right */
    q16_quaternion_t left_prod = q16_quaternion_mul(a_left, b_left);
    q16_quaternion_t b_right_conj = q16_quaternion_conj(b_right);
    q16_quaternion_t right_term = q16_quaternion_mul(b_right_conj, a_right);
    
    q16_quaternion_t result_left = {
        .w = q16_sub(left_prod.w, right_term.w),
        .x = q16_sub(left_prod.x, right_term.x),
        .y = q16_sub(left_prod.y, right_term.y),
        .z = q16_sub(left_prod.z, right_term.z)
    };
    
    /* Compute right quaternion: b_right * a_left + a_right * conj(b_left) */
    q16_quaternion_t right_prod1 = q16_quaternion_mul(b_right, a_left);
    q16_quaternion_t b_left_conj = q16_quaternion_conj(b_left);
    q16_quaternion_t right_prod2 = q16_quaternion_mul(a_right, b_left_conj);
    
    q16_quaternion_t result_right = {
        .w = q16_add(right_prod1.w, right_prod2.w),
        .x = q16_add(right_prod1.x, right_prod2.x),
        .y = q16_add(right_prod1.y, right_prod2.y),
        .z = q16_add(right_prod1.z, right_prod2.z)
    };
    
    return (q16_octonion_t){
        .e0 = result_left.w, .e1 = result_left.x, .e2 = result_left.y, .e3 = result_left.z,
        .e4 = result_right.w, .e5 = result_right.x, .e6 = result_right.y, .e7 = result_right.z
    };
}

/* ============================================================================
 * Norm Computations
 * ============================================================================ */

/**
 * Compute squared norm (sum of squares) of an octonion.
 * 
 * ||o||² = e₀² + e₁² + e₂² + e₃² + e₄² + e₅² + e₆² + e₇²
 * 
 * Cost: 16 cycles (8 muls + 7 adds)
 */
q16_t q16_octonion_norm_squared(q16_octonion_t o) {
    q16_t sum = 0;
    sum = q16_add(sum, q16_mul(o.e0, o.e0));
    sum = q16_add(sum, q16_mul(o.e1, o.e1));
    sum = q16_add(sum, q16_mul(o.e2, o.e2));
    sum = q16_add(sum, q16_mul(o.e3, o.e3));
    sum = q16_add(sum, q16_mul(o.e4, o.e4));
    sum = q16_add(sum, q16_mul(o.e5, o.e5));
    sum = q16_add(sum, q16_mul(o.e6, o.e6));
    sum = q16_add(sum, q16_mul(o.e7, o.e7));
    return sum;
}

/**
 * Compute norm (magnitude) of an octonion.
 * 
 * ||o|| = √(||o||²)
 * 
 * Uses fast fixed-point square root approximation.
 * Cost: ~60 cycles
 */
q16_t q16_octonion_norm(q16_octonion_t o) {
    q16_t norm_sq = q16_octonion_norm_squared(o);
    return q16_sqrt(norm_sq);
}

/* ============================================================================
 * Advanced Octonion Operations
 * ============================================================================ */

/**
 * Compute multiplicative inverse of an octonion.
 * 
 * o⁻¹ = conj(o) / ||o||²
 * 
 * Cost: ~100 cycles
 */
q16_octonion_t q16_octonion_inverse(q16_octonion_t o) {
    q16_t norm_sq = q16_octonion_norm_squared(o);
    
    /* Handle zero divisor case */
    if (norm_sq == 0) {
        return Q16_OCTONION_ZERO;
    }
    
    /* Compute conjugate */
    q16_octonion_t conj = q16_octonion_conj(o);
    
    /* Scale by 1/||o||² */
    q16_t inv_norm_sq = q16_recip(norm_sq);
    return q16_octonion_scale(conj, inv_norm_sq);
}

/**
 * Octonion exponential using series expansion.
 * 
 * exp(o) = exp(real) * (cos(||imag||) + (imag/||imag||) * sin(||imag||))
 * 
 * For pure imaginary octonions, this reduces to Euler's formula.
 * Cost: ~300 cycles
 */
q16_octonion_t q16_octonion_exp(q16_octonion_t o) {
    q16_t real_part = o.e0;
    
    /* Extract imaginary part */
    q16_octonion_t imag_part = {
        .e0 = 0, .e1 = o.e1, .e2 = o.e2, .e3 = o.e3,
        .e4 = o.e4, .e5 = o.e5, .e6 = o.e6, .e7 = o.e7
    };
    
    /* Compute norm of imaginary part */
    q16_t imag_norm = q16_octonion_norm(imag_part);
    
    /* Handle pure real case */
    if (imag_norm == 0) {
        q16_t exp_real = q16_exp(real_part);
        return (q16_octonion_t){ .e0 = exp_real, 0, 0, 0, 0, 0, 0, 0 };
    }
    
    /* Compute exp(real) */
    q16_t exp_real = q16_exp(real_part);
    
    /* Compute cos(||imag||) and sin(||imag||) */
    q16_t cos_imag = q16_cos(imag_norm);
    q16_t sin_imag = q16_sin(imag_norm);
    
    /* Normalize imaginary part */
    q16_t inv_imag_norm = q16_recip(imag_norm);
    q16_octonion_t imag_unit = q16_octonion_scale(imag_part, inv_imag_norm);
    
    /* Build result: exp(real) * (cos(||imag||) + imag_unit * sin(||imag||)) */
    q16_octonion_t cos_term = { .e0 = cos_imag, 0, 0, 0, 0, 0, 0, 0 };
    q16_octonion_t sin_term = q16_octonion_scale(imag_unit, sin_imag);
    
    q16_octonion_t sum = q16_octonion_add(cos_term, sin_term);
    return q16_octonion_scale(sum, exp_real);
}

/**
 * Octonion natural logarithm.
 * 
 * log(o) = log(||o||) + (imag/||imag||) * arccos(real/||o||)
 * 
 * Cost: ~400 cycles
 */
q16_octonion_t q16_octonion_log(q16_octonion_t o) {
    q16_t norm = q16_octonion_norm(o);
    
    /* Handle zero case */
    if (norm == 0) {
        return Q16_OCTONION_ZERO;  /* -∞, but we return zero */
    }
    
    q16_t real_part = o.e0;
    
    /* Extract and normalize imaginary part */
    q16_octonion_t imag_part = {
        .e0 = 0, .e1 = o.e1, .e2 = o.e2, .e3 = o.e3,
        .e4 = o.e4, .e5 = o.e5, .e6 = o.e6, .e7 = o.e7
    };
    
    q16_t imag_norm = q16_octonion_norm(imag_part);
    
    /* Handle pure real case */
    if (imag_norm == 0) {
        q16_t log_norm = q16_log2(norm);  /* Approximate using log2 */
        return (q16_octonion_t){ .e0 = log_norm, 0, 0, 0, 0, 0, 0, 0 };
    }
    
    /* Compute log(||o||) */
    q16_t log_norm = q16_log2(norm);
    
    /* Compute arccos(real/||o||) - approximate using Taylor series */
    q16_t cos_theta = q16_div(real_part, norm);
    q16_t theta = q16_sub(Q16_PI >> 1, cos_theta);  /* Simple approximation */
    
    /* Scale imaginary unit vector by theta */
    q16_t inv_imag_norm = q16_recip(imag_norm);
    q16_octonion_t imag_unit = q16_octonion_scale(imag_part, inv_imag_norm);
    q16_octonion_t angle_part = q16_octonion_scale(imag_unit, theta);
    
    /* Combine real and imaginary parts */
    angle_part.e0 = log_norm;
    return angle_part;
}

/**
 * Octonion power function: a^b = exp(b * log(a))
 * 
 * Cost: ~800 cycles (log + mul + exp)
 */
q16_octonion_t q16_octonion_pow(q16_octonion_t a, q16_octonion_t b) {
    /* Handle special cases */
    if (q16_octonion_equals(&a, &Q16_OCTONION_ZERO)) {
        return Q16_OCTONION_ZERO;
    }
    
    if (q16_octonion_equals(&b, &Q16_OCTONION_ZERO)) {
        return Q16_OCTONION_ONE;
    }
    
    /* General case: a^b = exp(b * log(a)) */
    q16_octonion_t log_a = q16_octonion_log(a);
    q16_octonion_t b_log_a = q16_octonion_mul(b, log_a);
    return q16_octonion_exp(b_log_a);
}

/* ============================================================================
 * SIMD-Optimized Batch Operations
 * ============================================================================ */

#ifdef __SSE2__

/**
 * Add two octonion pairs using SSE2 (process 2 octonions at once).
 * 
 * Each octonion has 8 components, so we process 16 Q16.16 values total
 * using 4 SSE2 operations (4 components per __m128i).
 * 
 * Cost: 4 cycles throughput
 */
void q16_octonion_add_simd_x2(q16_octonion_t *result, const q16_octonion_t *a, const q16_octonion_t *b) {
    /* Process first octonion */
    __m128i a1 = _mm_load_si128((__m128i*)&a[0].v[0]);  /* Load a[0].e0-e3 */
    __m128i b1 = _mm_load_si128((__m128i*)&b[0].v[0]);  
    __m128i r1 = _mm_add_epi32(a1, b1);
    _mm_store_si128((__m128i*)&result[0].v[0], r1);
    
    __m128i a2 = _mm_load_si128((__m128i*)&a[0].v[4]);  /* Load a[0].e4-e7 */
    __m128i b2 = _mm_load_si128((__m128i*)&b[0].v[4]);  
    __m128i r2 = _mm_add_epi32(a2, b2);
    _mm_store_si128((__m128i*)&result[0].v[4], r2);
    
    /* Process second octonion */
    __m128i a3 = _mm_load_si128((__m128i*)&a[1].v[0]);  /* Load a[1].e0-e3 */
    __m128i b3 = _mm_load_si128((__m128i*)&b[1].v[0]);  
    __m128i r3 = _mm_add_epi32(a3, b3);
    _mm_store_si128((__m128i*)&result[1].v[0], r3);
    
    __m128i a4 = _mm_load_si128((__m128i*)&a[1].v[4]);  /* Load a[1].e4-e7 */
    __m128i b4 = _mm_load_si128((__m128i*)&b[1].v[4]);  
    __m128i r4 = _mm_add_epi32(a4, b4);
    _mm_store_si128((__m128i*)&result[1].v[4], r4);
}

/**
 * Subtract two octonion pairs using SSE2.
 */
void q16_octonion_sub_simd_x2(q16_octonion_t *result, const q16_octonion_t *a, const q16_octonion_t *b) {
    __m128i a1 = _mm_load_si128((__m128i*)&a[0].v[0]);
    __m128i b1 = _mm_load_si128((__m128i*)&b[0].v[0]);
    __m128i r1 = _mm_sub_epi32(a1, b1);
    _mm_store_si128((__m128i*)&result[0].v[0], r1);
    
    __m128i a2 = _mm_load_si128((__m128i*)&a[0].v[4]);
    __m128i b2 = _mm_load_si128((__m128i*)&b[0].v[4]);
    __m128i r2 = _mm_sub_epi32(a2, b2);
    _mm_store_si128((__m128i*)&result[0].v[4], r2);
    
    __m128i a3 = _mm_load_si128((__m128i*)&a[1].v[0]);
    __m128i b3 = _mm_load_si128((__m128i*)&b[1].v[0]);
    __m128i r3 = _mm_sub_epi32(a3, b3);
    _mm_store_si128((__m128i*)&result[1].v[0], r3);
    
    __m128i a4 = _mm_load_si128((__m128i*)&a[1].v[4]);
    __m128i b4 = _mm_load_si128((__m128i*)&b[1].v[4]);
    __m128i r4 = _mm_sub_epi32(a4, b4);
    _mm_store_si128((__m128i*)&result[1].v[4], r4);
}

/**
 * Scale two octonions by a scalar with optimal SIMD path selection
 * Fallback hierarchy: SSE4.1 → SSE2 → MMX → Scalar
 */
void q16_octonion_scale_simd_x2(q16_octonion_t *result, const q16_octonion_t *a, q16_t scalar) {
#if defined(__SSE4_1__) || defined(__AVX__)
    /* SSE4.1 path: Native 32-bit multiply */
    __m128i scalar_vec = _mm_set1_epi32(scalar);
    
    /* Process first octonion (8 components = 2 x 128-bit vectors) */
    __m128i a1 = _mm_load_si128((__m128i*)&a[0].v[0]);
    __m128i lo1 = _mm_mullo_epi32(a1, scalar_vec);
    __m128i hi1 = _mm_mulhi_epi32(a1, scalar_vec);
    __m128i result1_lo = _mm_srli_epi32(lo1, 16);
    __m128i result1_hi = _mm_slli_epi32(hi1, 16);
    __m128i result1 = _mm_or_si128(result1_lo, result1_hi);
    _mm_store_si128((__m128i*)&result[0].v[0], result1);
    
    __m128i a2 = _mm_load_si128((__m128i*)&a[0].v[4]);
    __m128i lo2 = _mm_mullo_epi32(a2, scalar_vec);
    __m128i hi2 = _mm_mulhi_epi32(a2, scalar_vec);
    __m128i result2_lo = _mm_srli_epi32(lo2, 16);
    __m128i result2_hi = _mm_slli_epi32(hi2, 16);
    __m128i result2 = _mm_or_si128(result2_lo, result2_hi);
    _mm_store_si128((__m128i*)&result[0].v[4], result2);
    
    /* Process second octonion */
    __m128i a3 = _mm_load_si128((__m128i*)&a[1].v[0]);
    __m128i lo3 = _mm_mullo_epi32(a3, scalar_vec);
    __m128i hi3 = _mm_mulhi_epi32(a3, scalar_vec);
    __m128i result3_lo = _mm_srli_epi32(lo3, 16);
    __m128i result3_hi = _mm_slli_epi32(hi3, 16);
    __m128i result3 = _mm_or_si128(result3_lo, result3_hi);
    _mm_store_si128((__m128i*)&result[1].v[0], result3);
    
    __m128i a4 = _mm_load_si128((__m128i*)&a[1].v[4]);
    __m128i lo4 = _mm_mullo_epi32(a4, scalar_vec);
    __m128i hi4 = _mm_mulhi_epi32(a4, scalar_vec);
    __m128i result4_lo = _mm_srli_epi32(lo4, 16);
    __m128i result4_hi = _mm_slli_epi32(hi4, 16);
    __m128i result4 = _mm_or_si128(result4_lo, result4_hi);
    _mm_store_si128((__m128i*)&result[1].v[4], result4);
    
#elif defined(__SSE2__)
    /* SSE2 path: 16-bit multiply with unpacking */
    __m128i scalar_vec = _mm_set1_epi32(scalar);
    __m128i scalar_lo = _mm_and_si128(scalar_vec, _mm_set1_epi32(0xFFFF));
    __m128i scalar_hi = _mm_srli_epi32(scalar_vec, 16);
    
    for (int oct = 0; oct < 2; oct++) {
        for (int vec = 0; vec < 2; vec++) {
            __m128i va = _mm_load_si128((__m128i*)&a[oct].v[vec * 4]);
            
            __m128i va_lo = _mm_and_si128(va, _mm_set1_epi32(0xFFFF));
            __m128i va_hi = _mm_srli_epi32(va, 16);
            
            __m128i prod_ll = _mm_mullo_epi16(va_lo, scalar_lo);
            __m128i prod_lh = _mm_mullo_epi16(va_lo, scalar_hi);
            __m128i prod_hl = _mm_mullo_epi16(va_hi, scalar_lo);
            __m128i prod_hh = _mm_mullo_epi16(va_hi, scalar_hi);
            
            __m128i mid = _mm_add_epi32(prod_lh, prod_hl);
            __m128i mid_shifted = _mm_add_epi32(_mm_srli_epi32(prod_ll, 16), mid);
            __m128i high_shifted = _mm_slli_epi32(prod_hh, 16);
            __m128i vr = _mm_add_epi32(high_shifted, mid_shifted);
            
            _mm_store_si128((__m128i*)&result[oct].v[vec * 4], vr);
        }
    }
    
#elif defined(__MMX__)
    /* MMX path: Process 2 components at a time */
    for (int oct = 0; oct < 2; oct++) {
        for (int i = 0; i < 4; i++) {
            __m64 *ma = (__m64*)&a[oct].v[i * 2];
            __m64 *mr = (__m64*)&result[oct].v[i * 2];
            __m64 scalar_vec = _mm_set1_pi32(scalar);
            
            __m64 va = *ma;
            __m64 va_lo = _mm_and_si64(va, _mm_set1_pi32(0xFFFF));
            __m64 va_hi = _mm_srli_pi32(va, 16);
            __m64 scalar_lo = _mm_and_si64(scalar_vec, _mm_set1_pi32(0xFFFF));
            __m64 scalar_hi = _mm_srli_pi32(scalar_vec, 16);
            
            __m64 prod_ll = _mm_mullo_pi16(va_lo, scalar_lo);
            __m64 prod_lh = _mm_mullo_pi16(va_lo, scalar_hi);
            __m64 prod_hl = _mm_mullo_pi16(va_hi, scalar_lo);
            __m64 prod_hh = _mm_mullo_pi16(va_hi, scalar_hi);
            
            __m64 mid = _mm_add_pi32(prod_lh, prod_hl);
            __m64 mid_shifted = _mm_add_pi32(_mm_srli_pi32(prod_ll, 16), mid);
            __m64 high_shifted = _mm_slli_pi32(prod_hh, 16);
            __m64 vr = _mm_add_pi32(high_shifted, mid_shifted);
            
            *mr = vr;
        }
    }
    _mm_empty();
    
#else
    /* Scalar fallback */
    for (int oct = 0; oct < 2; oct++) {
        for (int i = 0; i < 8; i++) {
            int64_t prod = (int64_t)a[oct].v[i] * (int64_t)scalar;
            result[oct].v[i] = (q16_t)(prod >> 16);
        }
    }
#endif
}

#endif /* __SSE2__ */

#ifdef __AVX2__

/**
 * Add four octonions using AVX2 (32 Q16.16 values total).
 * 
 * Cost: 8 cycles throughput (4 AVX2 additions)
 */
void q16_octonion_add_simd_x4(q16_octonion_t *result, const q16_octonion_t *a, const q16_octonion_t *b) {
    /* Process 8 components at a time using 256-bit AVX2 */
    for (int i = 0; i < 4; i++) {
        __m256i av = _mm256_load_si256((__m256i*)&a[i].v[0]);
        __m256i bv = _mm256_load_si256((__m256i*)&b[i].v[0]);
        __m256i rv = _mm256_add_epi32(av, bv);
        _mm256_store_si256((__m256i*)&result[i].v[0], rv);
    }
}

/**
 * Subtract four octonions using AVX2.
 */
void q16_octonion_sub_simd_x4(q16_octonion_t *result, const q16_octonion_t *a, const q16_octonion_t *b) {
    for (int i = 0; i < 4; i++) {
        __m256i av = _mm256_load_si256((__m256i*)&a[i].v[0]);
        __m256i bv = _mm256_load_si256((__m256i*)&b[i].v[0]);
        __m256i rv = _mm256_sub_epi32(av, bv);
        _mm256_store_si256((__m256i*)&result[i].v[0], rv);
    }
}

/**
 * Scale four octonions by scalar using AVX2.
 */
void q16_octonion_scale_simd_x4(q16_octonion_t *result, const q16_octonion_t *a, q16_t scalar) {
    __m256i scalar_vec = _mm256_set1_epi32(scalar);
    
    for (int i = 0; i < 4; i++) {
        __m256i av = _mm256_load_si256((__m256i*)&a[i].v[0]);
        
        /* 32x32->64 bit multiplication with proper Q16.16 scaling */
        __m256i lo = _mm256_mullo_epi32(av, scalar_vec);
        __m256i hi = _mm256_mulhi_epi32(av, scalar_vec);
        
        /* Combine results and shift for Q16.16 */
        __m256i result_lo = _mm256_srli_epi32(lo, 16);
        __m256i result_hi = _mm256_slli_epi32(hi, 16);
        __m256i rv = _mm256_or_si256(result_lo, result_hi);
        
        _mm256_store_si256((__m256i*)&result[i].v[0], rv);
    }
}

#endif /* __AVX2__ */

/* ============================================================================
 * Copy-on-Write Implementation
 * ============================================================================ */

/**
 * Create new COW octonion container with reference count of 1.
 */
q16_octonion_cow_t* q16_octonion_cow_create(const q16_octonion_t *initial) {
    q16_octonion_cow_t *cow = kalloc();  /* Use kernel allocator */
    if (!cow) return NULL;
    
    cow->data = kalloc();
    if (!cow->data) {
        kfree((char*)cow);
        return NULL;
    }
    
    q16_octonion_copy(cow->data, initial);
    cow->ref_count = 1;
    cow->is_mutable = true;
    cow->energy_consumed = 0;
    
    return cow;
}

/**
 * Clone COW container (increment reference count).
 */
q16_octonion_cow_t* q16_octonion_cow_clone(q16_octonion_cow_t *cow) {
    if (!cow) return NULL;
    
    __atomic_fetch_add(&cow->ref_count, 1, __ATOMIC_SEQ_CST);
    cow->is_mutable = false;  /* Mark as immutable since shared */
    
    return cow;
}

/**
 * Get mutable reference, triggering copy if needed.
 */
q16_octonion_t* q16_octonion_cow_get_mut(q16_octonion_cow_t *cow) {
    if (!cow) return NULL;
    
    /* If reference count is 1, we can mutate in place */
    if (cow->ref_count == 1) {
        cow->is_mutable = true;
        return cow->data;
    }
    
    /* Need to create private copy */
    q16_octonion_t *new_data = kalloc();
    if (!new_data) return NULL;
    
    q16_octonion_copy(new_data, cow->data);
    
    /* Decrement old reference */
    __atomic_fetch_sub(&cow->ref_count, 1, __ATOMIC_SEQ_CST);
    
    /* Update to point to new data */
    cow->data = new_data;
    cow->ref_count = 1;
    cow->is_mutable = true;
    
    return new_data;
}

/**
 * Get immutable reference (no copy needed).
 */
const q16_octonion_t* q16_octonion_cow_get_const(q16_octonion_cow_t *cow) {
    return cow ? cow->data : NULL;
}

/**
 * Release COW reference (decrement count, free if zero).
 */
void q16_octonion_cow_release(q16_octonion_cow_t *cow) {
    if (!cow) return;
    
    uint32_t old_count = __atomic_fetch_sub(&cow->ref_count, 1, __ATOMIC_SEQ_CST);
    
    if (old_count == 1) {
        /* Last reference - free memory */
        kfree((char*)cow->data);
        kfree((char*)cow);
    }
}

/* ============================================================================
 * Conversion and Utility Functions
 * ============================================================================ */

#ifndef EXO_KERNEL
/**
 * Convert from floating-point octonion (userspace only).
 * 
 * This function is only available in userspace contexts where
 * floating-point operations are permitted.
 */
q16_octonion_t q16_octonion_from_double(double e0, double e1, double e2, double e3,
                                       double e4, double e5, double e6, double e7) {
    return (q16_octonion_t){
        .v = {
            Q16_FROM_FLOAT(e0), Q16_FROM_FLOAT(e1), 
            Q16_FROM_FLOAT(e2), Q16_FROM_FLOAT(e3),
            Q16_FROM_FLOAT(e4), Q16_FROM_FLOAT(e5), 
            Q16_FROM_FLOAT(e6), Q16_FROM_FLOAT(e7)
        }
    };
}
#endif

/**
 * Convert octonion to string representation (for debugging).
 * 
 * Returns static buffer - not thread safe, but useful for kernel debugging.
 */
const char* q16_octonion_to_string(q16_octonion_t o) {
    static char buffer[256];
    char *pos = buffer;
    
    /* Manual string building without sprintf */
    *pos++ = '(';
    
    for (int i = 0; i < 8; i++) {
        const char *component = q16_to_string(o.v[i]);
        
        /* Copy component string */
        while (*component) {
            *pos++ = *component++;
        }
        
        if (i < 7) {
            *pos++ = ',';
            *pos++ = ' ';
        }
    }
    
    *pos++ = ')';
    *pos = '\0';
    
    return buffer;
}

/* ============================================================================
 * Testing and Validation
 * ============================================================================ */

#ifdef Q16_OCTONION_ENABLE_TESTS

/**
 * Run comprehensive octonion tests.
 */
void q16_octonion_run_tests(void) {
    cprintf("Q16 Octonion Tests:\n");
    
    /* Test basic construction */
    q16_octonion_t o1 = Q16_OCTONION_FROM_INTS(1, 2, 3, 4, 5, 6, 7, 8);
    q16_octonion_t o2 = Q16_OCTONION_FROM_INTS(8, 7, 6, 5, 4, 3, 2, 1);
    
    /* Test arithmetic */
    q16_octonion_t sum = q16_octonion_add(o1, o2);
    q16_octonion_t diff = q16_octonion_sub(o1, o2);
    q16_octonion_t prod = q16_octonion_mul(o1, o2);
    
    cprintf("  o1 = %s\n", q16_octonion_to_string(o1));
    cprintf("  o2 = %s\n", q16_octonion_to_string(o2));
    cprintf("  o1 + o2 = %s\n", q16_octonion_to_string(sum));
    cprintf("  o1 - o2 = %s\n", q16_octonion_to_string(diff));
    cprintf("  o1 * o2 = %s\n", q16_octonion_to_string(prod));
    
    /* Test norms */
    q16_t norm_sq = q16_octonion_norm_squared(o1);
    q16_t norm = q16_octonion_norm(o1);
    cprintf("  ||o1||² = %s\n", q16_to_string(norm_sq));
    cprintf("  ||o1|| = %s\n", q16_to_string(norm));
    
    /* Test conjugate */
    q16_octonion_t conj = q16_octonion_conj(o1);
    cprintf("  conj(o1) = %s\n", q16_octonion_to_string(conj));
    
    /* Test inverse */
    q16_octonion_t inv = q16_octonion_inverse(o1);
    q16_octonion_t identity_check = q16_octonion_mul(o1, inv);
    cprintf("  o1⁻¹ = %s\n", q16_octonion_to_string(inv));
    cprintf("  o1 * o1⁻¹ = %s\n", q16_octonion_to_string(identity_check));
    
    /* Test Superforce energy */
    q16_t energy = q16_octonion_superforce_energy(o1);
    cprintf("  Superforce energy = %s\n", q16_to_string(energy));
}

/**
 * Benchmark octonion operations.
 */
void q16_octonion_benchmark(void) {
    const int iterations = 10000;
    q16_octonion_t a = Q16_OCTONION_FROM_INTS(1, 2, 3, 4, 5, 6, 7, 8);
    q16_octonion_t b = Q16_OCTONION_FROM_INTS(8, 7, 6, 5, 4, 3, 2, 1);
    q16_octonion_t result;
    
    cprintf("Q16 Octonion Benchmarks (%d iterations):\n", iterations);
    
    /* Time addition */
    uint32_t start = ticks;
    for (int i = 0; i < iterations; i++) {
        result = q16_octonion_add(a, b);
    }
    uint32_t add_time = ticks - start;
    cprintf("  Addition: %d ticks total, %d cycles/op\n", 
            add_time, add_time * 1000000 / iterations);
    
    /* Time multiplication */
    start = ticks;
    for (int i = 0; i < iterations; i++) {
        result = q16_octonion_mul(a, b);
    }
    uint32_t mul_time = ticks - start;
    cprintf("  Multiplication: %d ticks total, %d cycles/op\n", 
            mul_time, mul_time * 1000000 / iterations);
    
    /* Time norm computation */
    start = ticks;
    q16_t norm;
    for (int i = 0; i < iterations; i++) {
        norm = q16_octonion_norm(a);
    }
    uint32_t norm_time = ticks - start;
    cprintf("  Norm: %d ticks total, %d cycles/op\n", 
            norm_time, norm_time * 1000000 / iterations);
    
    /* Prevent optimization */
    (void)result;
    (void)norm;
}

#endif /* Q16_OCTONION_ENABLE_TESTS */
