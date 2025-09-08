/**
 * @file    octonion.h
 * @brief   Quaternion and octonion algebra utilities.
 *
 * Provides data structures and operations for quaternions and octonions,
 * including creation, arithmetic, norms, and comparisons. Useful for
 * capability tokens, rotations, and exotic algebraic constructs.
 */

#pragma once
#ifndef OCTONION_H
#define OCTONION_H

#include <string.h>      /* memcmp */
#include <stdint.h>      /* Fixed point types */

#include "lattice_types.h"  /* defines octonion_t */

/* Kernel-safe math functions */
extern uint32_t kisqrt32(uint32_t x);
extern int32_t kabs32(int32_t x);

/* Fixed-point square root for doubles */
static inline double ksqrt_double(double x) {
    /* Convert to fixed point, sqrt, convert back */
    if (x < 0) return 0;
    uint32_t fixed = (uint32_t)(x * 65536.0);
    uint32_t result = kisqrt32(fixed);
    return result / 256.0;  /* sqrt scales by 256 */
}

/* Absolute value for doubles */
static inline double kfabs(double x) {
    return x < 0 ? -x : x;
}

/**
 * @brief Quaternion type (4D extension of complex numbers).
 */
typedef struct {
    double w, x, y, z;
} quaternion_t;

/**
 * @brief Create a quaternion.
 */
static inline quaternion_t quaternion_create(double w, double x, double y, double z) {
    return (quaternion_t){ .w = w, .x = x, .y = y, .z = z };
}

/**
 * @brief Multiply two quaternions.
 */
static inline quaternion_t quaternion_multiply(quaternion_t a, quaternion_t b) {
    return (quaternion_t){
        .w = a.w*b.w - a.x*b.x - a.y*b.y - a.z*b.z,
        .x = a.w*b.x + a.x*b.w + a.y*b.z - a.z*b.y,
        .y = a.w*b.y - a.x*b.z + a.y*b.w + a.z*b.x,
        .z = a.w*b.z + a.x*b.y - a.y*b.x + a.z*b.w
    };
}

/**
 * @brief Conjugate of a quaternion.
 */
static inline quaternion_t quaternion_conjugate(quaternion_t q) {
    return (quaternion_t){ .w = q.w, .x = -q.x, .y = -q.y, .z = -q.z };
}

/**
 * @brief Squared norm (magnitude^2) of a quaternion.
 */
static inline double quaternion_norm_sq(quaternion_t q) {
    return q.w*q.w + q.x*q.x + q.y*q.y + q.z*q.z;
}

/**
 * @brief Norm (magnitude) of a quaternion.
 */
static inline double quaternion_norm(quaternion_t q) {
    return ksqrt_double(quaternion_norm_sq(q));
}

/**
 * @brief Build a quaternion from a CPU ID (simple mapping).
 */
static inline quaternion_t quaternion_from_cpu_id(int cpu_id) {
    return quaternion_create((double)cpu_id, 0.0, 0.0, 0.0);
}

/**
 * @brief Compare two octonions for equality (bitwise).
 *
 * Returns 1 if equal, 0 otherwise.
 */
static inline int octonion_equals(const octonion_t *a, const octonion_t *b) {
    if (!a || !b) return a == b;
    return memcmp(a, b, sizeof(*a)) == 0;
}

/**
 * @brief Create an octonion from eight doubles.
 */
static inline octonion_t octonion_create(double e0, double e1, double e2, double e3,
                                         double e4, double e5, double e6, double e7) {
    return (octonion_t){
        .e0 = e0, .e1 = e1, .e2 = e2, .e3 = e3,
        .e4 = e4, .e5 = e5, .e6 = e6, .e7 = e7
    };
}

/**
 * @brief Conjugate (negate imaginary parts) of an octonion.
 */
static inline octonion_t octonion_conjugate(octonion_t o) {
    return (octonion_t){
        .e0 = o.e0, .e1 = -o.e1, .e2 = -o.e2, .e3 = -o.e3,
        .e4 = -o.e4, .e5 = -o.e5, .e6 = -o.e6, .e7 = -o.e7
    };
}

/**
 * @brief Multiply two octonions via Cayley–Dickson.
 */
static inline octonion_t octonion_multiply(octonion_t a, octonion_t b) {
    /* Split into quaternion halves */
    quaternion_t a_l = {a.e0, a.e1, a.e2, a.e3};
    quaternion_t a_r = {a.e4, a.e5, a.e6, a.e7};
    quaternion_t b_l = {b.e0, b.e1, b.e2, b.e3};
    quaternion_t b_r = {b.e4, b.e5, b.e6, b.e7};

    quaternion_t left  = quaternion_multiply(a_l, b_l);
    quaternion_t tmp1  = quaternion_multiply(quaternion_conjugate(b_r), a_r);
    left.w -= tmp1.w; left.x -= tmp1.x; left.y -= tmp1.y; left.z -= tmp1.z;

    quaternion_t right = quaternion_multiply(b_r, a_l);
    quaternion_t tmp2  = quaternion_multiply(a_r, quaternion_conjugate(b_l));
    right.w += tmp2.w; right.x += tmp2.x; right.y += tmp2.y; right.z += tmp2.z;

    return (octonion_t){
        .e0 = left.w,  .e1 = left.x,  .e2 = left.y,  .e3 = left.z,
        .e4 = right.w, .e5 = right.x, .e6 = right.y, .e7 = right.z
    };
}

/**
 * @brief Squared norm of an octonion.
 */
static inline double octonion_norm_sq(octonion_t o) {
    return o.e0*o.e0 + o.e1*o.e1 + o.e2*o.e2 + o.e3*o.e3 +
           o.e4*o.e4 + o.e5*o.e5 + o.e6*o.e6 + o.e7*o.e7;
}

/**
 * @brief Norm (magnitude) of an octonion.
 */
static inline double octonion_norm(octonion_t o) {
    return ksqrt_double(octonion_norm_sq(o));
}

/**
 * @brief Inverse (multiplicative) of an octonion.
 */
static inline octonion_t octonion_inverse(octonion_t o) {
    double norm2 = octonion_norm_sq(o);
    octonion_t conj = octonion_conjugate(o);
    if (norm2 == 0.0) return conj;  /* zero divisor */
    double inv = 1.0 / norm2;
    conj.e0 *= inv; conj.e1 *= inv; conj.e2 *= inv; conj.e3 *= inv;
    conj.e4 *= inv; conj.e5 *= inv; conj.e6 *= inv; conj.e7 *= inv;
    return conj;
}

/**
 * @brief Busy‐wait delay scaled by a norm—useful for hyperbolic pause.
 */
static inline void hyperbolic_pause(double norm_val) {
    unsigned long delay = (unsigned long)(kfabs(norm_val) * 100.0);
    if (delay == 0) delay = 1;
    for (volatile unsigned long i = 0; i < delay; ++i) { }
}

#endif /* OCTONION_H */