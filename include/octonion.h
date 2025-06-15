#pragma once

#ifndef OCTONION_H
#define OCTONION_H

/**
 * @file octonion.h
 * @brief Quaternion and octonion algebra utilities.
 */

/* Quaternion and octonion type definitions. */

#include "lattice_types.h"

typedef struct {
  double w;
  double x;
  double y;
  double z;
} quaternion_t;

#include <math.h>      /* sqrt and fabs */
#include <stdatomic.h> /* atomic operations for spinlocks */
#include <string.h>    /* memcmp */
#ifdef USE_SIMD
#include <immintrin.h> /* SIMD intrinsics */
#endif

/** Add two octonions component-wise. */
octonion_t octonion_add(octonion_t a, octonion_t b);

/** Multiply two octonions using the Cayley–Dickson construction. */
octonion_t octonion_mul(octonion_t a, octonion_t b);

/** Compute the multiplicative inverse of an octonion. */
octonion_t octonion_inv(octonion_t o);

// Forward declare for use in qspin_lock_t if it were here, but it'll be in its
// own header.

static inline int octonion_equals(const octonion_t *o1, const octonion_t *o2) {
  if (!o1 || !o2)
    return (o1 == o2);
  return memcmp(o1, o2, sizeof(octonion_t)) == 0;
}

static inline quaternion_t quaternion_create(double w, double x, double y,
                                             double z) {
  quaternion_t q = {w, x, y, z};
  return q;
}

static inline quaternion_t quaternion_multiply(quaternion_t q1,
                                               quaternion_t q2) {
  quaternion_t result;
  result.w = q1.w * q2.w - q1.x * q2.x - q1.y * q2.y - q1.z * q2.z;
  result.x = q1.w * q2.x + q1.x * q2.w + q1.y * q2.z - q1.z * q2.y;
  result.y = q1.w * q2.y - q1.x * q2.z + q1.y * q2.w + q1.z * q2.x;
  result.z = q1.w * q2.z + q1.x * q2.y - q1.y * q2.x + q1.z * q2.w;
  return result;
}

/** Return the quaternion conjugate. */
static inline quaternion_t quaternion_conjugate(quaternion_t q) {
  return (quaternion_t){q.w, -q.x, -q.y, -q.z};
}

// Squared norm, often used to avoid sqrt
static inline double quaternion_norm_sq(quaternion_t q) {
  return q.w * q.w + q.x * q.x + q.y * q.y + q.z * q.z;
}

// Actual norm
static inline double quaternion_norm(quaternion_t q) {
  return sqrt(quaternion_norm_sq(q));
}

// Quaternion representing a CPU (simplified)
static inline quaternion_t quaternion_from_cpu_id(int cpu_id) {
  // This is a simplistic representation. The framework paper might imply
  // a more sophisticated mapping or use of quaternion properties.
  return quaternion_create((double)cpu_id, 0.0, 0.0, 0.0);
}

/** Create an octonion from eight coefficients. */
static inline octonion_t octonion_create(double e0, double e1, double e2,
                                         double e3, double e4, double e5,
                                         double e6, double e7) {
  return (octonion_t){e0, e1, e2, e3, e4, e5, e6, e7};
}

/** Conjugate an octonion by negating the imaginary parts. */
static inline octonion_t octonion_conjugate(octonion_t o) {
  return (octonion_t){o.e0, -o.e1, -o.e2, -o.e3, -o.e4, -o.e5, -o.e6, -o.e7};
}

/**
 * Multiply two octonions using the Cayley-Dickson construction.
 */
static inline octonion_t octonion_multiply(octonion_t a, octonion_t b) {
  quaternion_t a_l = {a.e0, a.e1, a.e2, a.e3};
  quaternion_t a_r = {a.e4, a.e5, a.e6, a.e7};
  quaternion_t b_l = {b.e0, b.e1, b.e2, b.e3};
  quaternion_t b_r = {b.e4, b.e5, b.e6, b.e7};

  quaternion_t left = quaternion_multiply(a_l, b_l);
  quaternion_t temp = quaternion_multiply(quaternion_conjugate(b_r), a_r);
  left.w -= temp.w;
  left.x -= temp.x;
  left.y -= temp.y;
  left.z -= temp.z;

  quaternion_t right = quaternion_multiply(b_r, a_l);
  quaternion_t temp2 = quaternion_multiply(a_r, quaternion_conjugate(b_l));
  right.w += temp2.w;
  right.x += temp2.x;
  right.y += temp2.y;
  right.z += temp2.z;

  return (octonion_t){left.w,  left.x,  left.y,  left.z,
                      right.w, right.x, right.y, right.z};
}

/** Squared norm of an octonion. */
static inline double octonion_norm_sq(octonion_t o) {
#ifdef USE_SIMD
  __m256d v0 = _mm256_loadu_pd(&o.e0);
  __m256d v1 = _mm256_loadu_pd(&o.e4);
  v0 = _mm256_mul_pd(v0, v0);
  v1 = _mm256_mul_pd(v1, v1);
  __m256d sum = _mm256_add_pd(v0, v1);
  __m128d hi =
      _mm_add_pd(_mm256_extractf128_pd(sum, 1), _mm256_castpd256_pd128(sum));
  hi = _mm_hadd_pd(hi, hi);
  double out;
  _mm_store_sd(&out, hi);
  return out;
#else
  return o.e0 * o.e0 + o.e1 * o.e1 + o.e2 * o.e2 + o.e3 * o.e3 + o.e4 * o.e4 +
         o.e5 * o.e5 + o.e6 * o.e6 + o.e7 * o.e7;
#endif
}

/** Norm of an octonion. */
static inline double octonion_norm(octonion_t o) {
  return sqrt(octonion_norm_sq(o));
}

/** Compute the multiplicative inverse of an octonion. */
static inline octonion_t octonion_inverse(octonion_t o) {
  double n = octonion_norm_sq(o);
  octonion_t conj = octonion_conjugate(o);
  if (n == 0.0)
    return conj; /* Return zero divisor unchanged. */
  double inv_n = 1.0 / n;
  conj.e0 *= inv_n;
  conj.e1 *= inv_n;
  conj.e2 *= inv_n;
  conj.e3 *= inv_n;
  conj.e4 *= inv_n;
  conj.e5 *= inv_n;
  conj.e6 *= inv_n;
  conj.e7 *= inv_n;
  return conj;
}

// Placeholder for hyperbolic pause - for now, just a busy loop scaled by norm.
// The actual "hyperbolic_pause" from the paper might be more complex.
static inline void hyperbolic_pause(double norm_val) {
  // Avoid issues with zero or very small norms in loop bound
  unsigned long delay = (unsigned long)(fabs(norm_val) * 100.0);
  if (delay == 0)
    delay = 1; // Minimum delay
  for (volatile unsigned long i = 0; i < delay; ++i) {
    // Busy wait
  }
}

#endif // OCTONION_H
