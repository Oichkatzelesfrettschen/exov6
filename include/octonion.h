#pragma once

#ifndef OCTONION_H
#define OCTONION_H

// Placeholder for quaternion and octonion types

typedef struct {
    double w;
    double x;
    double y;
    double z;
} quaternion_t;

typedef struct {
    double e0;
    double e1;
    double e2;
    double e3;
    double e4;
    double e5;
    double e6;
    double e7;
} octonion_t;

#include <math.h> // For sqrt in norm, fabs
#include <stdatomic.h> // For atomic operations (will be used in spinlock)
#include <string.h> // For memcmp

// Forward declare for use in qspin_lock_t if it were here, but it'll be in its own header.

static inline int octonion_equals(const octonion_t* o1, const octonion_t* o2) {
    if (!o1 || !o2) return (o1 == o2);
    return memcmp(o1, o2, sizeof(octonion_t)) == 0;
}

static inline quaternion_t quaternion_create(double w, double x, double y, double z) {
    quaternion_t q = {w, x, y, z};
    return q;
}

static inline quaternion_t quaternion_multiply(quaternion_t q1, quaternion_t q2) {
    quaternion_t result;
    result.w = q1.w * q2.w - q1.x * q2.x - q1.y * q2.y - q1.z * q2.z;
    result.x = q1.w * q2.x + q1.x * q2.w + q1.y * q2.z - q1.z * q2.y;
    result.y = q1.w * q2.y - q1.x * q2.z + q1.y * q2.w + q1.z * q2.x;
    result.z = q1.w * q2.z + q1.x * q2.y - q1.y * q2.x + q1.z * q2.w;
    return result;
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

// Placeholder for hyperbolic pause - for now, just a busy loop scaled by norm.
// The actual "hyperbolic_pause" from the paper might be more complex.
static inline void hyperbolic_pause(double norm_val) {
    // Avoid issues with zero or very small norms in loop bound
    unsigned long delay = (unsigned long)(fabs(norm_val) * 100.0);
    if (delay == 0) delay = 1; // Minimum delay
    for (volatile unsigned long i = 0; i < delay; ++i) {
        // Busy wait
    }
}

#endif // OCTONION_H
