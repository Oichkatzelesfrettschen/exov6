#include "include/octonion.h"

/**
 * @file octonion.c
 * @brief Octonion arithmetic helper implementations.
 */

/** Add two octonions component-wise. */
octonion_t octonion_add(octonion_t a, octonion_t b) {
  octonion_t r = {0};
  for (int i = 0; i < 8; ++i) {
    r.v[i] = a.v[i] + b.v[i];
  }
  return r;
}

/** Multiply two octonions using the Cayley–Dickson construction. */
octonion_t octonion_mul(octonion_t a, octonion_t b) {
  quaternion_t a_l = {a.coeffs.e0, a.coeffs.e1, a.coeffs.e2, a.coeffs.e3};
  quaternion_t a_r = {a.coeffs.e4, a.coeffs.e5, a.coeffs.e6, a.coeffs.e7};
  quaternion_t b_l = {b.coeffs.e0, b.coeffs.e1, b.coeffs.e2, b.coeffs.e3};
  quaternion_t b_r = {b.coeffs.e4, b.coeffs.e5, b.coeffs.e6, b.coeffs.e7};

  quaternion_t left = quaternion_multiply(a_l, b_l);
  quaternion_t tmp = quaternion_multiply(quaternion_conjugate(b_r), a_r);
  left.w -= tmp.w;
  left.x -= tmp.x;
  left.y -= tmp.y;
  left.z -= tmp.z;

  quaternion_t right = quaternion_multiply(b_r, a_l);
  tmp = quaternion_multiply(a_r, quaternion_conjugate(b_l));
  right.w += tmp.w;
  right.x += tmp.x;
  right.y += tmp.y;
  right.z += tmp.z;

  return (octonion_t){.coeffs = {left.w, left.x, left.y, left.z, right.w,
                                 right.x, right.y, right.z}};
}

/** Compute the multiplicative inverse of an octonion. */
octonion_t octonion_inv(octonion_t o) {
  double n = 0.0;
  for (int i = 0; i < 8; ++i) {
    n += o.v[i] * o.v[i];
  }
  if (n == 0.0) {
    return o; /* zero divisor */
  }
  octonion_t conj = octonion_conjugate(o);
  for (int i = 0; i < 8; ++i) {
    conj.v[i] /= n;
  }
  return conj;
}
