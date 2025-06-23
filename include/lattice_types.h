#pragma once

#ifndef LATTICE_TYPES_H
#define LATTICE_TYPES_H

#include <stdint.h> // For uint16_t, uint8_t
#include <stddef.h> // For size_t (though not used if sizes are implicit)

// Placeholder values for typical lattice scheme parameters
#define LATTICE_DIMENSION_N 256 // Example: n for Kyber/Dilithium
#define LATTICE_KEY_BYTES                                                      \
  (LATTICE_DIMENSION_N * 12 / 8 *                                              \
   2) // Approx for Kyber public key (k*n*logq/8 for k=2)
#define LATTICE_SIG_BYTES                                                      \
  2420 // Example: Dilithium2 signature size (CRYSTALS-Dilithium M(L2) with
       // N=256)
#define LATTICE_POLY_VEC_ELEMENTS                                              \
  LATTICE_DIMENSION_N // Number of coefficients in a polynomial vector element

typedef struct {
  uint16_t coeffs[LATTICE_POLY_VEC_ELEMENTS]; // Example: a polynomial vector
                                              // (e.g. n elements of uint16_t)
  // int dimension; // Could be implicit from LATTICE_POLY_VEC_ELEMENTS
} lattice_poly_vec_t; // More specific than generic lattice_pt for resource_id

typedef struct {
  uint8_t key_data[LATTICE_KEY_BYTES];
  // size_t key_size; // Could be implicit from LATTICE_KEY_BYTES
} lattice_public_key_t; // More specific

/**
 * @brief Container for a lattice-based private key.
 */
typedef struct {
  uint8_t key_data[LATTICE_KEY_BYTES];
} lattice_secret_key_t;

typedef struct {
  uint8_t sig_data[LATTICE_SIG_BYTES];
  // size_t sig_size; // Could be implicit from LATTICE_SIG_BYTES
} lattice_sig_t; // More specific

/**
 * @brief Octonion capability token consisting of eight components.
 */
/**
 * @brief Octonion capability token consisting of eight components.
 *
 * The anonymous structure allows direct member access (e.g., `o.e0`) while
 * still providing array-based and raw byte views.
 */
typedef union {
  double v[8];                       /**< Array-style coefficient access. */
  struct {
    double e0;
    double e1;
    double e2;
    double e3;
    double e4;
    double e5;
    double e6;
    double e7;
  };                                /**< Named coefficient access. */
  uint8_t bytes[8 * sizeof(double)]; /**< Raw byte representation. */
} octonion_t;

// Original generic lattice_pt (can be kept if used elsewhere, or removed if
// fully replaced) For now, we will replace its use in cap_entry with the more
// specific lattice_poly_vec_t*
typedef struct {
  void *data;    // Pointer to the actual point data
  int dimension; // Dimension of the vector or number of coefficients
} lattice_pt;

#endif // LATTICE_TYPES_H
