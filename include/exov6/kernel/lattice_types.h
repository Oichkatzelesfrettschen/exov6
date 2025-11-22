/**
 * @file    lattice_types.h
 * @brief   Fixed-size types and structures for lattice‐based cryptography.
 *
 * This header defines concrete, compile‐time fixed‐length types for
 * lattice schemes (e.g., Kyber, Dilithium) and related cryptographic tokens.
 * It also provides an octonion capability token for exotic capability schemes.
 *
 * All sizes are determined by preprocessor constants—no dynamic allocation
 * is required for these types.
 */

#pragma once

#ifndef LATTICE_TYPES_H
#define LATTICE_TYPES_H

#include <stdint.h>  // uint8_t, uint16_t
#include <stddef.h>  // size_t

/** @brief Dimension parameter for NTRU/Kyber/Dilithium-style schemes. */
#define LATTICE_DIMENSION_N        256u

/** @brief Byte length of a public key (approx. for Kyber-like schemes). */
#define LATTICE_KEY_BYTES          ((LATTICE_DIMENSION_N * 12u / 8u) * 2u)

/** @brief Byte length of a signature (e.g. Dilithium2 at N=256). */
#define LATTICE_SIG_BYTES          2420u

/** @brief Number of coefficients in a polynomial‐vector element. */
#define LATTICE_POLY_VEC_ELEMENTS  LATTICE_DIMENSION_N

/**
 * @brief Polynomial‐vector element (e.g., a Kyber or Dilithium vector).
 *
 * Contains exactly N coefficients of 16 bits each.
 */
typedef struct {
    uint16_t coeffs[LATTICE_POLY_VEC_ELEMENTS];
} lattice_poly_vec_t;

/**
 * @brief Public key container for lattice‐based scheme.
 *
 * Exactly LATTICE_KEY_BYTES bytes.
 */
typedef struct {
    uint8_t key_data[LATTICE_KEY_BYTES];
} lattice_public_key_t;

/**
 * @brief Secret (private) key container for lattice‐based scheme.
 *
 * Exactly LATTICE_KEY_BYTES bytes (same size as public key).
 */
typedef struct {
    uint8_t key_data[LATTICE_KEY_BYTES];
} lattice_secret_key_t;

/**
 * @brief Signature container for lattice‐based scheme.
 *
 * Exactly LATTICE_SIG_BYTES bytes.
 */
typedef struct {
    uint8_t sig_data[LATTICE_SIG_BYTES];
} lattice_sig_t;

/**
 * @brief Octonion capability token (8‐tuple of doubles).
 *
 * Union allows:
 *  - Array‐indexed access via `v[0..7]`
 *  - Named access via members e0..e7
 *  - Raw byte access via `bytes[...]`
 */
typedef union {
    double       v[8];                             /**< Array view. */
    struct {
        double e0, e1, e2, e3, e4, e5, e6, e7;      /**< Named view. */
    };
    uint8_t      bytes[8 * sizeof(double)];         /**< Byte‐level view. */
} octonion_t;

#endif /* LATTICE_TYPES_H */
