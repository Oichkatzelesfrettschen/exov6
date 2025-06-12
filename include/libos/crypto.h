#ifndef LIBOS_CRYPTO_H
#define LIBOS_CRYPTO_H

#include <stdint.h>
#include <stddef.h> // For size_t

/**
 * @brief Derives a key using a (currently stubbed) Key Derivation Function.
 *
 * This function is intended to derive a key of 'okm_len' bytes from the
 * input key material 'ikm'. The 'salt' can be used to add randomness,
 * and 'info' provides context-specific information for the derivation.
 *
 * NOTE: This is currently a STUB implementation and NOT cryptographically secure.
 * It should be replaced with a proper KDF (e.g., HKDF-SHA256) in the future.
 *
 * @param salt Optional salt. Can be NULL if not used.
 * @param salt_len Length of the salt. Must be 0 if salt is NULL.
 * @param ikm Input Key Material. Must not be NULL if ikm_len > 0.
 * @param ikm_len Length of the Input Key Material.
 * @param info Optional context-specific information string. Can be NULL.
 * @param okm Buffer to store the Output Key Material. Must not be NULL if okm_len > 0.
 * @param okm_len Desired length of the Output Key Material in bytes.
 * @return 0 on success, -1 on error (e.g., invalid parameters like NULL ikm/okm for non-zero lengths).
 */
int libos_kdf_derive(
    const uint8_t* salt, size_t salt_len,
    const uint8_t* ikm, size_t ikm_len,
    const char* info,
    uint8_t* okm, size_t okm_len
);

/**
 * @brief Verifies two HMAC digests in constant time.
 *
 * This function compares two byte arrays (HMAC digests) of a given length.
 * The comparison is designed to take the same amount of time regardless of
 * whether the digests match or where the first difference occurs, to help
 * mitigate timing side-channel attacks.
 *
 * @param a Pointer to the first HMAC digest.
 * @param b Pointer to the second HMAC digest.
 * @param len The length of the digests to compare.
 * @return 1 if the digests are identical, 0 otherwise.
 */
int hmac_verify_constant_time(const unsigned char *a, const unsigned char *b, size_t len);

#endif // LIBOS_CRYPTO_H
