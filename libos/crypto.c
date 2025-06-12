#include "libos/crypto.h" // Should resolve to include/libos/crypto.h
#include <string.h> // For strlen, memcpy, memset, and NULL
#include <stdio.h>  // For temporary printf warning

// NOTE: THIS IS A STUB IMPLEMENTATION AND NOT CRYPTOGRAPHICALLY SECURE.
// It should be replaced with a proper KDF (e.g., HKDF-SHA256).

int libos_kdf_derive(
    const uint8_t* salt, size_t salt_len,
    const uint8_t* ikm, size_t ikm_len,
    const char* info,
    uint8_t* okm, size_t okm_len
) {
    // Basic parameter validation
    if ((ikm_len > 0 && !ikm) || (okm_len > 0 && !okm)) {
        return -1; // Invalid parameters
    }
    if (salt_len > 0 && !salt) {
        // Technically, salt can be all zeros, but NULL with non-zero len is an issue.
        // For simplicity, let's treat NULL salt with salt_len > 0 as an error.
        return -1;
    }

    // STUB: Simple non-secure derivation for placeholder purposes.
    // This just XORs parts of IKM, salt, and info into the output buffer.
    // It is NOT a secure KDF.

    // Temporary: Print a warning that a stub is being used.
    // In a real system, this might go to a dedicated log or be a compile-time warning.
    // Using printf directly might be problematic if the libOS environment does not
    // have a conventional stdout or if it's too early in boot.
    // Consider removing or replacing with a libOS-specific logging mechanism.
    // printf("WARNING: Using STUB Key Derivation Function. NOT FOR PRODUCTION USE.\n");


    memset(okm, 0, okm_len); // Initialize output buffer

    if (okm_len == 0) {
        return 0; // Nothing to derive
    }

    size_t i;
    for (i = 0; i < okm_len; ++i) {
        if (ikm_len > 0) {
            okm[i] ^= ikm[i % ikm_len];
        }
        if (salt_len > 0) {
            okm[i] ^= salt[i % salt_len];
        }
        if (info) {
            size_t info_len = strlen(info);
            if (info_len > 0) {
                okm[i] ^= info[i % info_len];
            }
        }
        // Add a simple counter to make different bytes of OKM different
        // even if inputs are short or repetitive for this stub.
        okm[i] ^= (uint8_t)i;
    }

    return 0; // Success
}

/**
 * Verifies two HMAC digests in constant time.
 */
int hmac_verify_constant_time(const unsigned char *a, const unsigned char *b, size_t len) {
    volatile unsigned char diff = 0;
    if (a == NULL || b == NULL) {
        if (a == b) return 1; // Both NULL, considered equal for the purpose of this check.
        return 0; // One NULL, one not: considered different.
    }
    for (size_t i = 0; i < len; i++) {
        diff |= a[i] ^ b[i];
    }
    return diff == 0;
}
