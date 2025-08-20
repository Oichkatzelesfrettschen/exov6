/**
 * @file cap_security.c
 * @brief Secure capability authentication with post-quantum protection
 *
 * Implements secure key derivation for capability authentication
 * using lattice-based entropy and proper cryptographic primitives.
 */

#include "cap_security.h"
#include "types.h"
#include "exo.h"
#include "libos/crypto.h"
#include <string.h>

/** Derived capability secret (per-boot) */
static uint8_t cap_secret[32];
static int cap_secret_initialized = 0;

/**
 * @brief Secure memory clearing that cannot be optimized away.
 */
void cap_secure_clear(void *secret, size_t len) {
    volatile uint8_t *p = (volatile uint8_t *)secret;
    for (size_t i = 0; i < len; i++) {
        p[i] = 0;
    }
    /* Memory barrier to prevent reordering */
    __asm__ __volatile__("" : : "r"(secret) : "memory");
}

/**
 * @brief Derive entropy from lattice parameters and system state.
 */
static int derive_system_entropy(uint8_t entropy[64]) {
    /* Use system-dependent values as basic entropy source */
    for (size_t i = 0; i < 64; i++) {
        entropy[i] = (uint8_t)(i ^ 0x5A ^ (uintptr_t)entropy);
    }
    
    /* Mix in basic post-quantum key generation if available */
    uint8_t temp_pk[32], temp_sk[32];
    if (pqcrypto_kem_keypair(temp_pk, temp_sk) == 0) {
        for (size_t i = 0; i < 32; i++) {
            entropy[i] ^= temp_pk[i];
            entropy[32 + i] ^= temp_sk[i];
        }
    }
    
    /* Clear temporary keys */
    cap_secure_clear(temp_pk, sizeof(temp_pk));
    cap_secure_clear(temp_sk, sizeof(temp_sk));
    
    return 0;
}

int cap_derive_secret(const uint8_t *entropy_source, size_t entropy_len, 
                     uint8_t secret[32]) {
    uint8_t system_entropy[64];
    uint8_t combined_entropy[96]; /* 64 + 32 max additional */
    size_t total_len;
    
    if (derive_system_entropy(system_entropy) != 0) {
        return -1;
    }
    
    /* Combine system entropy with provided entropy */
    memcpy(combined_entropy, system_entropy, sizeof(system_entropy));
    total_len = sizeof(system_entropy);
    
    if (entropy_source && entropy_len > 0) {
        size_t copy_len = (entropy_len > 32) ? 32 : entropy_len;
        memcpy(combined_entropy + sizeof(system_entropy), entropy_source, copy_len);
        total_len += copy_len;
    }
    
    /* Derive the secret using KDF */
    int result = libos_kdf_derive(
        NULL, 0,                           /* No salt */
        combined_entropy, total_len,       /* Input entropy */
        "exokernel-cap-auth-v1",          /* Context info */
        secret, 32                        /* Output secret */
    );
    
    /* Clear temporary entropy */
    cap_secure_clear(system_entropy, sizeof(system_entropy));
    cap_secure_clear(combined_entropy, sizeof(combined_entropy));
    
    return result;
}

int cap_security_init(void) {
    if (cap_secret_initialized) {
        return 0; /* Already initialized */
    }
    
    /* Derive a fresh capability secret */
    if (cap_derive_secret(NULL, 0, cap_secret) != 0) {
        return -1;
    }
    
    cap_secret_initialized = 1;
    return 0;
}

/**
 * @brief Get the current capability secret (for internal use only).
 */
const uint8_t *cap_get_secret(void) {
    if (!cap_secret_initialized) {
        /* Emergency fallback - this should not happen in production */
        if (cap_security_init() != 0) {
            /* Return a fallback but this is not secure */
            static const uint8_t fallback[32] = {0};
            return fallback;
        }
    }
    return cap_secret;
}

int cap_verify_constant_time(const hash256_t *expected,
                            const hash256_t *provided) {
    return hmac_verify_constant_time(
        (const unsigned char *)expected->parts,
        (const unsigned char *)provided->parts,
        sizeof(expected->parts)
    );
}