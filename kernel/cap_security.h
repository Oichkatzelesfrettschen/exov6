/**
 * @file cap_security.h
 * @brief Secure capability system with post-quantum protection
 *
 * Provides secure key derivation and capability authentication
 * using post-quantum lattice-based cryptography.
 */

#pragma once

#include "types.h"
#include "exo.h"
#include <stdint.h>
#include <stddef.h>

/**
 * @brief Initialize the capability security subsystem.
 * 
 * Derives the capability secret from system entropy and
 * post-quantum lattice parameters. Must be called during
 * early kernel initialization.
 *
 * @return 0 on success, negative on failure
 */
[[nodiscard]] int cap_security_init(void);

/**
 * @brief Derive a capability authentication secret.
 *
 * Uses HKDF-SHA256 with lattice-based entropy to derive
 * a per-boot capability secret. This ensures capability
 * secrets are not predictable across reboots.
 *
 * @param entropy_source Optional entropy bytes (can be NULL)
 * @param entropy_len Length of entropy source
 * @param secret Output buffer for derived secret (32 bytes)
 * @return 0 on success, negative on failure
 */
[[nodiscard]] int cap_derive_secret(const uint8_t *entropy_source, 
                                   size_t entropy_len, 
                                   uint8_t secret[32]);

/**
 * @brief Securely clear capability secret from memory.
 *
 * Uses explicit_bzero or equivalent to prevent compiler
 * optimization from removing the memory clearing.
 *
 * @param secret Secret buffer to clear
 * @param len Length of secret buffer
 */
void cap_secure_clear(void *secret, size_t len);

/**
 * @brief Verify capability authentication in constant time.
 *
 * Uses constant-time comparison to prevent timing attacks
 * against capability verification.
 *
 * @param expected Expected authentication tag
 * @param provided Provided authentication tag
 * @return 1 if tags match, 0 otherwise
 */
[[nodiscard]] int cap_verify_constant_time(const hash256_t *expected,
                                          const hash256_t *provided);