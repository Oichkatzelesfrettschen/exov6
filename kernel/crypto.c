#include "libos/crypto.h" // Should resolve to include/libos/crypto.h
#ifdef HAVE_PQCRYPTO
#include <pqcrypto/kyber512.h>
#endif
#include <string.h> // For strlen, memcpy, memset, and NULL
#include <stdio.h>  // For temporary printf warning

// NOTE: THIS IS A STUB IMPLEMENTATION AND NOT CRYPTOGRAPHICALLY SECURE.
// It should be replaced with a proper KDF (e.g., HKDF-SHA256).

int libos_kdf_derive(const uint8_t *salt, size_t salt_len, const uint8_t *ikm,
                     size_t ikm_len, const char *info, uint8_t *okm,
                     size_t okm_len) {
  // Basic parameter validation
  if ((ikm_len > 0 && !ikm) || (okm_len > 0 && !okm)) {
    return -1; // Invalid parameters
  }
  if (salt_len > 0 && !salt) {
    // Technically, salt can be all zeros, but NULL with non-zero len is an
    // issue. For simplicity, let's treat NULL salt with salt_len > 0 as an
    // error.
    return -1;
  }

  // STUB: Simple non-secure derivation for placeholder purposes.
  // This just XORs parts of IKM, salt, and info into the output buffer.
  // It is NOT a secure KDF.

  // Temporary: Print a warning that a stub is being used.
  // In a real system, this might go to a dedicated log or be a compile-time
  // warning. Using printf directly might be problematic if the libOS
  // environment does not have a conventional stdout or if it's too early in
  // boot. Consider removing or replacing with a libOS-specific logging
  // mechanism. printf("WARNING: Using STUB Key Derivation Function. NOT FOR
  // PRODUCTION USE.\n");

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
int hmac_verify_constant_time(const unsigned char *a, const unsigned char *b,
                              size_t len) {
  volatile unsigned char diff = 0;
  if (a == NULL || b == NULL) {
    if (a == b)
      return 1; // Both NULL, considered equal for the purpose of this check.
    return 0;   // One NULL, one not: considered different.
  }
  for (size_t i = 0; i < len; i++) {
    diff |= a[i] ^ b[i];
  }
  return diff == 0;
}

/*=============================================================================
 * Post-quantum helper stubs
 *============================================================================*/
/** Generate a key pair for a Kyber-like KEM. */
int pqcrypto_kem_keypair(uint8_t *pk, uint8_t *sk) {
#ifdef HAVE_PQCRYPTO
  return pqcrystals_kyber512_ref_keypair(pk, sk);
#else
  for (size_t i = 0; i < 32; ++i) {
    pk[i] = (uint8_t)i;
    sk[i] = (uint8_t)(i + 1);
  }
  return 0;
#endif
}

/** Encapsulate a secret with a peer public key. */
int pqcrypto_kem_enc(uint8_t *cipher, uint8_t *key, const uint8_t *pk) {
#ifdef HAVE_PQCRYPTO
  return pqcrystals_kyber512_ref_enc(cipher, key, pk);
#else
  (void)pk;
  for (size_t i = 0; i < 32; ++i) {
    key[i] = (uint8_t)(i + 2);
    cipher[i] = key[i] ^ 0xAAu;
  }
  return 0;
#endif
}

/** Decapsulate a secret using a private key. */
int pqcrypto_kem_dec(uint8_t *key, const uint8_t *cipher, const uint8_t *sk) {
#ifdef HAVE_PQCRYPTO
  return pqcrystals_kyber512_ref_dec(key, cipher, sk);
#else
  (void)sk;
  for (size_t i = 0; i < 32; ++i) {
    key[i] = cipher[i] ^ 0xAAu;
  }
  return 0;
#endif
}

/**
 * Generate a signing key pair.
 */
int pqcrypto_sign_keypair(uint8_t *pk, uint8_t *sk) {
#ifdef HAVE_PQCRYPTO
  return pqcrystals_dilithium2_ref_keypair(pk, sk);
#else
  for (size_t i = 0; i < 32; ++i) {
    pk[i] = (uint8_t)(i + 3u);
    sk[i] = (uint8_t)(i + 4u);
  }
  return 0;
#endif
}

/**
 * Sign a message using the private key.
 */
int pqcrypto_sign(uint8_t *sig, size_t *sig_len, const uint8_t *msg,
                  size_t msg_len, const uint8_t *sk) {
#ifdef HAVE_PQCRYPTO
  return pqcrystals_dilithium2_ref_sign(sig, sig_len, msg, msg_len, sk);
#else
  size_t n = msg_len < 32 ? msg_len : 32;
  for (size_t i = 0; i < n; ++i) {
    sig[i] = msg[i] ^ sk[i % 32];
  }
  *sig_len = n;
  return 0;
#endif
}

/**
 * Verify a message signature using the public key.
 */
int pqcrypto_verify(const uint8_t *sig, size_t sig_len, const uint8_t *msg,
                    size_t msg_len, const uint8_t *pk) {
#ifdef HAVE_PQCRYPTO
  return pqcrystals_dilithium2_ref_verify(sig, sig_len, msg, msg_len, pk);
#else
  size_t n = sig_len < msg_len ? sig_len : msg_len;
  for (size_t i = 0; i < n; ++i) {
    if ((sig[i] ^ pk[i % 32]) != msg[i]) {
      return -1;
    }
  }
  return 0;
#endif
}
