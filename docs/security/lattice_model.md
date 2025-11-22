# Lattice-Based Security Primitives

This document details the lattice-based cryptography and security primitives used in the Phoenix Exokernel.

## 1. Overview

The kernel employs post-quantum secure cryptographic primitives based on lattice problems (e.g., LWE, NTRU). These are used for capability authentication and secure IPC.

## 2. Cryptographic Types

Defined in `include/lattice_types.h`, the kernel uses fixed-size structures to avoid dynamic allocation overhead and ensure deterministic behavior.

*   **Lattice Dimension**: `N = 256`
*   **Key Size**: Defined by `LATTICE_KEY_BYTES`.
*   **Signature Size**: `LATTICE_SIG_BYTES` (approx 2.4KB for Dilithium2-level security).

### Core Structures

```c
typedef struct {
    uint16_t coeffs[256];  /* Polynomial vector coefficients */
} lattice_poly_vec_t;

typedef struct {
    uint8_t key_data[LATTICE_KEY_BYTES];
} lattice_public_key_t;
```

### Octonions
The system also defines `octonion_t`, an 8-tuple structure used for advanced capability schemes or multi-dimensional resource vectors.

```c
typedef union {
    double v[8];
    struct { double e0, e1, e2, e3, e4, e5, e6, e7; };
} octonion_t;
```

## 3. Entropy and Key Derivation

Implemented in `kernel/cap_security.c`.

*   **System Entropy**: Derived from system state (memory addresses, timing).
*   **Post-Quantum Mixing**: If available, PQ-KEM keypairs are generated and mixed into the entropy pool.
*   **Constant-Time Verification**: `cap_verify_constant_time` ensures that capability verification is resistant to timing side-channel attacks.
*   **Secret Storage**: The master capability secret is derived at boot and stored in `cap_secret`, which is then cleared from stack memory (`cap_secure_clear`).

## 4. Application

These primitives underpin the `auth_tag` in `exo_cap`, providing cryptographic proof of a capability's validity that cannot be forged, even by an attacker with infinite computing power (in the case of information-theoretic MACs) or quantum computers (in the case of lattice signatures).
