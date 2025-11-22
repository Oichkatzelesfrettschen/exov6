# Post-Quantum Cryptography (PQC) Integration

This document details the integration of Post-Quantum Cryptography in the Phoenix Exokernel.

## Overview

The system uses lattice-based cryptography to secure capabilities and IPC against quantum adversaries. This ensures long-term security for the Phoenix Distributed Access Control (PDAC) System V2 architecture.

## Cryptographic Primitives

### Lattice-Based Cryptography
The kernel primarily uses lattice-based primitives due to their balanced performance and security characteristics.

*   **Signatures**: Dilithium-style signatures are used for capability authentication.
*   **Key Encapsulation**: Kyber-style KEM is used for establishing secure IPC channels.
*   **Parameters**: `N=256` dimension is used as the standard security level (comparable to AES-128/SHA-256 but quantum-safe).

### Implementation (`kernel/crypto.c`, `kernel/lattice_ipc.c`)

*   **Key Storage**: Keys are stored in `lattice_public_key_t` and `lattice_private_key_t` structures defined in `include/lattice_types.h`.
*   **Entropy**: Key generation mixes system entropy with post-quantum noise sources.
*   **Constant-Time**: Critical operations (verification, comparison) are implemented in constant time to prevent side-channel attacks.

## Integration Points

### 1. Capability System
Capabilities (`exo_cap`) include an `auth_tag` which is a lattice signature.
*   **Generation**: When a capability is created (e.g., `cap_grant`), the kernel signs it using the master lattice key.
*   **Verification**: When a capability is presented, the kernel verifies the signature.

### 2. Secure IPC
Inter-Process Communication uses an authenticated channel established via PQC KEM.
*   **Handshake**: Processes exchange public keys and encapsulate a shared secret.
*   **Session**: The shared secret drives a symmetric cipher (ChaCha20-Poly1305 or similar) for the session, but the root of trust is PQC.

## Performance Optimizations

*   **SIMD Acceleration**: AVX-512 implementations are available for x86_64 (Tier-1) to accelerate polynomial multiplication.
*   **Stack Usage**: Large lattice keys are handled carefully to avoid kernel stack overflow.

## Roadmap

*   **Hybrid Mode**: Option to combine ECC with Lattice for transition periods.
*   **Standards Compliance**: Alignment with final NIST FIPS 203/204 standards.
