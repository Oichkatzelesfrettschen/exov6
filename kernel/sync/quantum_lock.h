#pragma once

#include <stdatomic.h>
#include <stdint.h>
#include <stdbool.h>
#include "ultimate_lock_synthesis.h"

/**
 * @file quantum_lock.h
 * @brief Quantum-ready lock primitives with post-quantum cryptographic authentication
 * 
 * This module provides lock primitives that are resistant to both classical and quantum
 * attacks, implementing post-quantum cryptographic algorithms for lock authentication,
 * quantum error correction for lock state integrity, and quantum-safe random number
 * generation for timing and scheduling decisions.
 */

// Post-Quantum Cryptographic Algorithms
#define DILITHIUM_SIGNATURE_SIZE    3293
#define KYBER_CIPHERTEXT_SIZE      1568
#define SPHINCS_SIGNATURE_SIZE     49856

// Quantum Error Correction Codes
#define QEC_SYNDROME_SIZE          32
#define QEC_STABILIZER_COUNT       64

// Quantum Random Number Generator
#define QRNG_ENTROPY_POOL_SIZE     4096
#define QRNG_RESEED_THRESHOLD      1000

/**
 * @brief Post-quantum cryptographic signature for lock authentication
 */
typedef struct pq_signature {
    uint8_t dilithium_sig[DILITHIUM_SIGNATURE_SIZE];
    uint8_t sphincs_sig[SPHINCS_SIGNATURE_SIZE];
    uint64_t timestamp_ns;
    uint32_t nonce;
    uint32_t algorithm_id;
} pq_signature_t;

/**
 * @brief Quantum error correction syndrome for lock state integrity
 */
typedef struct qec_syndrome {
    _Alignas(32) uint8_t stabilizers[QEC_SYNDROME_SIZE];
    atomic_uint32_t error_count;
    atomic_uint64_t correction_history;
    uint32_t code_type;  // Surface code, color code, etc.
} qec_syndrome_t;

/**
 * @brief Quantum random number generator state
 */
typedef struct quantum_rng {
    _Alignas(64) atomic_uint64_t entropy_pool[QRNG_ENTROPY_POOL_SIZE / 8];
    atomic_uint32_t pool_index;
    atomic_uint32_t reseed_counter;
    atomic_uint64_t last_reseed_time;
    struct {
        uint32_t quantum_source_available : 1;
        uint32_t hardware_verified : 1;
        uint32_t entropy_adequate : 1;
        uint32_t reserved : 29;
    } flags;
} quantum_rng_t;

/**
 * @brief Quantum-ready lock with post-quantum authentication
 */
typedef struct quantum_lock {
    _Alignas(128) 
    
    // Core lock state with quantum error correction
    atomic_uint64_t state;
    qec_syndrome_t qec_state;
    
    // Post-quantum cryptographic authentication
    pq_signature_t owner_signature;
    atomic_uint32_t auth_generation;
    
    // Quantum timing and scheduling
    quantum_rng_t qrng;
    atomic_uint64_t quantum_timestamp;
    
    // Performance and diagnostics
    struct {
        atomic_uint64_t acquisitions;
        atomic_uint64_t contentions;
        atomic_uint64_t quantum_errors_corrected;
        atomic_uint64_t auth_failures;
        atomic_uint64_t timing_corrections;
    } metrics;
    
    // Lock metadata
    struct {
        const char *name;
        uint32_t security_level;  // 128-bit, 192-bit, 256-bit
        uint32_t quantum_resistance;  // Years of protection estimate
        ultimate_lock_t *fallback_lock;  // Classical fallback
    } config;
    
} quantum_lock_t;

/**
 * @brief Quantum entanglement context for distributed locking
 */
typedef struct quantum_entanglement {
    _Alignas(64)
    
    // Bell state representation (|00⟩ + |11⟩)/√2
    struct {
        atomic_uint64_t qubit_a_state;
        atomic_uint64_t qubit_b_state;
        atomic_uint64_t entanglement_phase;
        atomic_uint32_t coherence_time_ns;
    } bell_state;
    
    // Quantum measurement results
    struct {
        atomic_uint32_t measurement_count;
        atomic_uint64_t correlation_violations;  // Bell inequality violations
        atomic_uint32_t decoherence_events;
    } measurements;
    
    // Network synchronization
    struct {
        atomic_uint64_t network_delay_ns;
        atomic_uint32_t sync_error_rate;
        atomic_uint64_t last_sync_time;
    } network;
    
} quantum_entanglement_t;

// API Functions

/**
 * @brief Initialize a quantum-ready lock
 * @param lock Pointer to quantum lock structure
 * @param security_level Cryptographic security level (128/192/256 bits)
 * @param name Human-readable lock name
 * @return 0 on success, negative errno on failure
 */
int quantum_lock_init(quantum_lock_t *lock, uint32_t security_level, const char *name);

/**
 * @brief Acquire quantum lock with post-quantum authentication
 * @param lock Pointer to quantum lock
 * @param timeout_ns Maximum wait time in nanoseconds
 * @return 0 on success, -ETIMEDOUT, -EAUTH, or other errno
 */
int quantum_lock_acquire(quantum_lock_t *lock, uint64_t timeout_ns);

/**
 * @brief Try to acquire quantum lock without blocking
 * @param lock Pointer to quantum lock
 * @return 0 on success, -EBUSY if already held, other errno on error
 */
int quantum_lock_trylock(quantum_lock_t *lock);

/**
 * @brief Release quantum lock with authentication verification
 * @param lock Pointer to quantum lock
 * @return 0 on success, negative errno on failure
 */
int quantum_lock_release(quantum_lock_t *lock);

/**
 * @brief Check if quantum lock is currently held (wait-free)
 * @param lock Pointer to quantum lock
 * @return true if locked, false if available
 */
bool quantum_lock_is_locked(const quantum_lock_t *lock);

/**
 * @brief Get current holder information
 * @param lock Pointer to quantum lock
 * @param holder_info Output buffer for holder details
 * @return 0 on success, negative errno on failure
 */
int quantum_lock_get_holder(const quantum_lock_t *lock, pq_signature_t *holder_info);

/**
 * @brief Perform quantum error correction on lock state
 * @param lock Pointer to quantum lock
 * @return Number of errors corrected, negative errno on failure
 */
int quantum_lock_error_correct(quantum_lock_t *lock);

// Quantum Cryptography Functions

/**
 * @brief Generate post-quantum digital signature
 * @param message Message to sign
 * @param message_len Length of message
 * @param signature Output signature structure
 * @param private_key Private key for signing
 * @return 0 on success, negative errno on failure
 */
int pq_crypto_sign(const void *message, size_t message_len, 
                   pq_signature_t *signature, const void *private_key);

/**
 * @brief Verify post-quantum digital signature
 * @param message Original message
 * @param message_len Length of message
 * @param signature Signature to verify
 * @param public_key Public key for verification
 * @return 0 if valid, negative errno if invalid or error
 */
int pq_crypto_verify(const void *message, size_t message_len,
                     const pq_signature_t *signature, const void *public_key);

/**
 * @brief Generate quantum-safe random bytes
 * @param qrng Quantum RNG state
 * @param output Buffer for random bytes
 * @param length Number of bytes to generate
 * @return 0 on success, negative errno on failure
 */
int quantum_rng_generate(quantum_rng_t *qrng, void *output, size_t length);

/**
 * @brief Reseed quantum RNG with fresh entropy
 * @param qrng Quantum RNG state
 * @return 0 on success, negative errno on failure
 */
int quantum_rng_reseed(quantum_rng_t *qrng);

// Quantum Error Correction Functions

/**
 * @brief Initialize quantum error correction for lock state
 * @param syndrome QEC syndrome structure
 * @param code_type Type of error correction code (surface, color, etc.)
 * @return 0 on success, negative errno on failure
 */
int qec_init(qec_syndrome_t *syndrome, uint32_t code_type);

/**
 * @brief Detect and correct quantum errors in lock state
 * @param syndrome QEC syndrome
 * @param lock_state Pointer to lock state to correct
 * @return Number of errors corrected, negative errno on failure
 */
int qec_correct_errors(qec_syndrome_t *syndrome, atomic_uint64_t *lock_state);

/**
 * @brief Calculate syndrome for quantum error detection
 * @param syndrome QEC syndrome structure
 * @param lock_state Current lock state
 * @return 0 if no errors, positive if errors detected, negative errno on failure
 */
int qec_calculate_syndrome(qec_syndrome_t *syndrome, uint64_t lock_state);

// Quantum Entanglement Functions (for distributed locking)

/**
 * @brief Initialize quantum entanglement context
 * @param entanglement Entanglement context
 * @return 0 on success, negative errno on failure
 */
int quantum_entanglement_init(quantum_entanglement_t *entanglement);

/**
 * @brief Create entangled lock pair for distributed synchronization
 * @param local_lock Local quantum lock
 * @param remote_lock Remote quantum lock (network reference)
 * @param entanglement Entanglement context
 * @return 0 on success, negative errno on failure
 */
int quantum_entanglement_create_pair(quantum_lock_t *local_lock,
                                     quantum_lock_t *remote_lock,
                                     quantum_entanglement_t *entanglement);

/**
 * @brief Measure entangled lock state (collapses superposition)
 * @param entanglement Entanglement context
 * @param measurement_basis Basis for measurement (X, Y, Z)
 * @return Measurement result, negative errno on failure
 */
int quantum_entanglement_measure(quantum_entanglement_t *entanglement, char measurement_basis);

/**
 * @brief Check Bell inequality violation for entanglement verification
 * @param entanglement Entanglement context
 * @return Violation parameter S (S > 2 indicates quantum correlation)
 */
double quantum_entanglement_bell_test(const quantum_entanglement_t *entanglement);

// Advanced Quantum Features

/**
 * @brief Implement quantum key distribution for lock keys
 * @param lock Quantum lock
 * @param remote_endpoint Network endpoint for key exchange
 * @return 0 on success, negative errno on failure
 */
int quantum_lock_qkd_exchange(quantum_lock_t *lock, const char *remote_endpoint);

/**
 * @brief Perform quantum teleportation of lock state
 * @param source_lock Source lock to teleport
 * @param dest_lock Destination lock
 * @param entanglement Entanglement context
 * @return 0 on success, negative errno on failure
 */
int quantum_lock_teleport_state(const quantum_lock_t *source_lock,
                                quantum_lock_t *dest_lock,
                                quantum_entanglement_t *entanglement);

/**
 * @brief Apply quantum annealing for lock contention optimization
 * @param locks Array of contending quantum locks
 * @param count Number of locks
 * @param temperature Annealing temperature
 * @return Optimal lock acquisition order, negative errno on failure
 */
int quantum_lock_anneal_schedule(quantum_lock_t **locks, size_t count, double temperature);

// Statistics and Diagnostics

/**
 * @brief Get comprehensive quantum lock statistics
 * @param lock Quantum lock
 * @param stats Output statistics structure
 * @return 0 on success, negative errno on failure
 */
int quantum_lock_get_stats(const quantum_lock_t *lock, struct quantum_lock_stats *stats);

/**
 * @brief Reset quantum lock metrics
 * @param lock Quantum lock
 * @return 0 on success, negative errno on failure
 */
int quantum_lock_reset_stats(quantum_lock_t *lock);

/**
 * @brief Perform quantum lock health check
 * @param lock Quantum lock
 * @return Health score 0-100, negative errno on failure
 */
int quantum_lock_health_check(const quantum_lock_t *lock);

// Configuration and Tuning

/**
 * @brief Set quantum lock security parameters
 * @param lock Quantum lock
 * @param security_level New security level
 * @param quantum_resistance Target resistance in years
 * @return 0 on success, negative errno on failure
 */
int quantum_lock_configure_security(quantum_lock_t *lock, uint32_t security_level, 
                                    uint32_t quantum_resistance);

/**
 * @brief Enable/disable quantum features dynamically
 * @param lock Quantum lock
 * @param features Bitmask of features to enable/disable
 * @return 0 on success, negative errno on failure
 */
int quantum_lock_configure_features(quantum_lock_t *lock, uint64_t features);

// Feature flags for quantum_lock_configure_features
#define QUANTUM_FEATURE_ERROR_CORRECTION    (1ULL << 0)
#define QUANTUM_FEATURE_PQ_CRYPTO          (1ULL << 1)
#define QUANTUM_FEATURE_ENTANGLEMENT       (1ULL << 2)
#define QUANTUM_FEATURE_QKD                (1ULL << 3)
#define QUANTUM_FEATURE_TELEPORTATION      (1ULL << 4)
#define QUANTUM_FEATURE_ANNEALING          (1ULL << 5)
#define QUANTUM_FEATURE_BELL_TESTS         (1ULL << 6)
#define QUANTUM_FEATURE_QUANTUM_RNG        (1ULL << 7)

// Security levels
#define QUANTUM_SECURITY_128BIT            128
#define QUANTUM_SECURITY_192BIT            192
#define QUANTUM_SECURITY_256BIT            256

// QEC code types
#define QEC_CODE_SURFACE                   1
#define QEC_CODE_COLOR                     2
#define QEC_CODE_TOPOLOGICAL              3
#define QEC_CODE_STABILIZER               4

// Statistical structure
struct quantum_lock_stats {
    uint64_t total_acquisitions;
    uint64_t total_contentions;
    uint64_t average_hold_time_ns;
    uint64_t max_hold_time_ns;
    uint64_t quantum_errors_detected;
    uint64_t quantum_errors_corrected;
    uint64_t auth_successes;
    uint64_t auth_failures;
    uint64_t entanglement_events;
    uint64_t decoherence_events;
    double average_fidelity;
    double bell_violation_parameter;
    uint32_t current_security_level;
    uint32_t quantum_resistance_years;
};