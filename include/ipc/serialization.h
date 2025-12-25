/**
 * @file serialization.h
 * @brief Unified serialization interface for FeuerBird exokernel
 * 
 * This provides a layered serialization architecture that adapts based on
 * capability trust levels and performance requirements. It synthesizes:
 * - Raw memcpy for trusted kernel paths
 * - Cap'n Proto Lite for LibOS communication
 * - Full Cap'n Proto for userspace compatibility
 */

#ifndef SERIALIZATION_H
#define SERIALIZATION_H

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include "../exo.h"

// =============================================================================
// SERIALIZATION TYPES
// =============================================================================

typedef enum {
    SERIAL_RAW,           // Direct memcpy for trusted kernel paths
    SERIAL_CAPNP_LITE,    // Basic Cap'n Proto encoding with bounds checking
    SERIAL_CAPNP_FULL,    // Full Cap'n Proto protocol support
    SERIAL_PROTOBUF,      // Future: Protocol Buffers compatibility
    SERIAL_FLATBUF,       // Future: FlatBuffers compatibility
    SERIAL_MSGPACK,       // Future: MessagePack compatibility
} serial_type_t;

typedef enum {
    SERIAL_OK = 0,
    SERIAL_ERR_INVALID_TYPE,
    SERIAL_ERR_BUFFER_TOO_SMALL,
    SERIAL_ERR_INVALID_MESSAGE,
    SERIAL_ERR_OUT_OF_MEMORY,
    SERIAL_ERR_TRAVERSAL_LIMIT,
    SERIAL_ERR_CAPABILITY_DENIED,
} serial_error_t;

// =============================================================================
// SERIALIZATION INTERFACE
// =============================================================================

typedef struct serializer {
    serial_type_t type;
    const char* name;
    
    // Core operations
    size_t (*encode)(const void* msg, size_t msg_size, 
                     void* buf, size_t buf_size);
    size_t (*decode)(const void* buf, size_t buf_size,
                     void* msg, size_t msg_size);
    bool (*validate)(const void* buf, size_t size);
    
    // Extended operations (optional)
    serial_error_t (*encode_ex)(const void* msg, size_t msg_size,
                                void* buf, size_t buf_size,
                                size_t* encoded_size);
    serial_error_t (*decode_ex)(const void* buf, size_t buf_size,
                                void* msg, size_t msg_size,
                                size_t* decoded_size);
    
    // Performance metrics
    struct {
        uint64_t encode_calls;
        uint64_t decode_calls;
        uint64_t bytes_encoded;
        uint64_t bytes_decoded;
        uint64_t errors;
        uint64_t avg_encode_cycles;
        uint64_t avg_decode_cycles;
    } stats;
} serializer_t;

// =============================================================================
// CAPABILITY-AWARE SERIALIZATION
// =============================================================================

/**
 * Select serializer based on capability trust level
 * This implements the exokernel philosophy: mechanism not policy
 */
static inline serializer_t* exo_select_serializer(exo_cap cap) {
    // Extract trust level from capability rights field
    uint32_t trust_level = (cap.rights >> 16) & 0xF;
    
    if (trust_level >= 0xE) {
        // Kernel-level trust: use raw memcpy
        extern serializer_t raw_serializer;
        return &raw_serializer;
    } else if (trust_level >= 0x8) {
        // LibOS trust: use Cap'n Proto Lite
        extern serializer_t capnp_lite_serializer;
        return &capnp_lite_serializer;
    } else {
        // User-level: use full Cap'n Proto
        extern serializer_t capnp_full_serializer;
        return &capnp_full_serializer;
    }
}

/**
 * Serialize with automatic serializer selection
 */
static inline size_t exo_serialize(exo_cap cap, const void* msg, 
                                   size_t msg_size, void* buf, 
                                   size_t buf_size) {
    serializer_t* s = exo_select_serializer(cap);
    return s->encode(msg, msg_size, buf, buf_size);
}

/**
 * Deserialize with automatic serializer selection
 */
static inline size_t exo_deserialize(exo_cap cap, const void* buf,
                                     size_t buf_size, void* msg,
                                     size_t msg_size) {
    serializer_t* s = exo_select_serializer(cap);
    return s->decode(buf, buf_size, msg, msg_size);
}

// =============================================================================
// PERFORMANCE MONITORING
// =============================================================================

/**
 * Get serialization statistics for a capability
 */
static inline void exo_get_serial_stats(exo_cap cap, 
                                        struct serializer* stats_out) {
    serializer_t* s = exo_select_serializer(cap);
    if (stats_out) {
        *stats_out = *s;
    }
}

/**
 * Reset serialization statistics
 */
static inline void exo_reset_serial_stats(exo_cap cap) {
    serializer_t* s = exo_select_serializer(cap);
    s->stats.encode_calls = 0;
    s->stats.decode_calls = 0;
    s->stats.bytes_encoded = 0;
    s->stats.bytes_decoded = 0;
    s->stats.errors = 0;
    s->stats.avg_encode_cycles = 0;
    s->stats.avg_decode_cycles = 0;
}

// =============================================================================
// MESSAGE VALIDATION
// =============================================================================

/**
 * Validate a serialized message based on capability
 */
static inline bool exo_validate_message(exo_cap cap, const void* buf,
                                        size_t size) {
    serializer_t* s = exo_select_serializer(cap);
    if (s->validate) {
        return s->validate(buf, size);
    }
    return true; // No validation for raw serializer
}

// =============================================================================
// ZERO-COPY OPTIMIZATION
// =============================================================================

/**
 * Check if zero-copy is possible for this capability
 */
static inline bool exo_can_zero_copy(exo_cap cap) {
    serializer_t* s = exo_select_serializer(cap);
    return (s->type == SERIAL_RAW || s->type == SERIAL_CAPNP_LITE);
}

/**
 * Get direct pointer if zero-copy is possible
 */
static inline void* exo_get_zero_copy_ptr(exo_cap cap, void* buf,
                                          size_t offset) {
    if (exo_can_zero_copy(cap)) {
        return (uint8_t*)buf + offset;
    }
    return NULL;
}

#endif // SERIALIZATION_H