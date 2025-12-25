/**
 * @file serialization_simple.c
 * @brief Simplified serialization system for compilation testing
 */

#include "../../include/ipc/serialization.h"
#include "../string.h"
#include <stdatomic.h>
#include <time.h>
#include <stdio.h>

// Portable cycle counter fallback
static inline uint64_t get_cycles(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000000000ULL + ts.tv_nsec;
}

// =============================================================================
// RAW SERIALIZER
// =============================================================================

static size_t raw_encode(const void* msg, size_t msg_size,
                         void* buf, size_t buf_size) {
    if (!msg || !buf || msg_size > buf_size) {
        return 0;
    }
    
    uint64_t start_cycles = get_cycles();
    memcpy(buf, msg, msg_size);
    uint64_t end_cycles = get_cycles();
    
    extern serializer_t raw_serializer;
    atomic_fetch_add(&raw_serializer.stats.encode_calls, 1);
    atomic_fetch_add(&raw_serializer.stats.bytes_encoded, msg_size);
    
    uint64_t cycles = end_cycles - start_cycles;
    uint64_t old_avg = raw_serializer.stats.avg_encode_cycles;
    raw_serializer.stats.avg_encode_cycles = (old_avg * 7 + cycles) / 8;
    
    return msg_size;
}

static size_t raw_decode(const void* buf, size_t buf_size,
                         void* msg, size_t msg_size) {
    if (!buf || !msg || buf_size > msg_size) {
        return 0;
    }
    
    uint64_t start_cycles = get_cycles();
    memcpy(msg, buf, buf_size);
    uint64_t end_cycles = get_cycles();
    
    extern serializer_t raw_serializer;
    atomic_fetch_add(&raw_serializer.stats.decode_calls, 1);
    atomic_fetch_add(&raw_serializer.stats.bytes_decoded, buf_size);
    
    uint64_t cycles = end_cycles - start_cycles;
    uint64_t old_avg = raw_serializer.stats.avg_decode_cycles;
    raw_serializer.stats.avg_decode_cycles = (old_avg * 7 + cycles) / 8;
    
    return buf_size;
}

static bool raw_validate(const void* buf, size_t size) {
    return buf != NULL && size > 0;
}

// =============================================================================
// CAP'N PROTO LITE SERIALIZER
// =============================================================================

typedef struct {
    uint32_t magic;
    uint32_t size;
    uint32_t checksum;
    uint32_t reserved;
} capnp_lite_header_t;

#define CAPNP_LITE_MAGIC 0xCAFEBABE

static uint32_t simple_checksum(const void* data, size_t size) {
    const uint8_t* bytes = (const uint8_t*)data;
    uint32_t checksum = 0;
    for (size_t i = 0; i < size; i++) {
        checksum += bytes[i];
    }
    return checksum;
}

static size_t capnp_lite_encode(const void* msg, size_t msg_size,
                               void* buf, size_t buf_size) {
    if (!msg || !buf || buf_size < sizeof(capnp_lite_header_t) + msg_size) {
        return 0;
    }
    
    capnp_lite_header_t* header = (capnp_lite_header_t*)buf;
    header->magic = CAPNP_LITE_MAGIC;
    header->size = msg_size;
    header->checksum = simple_checksum(msg, msg_size);
    header->reserved = 0;
    
    memcpy((uint8_t*)buf + sizeof(capnp_lite_header_t), msg, msg_size);
    
    extern serializer_t capnp_lite_serializer;
    atomic_fetch_add(&capnp_lite_serializer.stats.encode_calls, 1);
    atomic_fetch_add(&capnp_lite_serializer.stats.bytes_encoded, msg_size);
    
    return sizeof(capnp_lite_header_t) + msg_size;
}

static size_t capnp_lite_decode(const void* buf, size_t buf_size,
                               void* msg, size_t msg_size) {
    if (!buf || !msg || buf_size < sizeof(capnp_lite_header_t)) {
        return 0;
    }
    
    const capnp_lite_header_t* header = (const capnp_lite_header_t*)buf;
    if (header->magic != CAPNP_LITE_MAGIC || header->size > msg_size) {
        return 0;
    }
    
    const uint8_t* payload = (const uint8_t*)buf + sizeof(capnp_lite_header_t);
    uint32_t checksum = simple_checksum(payload, header->size);
    if (checksum != header->checksum) {
        return 0;
    }
    
    memcpy(msg, payload, header->size);
    
    extern serializer_t capnp_lite_serializer;
    atomic_fetch_add(&capnp_lite_serializer.stats.decode_calls, 1);
    atomic_fetch_add(&capnp_lite_serializer.stats.bytes_decoded, header->size);
    
    return header->size;
}

static bool capnp_lite_validate(const void* buf, size_t size) {
    if (!buf || size < sizeof(capnp_lite_header_t)) {
        return false;
    }
    
    const capnp_lite_header_t* header = (const capnp_lite_header_t*)buf;
    return header->magic == CAPNP_LITE_MAGIC && 
           header->size <= (size - sizeof(capnp_lite_header_t));
}

// =============================================================================
// CAP'N PROTO FULL SERIALIZER (Stub)
// =============================================================================

static size_t capnp_full_encode(const void* msg, size_t msg_size,
                               void* buf, size_t buf_size) {
    // For now, fall back to lite encoding
    return capnp_lite_encode(msg, msg_size, buf, buf_size);
}

static size_t capnp_full_decode(const void* buf, size_t buf_size,
                               void* msg, size_t msg_size) {
    // For now, fall back to lite decoding
    return capnp_lite_decode(buf, buf_size, msg, msg_size);
}

static bool capnp_full_validate(const void* buf, size_t size) {
    return capnp_lite_validate(buf, size);
}

// =============================================================================
// SERIALIZER INSTANCES
// =============================================================================

serializer_t raw_serializer = {
    .type = SERIAL_RAW,
    .name = "Raw",
    .encode = raw_encode,
    .decode = raw_decode,
    .validate = raw_validate,
    .stats = {0}
};

serializer_t capnp_lite_serializer = {
    .type = SERIAL_CAPNP_LITE,
    .name = "Cap'n Proto Lite",
    .encode = capnp_lite_encode,
    .decode = capnp_lite_decode,
    .validate = capnp_lite_validate,
    .stats = {0}
};

serializer_t capnp_full_serializer = {
    .type = SERIAL_CAPNP_FULL,
    .name = "Cap'n Proto Full",
    .encode = capnp_full_encode,
    .decode = capnp_full_decode,
    .validate = capnp_full_validate,
    .stats = {0}
};

// =============================================================================
// INITIALIZATION
// =============================================================================

void init_serialization_system(void) {
    // Initialize serializer statistics
    memset(&raw_serializer.stats, 0, sizeof(raw_serializer.stats));
    memset(&capnp_lite_serializer.stats, 0, sizeof(capnp_lite_serializer.stats));
    memset(&capnp_full_serializer.stats, 0, sizeof(capnp_full_serializer.stats));
}

void shutdown_serialization_system(void) {
    // Nothing to clean up currently
}

// =============================================================================
// DEBUGGING
// =============================================================================

void print_serialization_stats(void) {
    printf("=== Serialization Statistics ===\n");
    printf("Raw Serializer:\n");
    printf("  Encode calls: %llu\n", raw_serializer.stats.encode_calls);
    printf("  Decode calls: %llu\n", raw_serializer.stats.decode_calls);
    printf("  Bytes encoded: %llu\n", raw_serializer.stats.bytes_encoded);
    printf("  Bytes decoded: %llu\n", raw_serializer.stats.bytes_decoded);
    
    printf("Cap'n Proto Lite Serializer:\n");
    printf("  Encode calls: %llu\n", capnp_lite_serializer.stats.encode_calls);
    printf("  Decode calls: %llu\n", capnp_lite_serializer.stats.decode_calls);
    printf("  Bytes encoded: %llu\n", capnp_lite_serializer.stats.bytes_encoded);
    printf("  Bytes decoded: %llu\n", capnp_lite_serializer.stats.bytes_decoded);
}