/**
 * @file serialization.c
 * @brief Implementation of unified serialization system
 * 
 * Provides three levels of serialization complexity based on trust:
 * 1. Raw - zero overhead for kernel
 * 2. Cap'n Proto Lite - basic safety for LibOS
 * 3. Cap'n Proto Full - complete protocol for userspace
 */

#include "../../include/ipc/serialization.h"
#include "capnp_helpers.h"
#include "../string.h"
#include <stdatomic.h>

// =============================================================================
// RAW SERIALIZER - Zero Overhead for Kernel
// =============================================================================

static size_t raw_encode(const void* msg, size_t msg_size,
                         void* buf, size_t buf_size) {
    if (!msg || !buf || msg_size > buf_size) {
        return 0;
    }
    
    // Track performance
    uint64_t start_cycles = __builtin_ia32_rdtsc();
    
    memcpy(buf, msg, msg_size);
    
    uint64_t end_cycles = __builtin_ia32_rdtsc();
    
    // Update statistics
    serializer_t* self = &raw_serializer;
    atomic_fetch_add(&self->stats.encode_calls, 1);
    atomic_fetch_add(&self->stats.bytes_encoded, msg_size);
    
    // Update average cycles (simplified moving average)
    uint64_t cycles = end_cycles - start_cycles;
    uint64_t old_avg = self->stats.avg_encode_cycles;
    self->stats.avg_encode_cycles = (old_avg * 7 + cycles) / 8;
    
    return msg_size;
}

static size_t raw_decode(const void* buf, size_t buf_size,
                         void* msg, size_t msg_size) {
    if (!buf || !msg || buf_size > msg_size) {
        return 0;
    }
    
    uint64_t start_cycles = __builtin_ia32_rdtsc();
    
    memcpy(msg, buf, buf_size);
    
    uint64_t end_cycles = __builtin_ia32_rdtsc();
    
    // Update statistics
    serializer_t* self = &raw_serializer;
    atomic_fetch_add(&self->stats.decode_calls, 1);
    atomic_fetch_add(&self->stats.bytes_decoded, buf_size);
    
    uint64_t cycles = end_cycles - start_cycles;
    uint64_t old_avg = self->stats.avg_decode_cycles;
    self->stats.avg_decode_cycles = (old_avg * 7 + cycles) / 8;
    
    return buf_size;
}

serializer_t raw_serializer = {
    .type = SERIAL_RAW,
    .name = "raw_memcpy",
    .encode = raw_encode,
    .decode = raw_decode,
    .validate = NULL,  // No validation needed for trusted paths
    .encode_ex = NULL,
    .decode_ex = NULL,
    .stats = {0}
};

// =============================================================================
// CAP'N PROTO LITE - Basic Safety for LibOS
// =============================================================================

typedef struct {
    uint32_t magic;      // 0xCAFEBABE for validation
    uint32_t version;    // Protocol version
    uint32_t msg_size;   // Size of actual message
    uint32_t checksum;   // Simple XOR checksum
} capnp_lite_header_t;

#define CAPNP_LITE_MAGIC 0xCAFEBABE
#define CAPNP_LITE_VERSION 1

static uint32_t compute_checksum(const void* data, size_t size) {
    const uint32_t* words = (const uint32_t*)data;
    size_t word_count = size / sizeof(uint32_t);
    uint32_t checksum = 0;
    
    for (size_t i = 0; i < word_count; i++) {
        checksum ^= words[i];
    }
    
    // Handle remaining bytes
    if (size % sizeof(uint32_t)) {
        uint32_t last_word = 0;
        memcpy(&last_word, (uint8_t*)data + (word_count * sizeof(uint32_t)),
               size % sizeof(uint32_t));
        checksum ^= last_word;
    }
    
    return checksum;
}

static size_t capnp_lite_encode(const void* msg, size_t msg_size,
                                void* buf, size_t buf_size) {
    size_t total_size = sizeof(capnp_lite_header_t) + msg_size;
    
    if (!msg || !buf || total_size > buf_size) {
        return 0;
    }
    
    uint64_t start_cycles = __builtin_ia32_rdtsc();
    
    // Prepare header
    capnp_lite_header_t* header = (capnp_lite_header_t*)buf;
    header->magic = CAPNP_LITE_MAGIC;
    header->version = CAPNP_LITE_VERSION;
    header->msg_size = msg_size;
    
    // Copy message
    memcpy((uint8_t*)buf + sizeof(capnp_lite_header_t), msg, msg_size);
    
    // Compute checksum
    header->checksum = compute_checksum(msg, msg_size);
    
    uint64_t end_cycles = __builtin_ia32_rdtsc();
    
    // Update statistics
    serializer_t* self = &capnp_lite_serializer;
    atomic_fetch_add(&self->stats.encode_calls, 1);
    atomic_fetch_add(&self->stats.bytes_encoded, total_size);
    
    uint64_t cycles = end_cycles - start_cycles;
    uint64_t old_avg = self->stats.avg_encode_cycles;
    self->stats.avg_encode_cycles = (old_avg * 7 + cycles) / 8;
    
    return total_size;
}

static size_t capnp_lite_decode(const void* buf, size_t buf_size,
                                void* msg, size_t msg_size) {
    if (!buf || !msg || buf_size < sizeof(capnp_lite_header_t)) {
        return 0;
    }
    
    uint64_t start_cycles = __builtin_ia32_rdtsc();
    
    const capnp_lite_header_t* header = (const capnp_lite_header_t*)buf;
    
    // Validate header
    if (header->magic != CAPNP_LITE_MAGIC ||
        header->version != CAPNP_LITE_VERSION ||
        header->msg_size > msg_size ||
        header->msg_size + sizeof(capnp_lite_header_t) > buf_size) {
        atomic_fetch_add(&capnp_lite_serializer.stats.errors, 1);
        return 0;
    }
    
    // Copy message
    const void* msg_data = (const uint8_t*)buf + sizeof(capnp_lite_header_t);
    memcpy(msg, msg_data, header->msg_size);
    
    // Verify checksum
    uint32_t checksum = compute_checksum(msg_data, header->msg_size);
    if (checksum != header->checksum) {
        atomic_fetch_add(&capnp_lite_serializer.stats.errors, 1);
        return 0;
    }
    
    uint64_t end_cycles = __builtin_ia32_rdtsc();
    
    // Update statistics
    serializer_t* self = &capnp_lite_serializer;
    atomic_fetch_add(&self->stats.decode_calls, 1);
    atomic_fetch_add(&self->stats.bytes_decoded, header->msg_size);
    
    uint64_t cycles = end_cycles - start_cycles;
    uint64_t old_avg = self->stats.avg_decode_cycles;
    self->stats.avg_decode_cycles = (old_avg * 7 + cycles) / 8;
    
    return header->msg_size;
}

static bool capnp_lite_validate(const void* buf, size_t size) {
    if (!buf || size < sizeof(capnp_lite_header_t)) {
        return false;
    }
    
    const capnp_lite_header_t* header = (const capnp_lite_header_t*)buf;
    
    // Basic validation
    if (header->magic != CAPNP_LITE_MAGIC ||
        header->version != CAPNP_LITE_VERSION ||
        header->msg_size + sizeof(capnp_lite_header_t) > size) {
        return false;
    }
    
    // Verify checksum
    const void* msg_data = (const uint8_t*)buf + sizeof(capnp_lite_header_t);
    uint32_t checksum = compute_checksum(msg_data, header->msg_size);
    
    return checksum == header->checksum;
}

serializer_t capnp_lite_serializer = {
    .type = SERIAL_CAPNP_LITE,
    .name = "capnp_lite",
    .encode = capnp_lite_encode,
    .decode = capnp_lite_decode,
    .validate = capnp_lite_validate,
    .encode_ex = NULL,
    .decode_ex = NULL,
    .stats = {0}
};

// =============================================================================
// CAP'N PROTO FULL - Complete Protocol for Userspace
// =============================================================================

static size_t capnp_full_encode(const void* msg, size_t msg_size,
                                void* buf, size_t buf_size) {
    uint64_t start_cycles = __builtin_ia32_rdtsc();
    
    // Use the existing Cap'n Proto helpers
    size_t encoded_size = capnp_encode(msg, msg_size, buf);
    
    if (encoded_size == 0) {
        atomic_fetch_add(&capnp_full_serializer.stats.errors, 1);
        return 0;
    }
    
    uint64_t end_cycles = __builtin_ia32_rdtsc();
    
    // Update statistics
    serializer_t* self = &capnp_full_serializer;
    atomic_fetch_add(&self->stats.encode_calls, 1);
    atomic_fetch_add(&self->stats.bytes_encoded, encoded_size);
    
    uint64_t cycles = end_cycles - start_cycles;
    uint64_t old_avg = self->stats.avg_encode_cycles;
    self->stats.avg_encode_cycles = (old_avg * 7 + cycles) / 8;
    
    return encoded_size;
}

static size_t capnp_full_decode(const void* buf, size_t buf_size,
                                void* msg, size_t msg_size) {
    uint64_t start_cycles = __builtin_ia32_rdtsc();
    
    // Use the existing Cap'n Proto helpers
    size_t decoded_size = capnp_decode(msg, msg_size, buf);
    
    if (decoded_size == 0) {
        atomic_fetch_add(&capnp_full_serializer.stats.errors, 1);
        return 0;
    }
    
    uint64_t end_cycles = __builtin_ia32_rdtsc();
    
    // Update statistics
    serializer_t* self = &capnp_full_serializer;
    atomic_fetch_add(&self->stats.decode_calls, 1);
    atomic_fetch_add(&self->stats.bytes_decoded, decoded_size);
    
    uint64_t cycles = end_cycles - start_cycles;
    uint64_t old_avg = self->stats.avg_decode_cycles;
    self->stats.avg_decode_cycles = (old_avg * 7 + cycles) / 8;
    
    return decoded_size;
}

static bool capnp_full_validate(const void* buf, size_t size) {
    if (!buf || size < sizeof(capnp_message_header_t)) {
        return false;
    }
    
    const capnp_message_header_t* header = (const capnp_message_header_t*)buf;
    uint32_t segment_count = header->segment_count + 1;
    
    if (segment_count > 16) {
        return false;
    }
    
    // Calculate expected size
    size_t expected_size = sizeof(capnp_message_header_t);
    expected_size += segment_count * sizeof(uint32_t);
    if (segment_count % 2 == 0) {
        expected_size += sizeof(uint32_t); // Padding
    }
    
    if (size < expected_size) {
        return false;
    }
    
    // Additional validation could be added here
    return true;
}

static serial_error_t capnp_full_encode_ex(const void* msg, size_t msg_size,
                                           void* buf, size_t buf_size,
                                           size_t* encoded_size) {
    if (!msg || !buf || !encoded_size) {
        return SERIAL_ERR_INVALID_MESSAGE;
    }
    
    size_t size = capnp_full_encode(msg, msg_size, buf, buf_size);
    if (size == 0) {
        return SERIAL_ERR_BUFFER_TOO_SMALL;
    }
    
    *encoded_size = size;
    return SERIAL_OK;
}

static serial_error_t capnp_full_decode_ex(const void* buf, size_t buf_size,
                                           void* msg, size_t msg_size,
                                           size_t* decoded_size) {
    if (!buf || !msg || !decoded_size) {
        return SERIAL_ERR_INVALID_MESSAGE;
    }
    
    if (!capnp_full_validate(buf, buf_size)) {
        return SERIAL_ERR_INVALID_MESSAGE;
    }
    
    size_t size = capnp_full_decode(buf, buf_size, msg, msg_size);
    if (size == 0) {
        return SERIAL_ERR_BUFFER_TOO_SMALL;
    }
    
    *decoded_size = size;
    return SERIAL_OK;
}

serializer_t capnp_full_serializer = {
    .type = SERIAL_CAPNP_FULL,
    .name = "capnp_full",
    .encode = capnp_full_encode,
    .decode = capnp_full_decode,
    .validate = capnp_full_validate,
    .encode_ex = capnp_full_encode_ex,
    .decode_ex = capnp_full_decode_ex,
    .stats = {0}
};

// =============================================================================
// SERIALIZATION BENCHMARKING
// =============================================================================

#ifdef ENABLE_SERIAL_BENCHMARK

typedef struct {
    uint32_t field1;
    uint64_t field2;
    uint8_t data[256];
} benchmark_msg_t;

void benchmark_serializers(void) {
    benchmark_msg_t msg = {
        .field1 = 0x12345678,
        .field2 = 0xDEADBEEFCAFEBABE,
    };
    
    // Fill data with pattern
    for (int i = 0; i < 256; i++) {
        msg.data[i] = i;
    }
    
    uint8_t buffer[1024];
    benchmark_msg_t decoded;
    
    // Benchmark each serializer
    serializer_t* serializers[] = {
        &raw_serializer,
        &capnp_lite_serializer,
        &capnp_full_serializer
    };
    
    for (int s = 0; s < 3; s++) {
        serializer_t* ser = serializers[s];
        
        // Warm up
        for (int i = 0; i < 100; i++) {
            ser->encode(&msg, sizeof(msg), buffer, sizeof(buffer));
            ser->decode(buffer, sizeof(buffer), &decoded, sizeof(decoded));
        }
        
        // Actual benchmark
        uint64_t encode_total = 0;
        uint64_t decode_total = 0;
        int iterations = 10000;
        
        for (int i = 0; i < iterations; i++) {
            uint64_t start = __builtin_ia32_rdtsc();
            size_t encoded = ser->encode(&msg, sizeof(msg), buffer, sizeof(buffer));
            uint64_t encode_end = __builtin_ia32_rdtsc();
            
            ser->decode(buffer, encoded, &decoded, sizeof(decoded));
            uint64_t decode_end = __builtin_ia32_rdtsc();
            
            encode_total += (encode_end - start);
            decode_total += (decode_end - encode_end);
        }
        
        printf("Serializer: %s\n", ser->name);
        printf("  Avg encode cycles: %lu\n", encode_total / iterations);
        printf("  Avg decode cycles: %lu\n", decode_total / iterations);
        printf("  Total calls: %lu encode, %lu decode\n",
               ser->stats.encode_calls, ser->stats.decode_calls);
        printf("  Total bytes: %lu encoded, %lu decoded\n",
               ser->stats.bytes_encoded, ser->stats.bytes_decoded);
        printf("  Errors: %lu\n\n", ser->stats.errors);
    }
}

#endif // ENABLE_SERIAL_BENCHMARK

// =============================================================================
// INITIALIZATION
// =============================================================================

void init_serialization_system(void) {
    // Reset all statistics
    memset(&raw_serializer.stats, 0, sizeof(raw_serializer.stats));
    memset(&capnp_lite_serializer.stats, 0, sizeof(capnp_lite_serializer.stats));
    memset(&capnp_full_serializer.stats, 0, sizeof(capnp_full_serializer.stats));
    
    #ifdef ENABLE_SERIAL_BENCHMARK
    // Run benchmarks if enabled
    benchmark_serializers();
    #endif
}