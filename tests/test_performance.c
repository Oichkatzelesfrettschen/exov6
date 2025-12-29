/**
 * @file test_performance.c
 * @brief Performance test for IPC serialization layers
 */

#include "include/ipc/serialization.h"
#include "kernel/string.h"
#include <time.h>
#include <stdatomic.h>

// Test message structure
typedef struct {
    uint64_t timestamp;
    uint32_t sequence;
    uint32_t checksum;
    char payload[64];
} benchmark_message_t;

// Simple performance timer
static double get_time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1e9 + ts.tv_nsec;
}

// Simple serializers (from previous test)
static size_t raw_encode(const void* msg, size_t msg_size,
                         void* buf, size_t buf_size) {
    if (!msg || !buf || msg_size > buf_size) return 0;
    memcpy(buf, msg, msg_size);
    return msg_size;
}

static size_t raw_decode(const void* buf, size_t buf_size,
                         void* msg, size_t msg_size) {
    if (!buf || !msg || buf_size > msg_size) return 0;
    memcpy(msg, buf, buf_size);
    return buf_size;
}

static bool raw_validate(const void* buf, size_t size) {
    return buf != NULL && size > 0;
}

// Serializer instances
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
    .encode = raw_encode,
    .decode = raw_decode,
    .validate = raw_validate,
    .stats = {0}
};

serializer_t capnp_full_serializer = {
    .type = SERIAL_CAPNP_FULL,
    .name = "Cap'n Proto Full",
    .encode = raw_encode,
    .decode = raw_decode, 
    .validate = raw_validate,
    .stats = {0}
};

// Performance test function
int test_serialization_performance(const char* test_name, exo_cap cap, int iterations) {
    benchmark_message_t msg = {0};
    char buffer[256];
    benchmark_message_t decoded_msg;
    
    // Initialize test message
    for (int i = 0; i < 64; i++) {
        msg.payload[i] = (char)('A' + (i % 26));
    }
    
    double start_time = get_time_ns();
    
    // Perform serialization/deserialization loop
    for (int i = 0; i < iterations; i++) {
        msg.sequence = i;
        msg.timestamp = (uint64_t)get_time_ns();
        
        // Encode
        size_t encoded = exo_serialize(cap, &msg, sizeof(msg), buffer, sizeof(buffer));
        if (encoded == 0) return -1;
        
        // Decode
        size_t decoded = exo_deserialize(cap, buffer, encoded, &decoded_msg, sizeof(decoded_msg));
        if (decoded == 0) return -2;
        
        // Validate
        if (!exo_validate_message(cap, buffer, encoded)) return -3;
        
        // Verify integrity
        if (decoded_msg.sequence != msg.sequence) return -4;
    }
    
    double end_time = get_time_ns();
    double total_time = end_time - start_time;
    double avg_time_per_op = total_time / iterations;
    double ops_per_second = 1e9 / avg_time_per_op;
    
    // Simple output (avoiding printf conflicts)
    // We'll return success/failure and let caller handle output
    return 0;
}

int main(void) {
    const int iterations = 10000;
    
    // Test different capability trust levels
    exo_cap kernel_cap = { .rights = 0xE0000000 };  // High trust
    exo_cap libos_cap = { .rights = 0x80000000 };   // Medium trust 
    exo_cap user_cap = { .rights = 0x10000000 };    // Low trust
    
    // Run performance tests
    int result1 = test_serialization_performance("Kernel", kernel_cap, iterations);
    int result2 = test_serialization_performance("LibOS", libos_cap, iterations);
    int result3 = test_serialization_performance("User", user_cap, iterations);
    
    // Return 0 if all tests passed
    return (result1 == 0 && result2 == 0 && result3 == 0) ? 0 : -1;
}