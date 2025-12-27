/**
 * @file test_simple_ipc.c
 * @brief Simple test of core IPC serialization functionality
 */

#include "include/ipc/serialization.h"
#include "kernel/string.h"
#include <stdatomic.h>

// Simple test data structure
typedef struct {
    uint32_t id;
    uint32_t value;
    char name[16];
} test_message_t;

// Portable cycle counter (stub)
static inline uint64_t get_cycles(void) {
    return 0; // Simplified for testing
}

// =============================================================================
// MINIMAL RAW SERIALIZER
// =============================================================================

static size_t raw_encode(const void* msg, size_t msg_size,
                         void* buf, size_t buf_size) {
    if (!msg || !buf || msg_size > buf_size) {
        return 0;
    }
    memcpy(buf, msg, msg_size);
    return msg_size;
}

static size_t raw_decode(const void* buf, size_t buf_size,
                         void* msg, size_t msg_size) {
    if (!buf || !msg || buf_size > msg_size) {
        return 0;
    }
    memcpy(msg, buf, buf_size);
    return buf_size;
}

static bool raw_validate(const void* buf, size_t size) {
    return buf != NULL && size > 0;
}

// Global serializer instance
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
    .encode = raw_encode,  // Simplified
    .decode = raw_decode,  // Simplified
    .validate = raw_validate,
    .stats = {0}
};

serializer_t capnp_full_serializer = {
    .type = SERIAL_CAPNP_FULL,
    .name = "Cap'n Proto Full",
    .encode = raw_encode,  // Simplified
    .decode = raw_decode,  // Simplified
    .validate = raw_validate,
    .stats = {0}
};

// =============================================================================
// TEST FUNCTIONS
// =============================================================================

int test_basic_serialization(void) {
    test_message_t msg = {
        .id = 0x12345678,
        .value = 0xDEADBEEF,
        .name = "test_msg"
    };
    
    char buffer[128];
    test_message_t decoded_msg = {0};
    
    // Test raw serialization
    exo_cap test_cap = {
        .pa = 0,
        .id = 1,
        .rights = 0xE0000000,  // High trust level
        .owner = 0
    };
    
    size_t encoded_size = exo_serialize(test_cap, &msg, sizeof(msg), buffer, sizeof(buffer));
    if (encoded_size != sizeof(msg)) {
        return -1;  // Encode failed
    }
    
    size_t decoded_size = exo_deserialize(test_cap, buffer, encoded_size, &decoded_msg, sizeof(decoded_msg));
    if (decoded_size != sizeof(msg)) {
        return -2;  // Decode failed
    }
    
    // Verify data integrity
    if (decoded_msg.id != msg.id || decoded_msg.value != msg.value) {
        return -3;  // Data corrupted
    }
    
    // Test message validation
    if (!exo_validate_message(test_cap, buffer, encoded_size)) {
        return -4;  // Validation failed
    }
    
    return 0;  // Success
}

// =============================================================================
// MAIN TEST
// =============================================================================

int main(void) {
    // Test basic functionality
    int result = test_basic_serialization();
    
    // Return result (0 = success, negative = error)
    return result;
}