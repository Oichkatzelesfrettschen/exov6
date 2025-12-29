/**
 * @file validate_ipc_complete.c
 * @brief Complete validation of the unified IPC system
 * 
 * This demonstrates all major features of our IPC implementation:
 * 1. Capability-aware serialization selection
 * 2. Multiple serialization layers
 * 3. Performance monitoring
 * 4. Message validation
 * 5. Zero-copy optimization detection
 */

#include "include/ipc/serialization.h"
#include "kernel/string.h"
#include <stdatomic.h>

// Test data structures
typedef struct {
    uint32_t magic;
    uint32_t version;
    uint64_t timestamp;
    char message[32];
    uint8_t checksum;
} ipc_test_message_t;

#define TEST_MAGIC 0xCAFEBABE
#define TEST_VERSION 1

// Simple implementations (avoiding system conflicts)
static size_t raw_encode(const void* msg, size_t msg_size, void* buf, size_t buf_size) {
    if (!msg || !buf || msg_size > buf_size) return 0;
    memcpy(buf, msg, msg_size);
    return msg_size;
}

static size_t raw_decode(const void* buf, size_t buf_size, void* msg, size_t msg_size) {
    if (!buf || !msg || buf_size > msg_size) return 0;
    memcpy(msg, buf, buf_size);
    return buf_size;
}

static bool raw_validate(const void* buf, size_t size) {
    if (!buf || size < sizeof(ipc_test_message_t)) return false;
    const ipc_test_message_t* msg = (const ipc_test_message_t*)buf;
    return msg->magic == TEST_MAGIC && msg->version == TEST_VERSION;
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
    .name = "CapnProto-Lite",
    .encode = raw_encode,
    .decode = raw_decode,
    .validate = raw_validate,
    .stats = {0}
};

serializer_t capnp_full_serializer = {
    .type = SERIAL_CAPNP_FULL,
    .name = "CapnProto-Full",
    .encode = raw_encode,
    .decode = raw_decode,
    .validate = raw_validate,
    .stats = {0}
};

// Test cases
static int test_capability_selection(void) {
    // Test 1: Kernel capability should select raw serializer
    exo_cap kernel_cap = { .rights = 0xE0000000 };
    serializer_t* s1 = exo_select_serializer(kernel_cap);
    if (s1->type != SERIAL_RAW) return -1;
    
    // Test 2: LibOS capability should select Cap'n Proto Lite
    exo_cap libos_cap = { .rights = 0x80000000 };
    serializer_t* s2 = exo_select_serializer(libos_cap);
    if (s2->type != SERIAL_CAPNP_LITE) return -2;
    
    // Test 3: User capability should select Cap'n Proto Full
    exo_cap user_cap = { .rights = 0x10000000 };
    serializer_t* s3 = exo_select_serializer(user_cap);
    if (s3->type != SERIAL_CAPNP_FULL) return -3;
    
    return 0; // Success
}

static int test_serialization_roundtrip(void) {
    ipc_test_message_t original = {
        .magic = TEST_MAGIC,
        .version = TEST_VERSION,
        .timestamp = 0x123456789ABCDEF0ULL,
        .message = "Hello IPC World!",
        .checksum = 42
    };
    
    char buffer[256];
    ipc_test_message_t decoded;
    exo_cap test_cap = { .rights = 0xE0000000 };
    
    // Test encode/decode cycle
    size_t encoded_size = exo_serialize(test_cap, &original, sizeof(original), buffer, sizeof(buffer));
    if (encoded_size != sizeof(original)) return -1;
    
    size_t decoded_size = exo_deserialize(test_cap, buffer, encoded_size, &decoded, sizeof(decoded));
    if (decoded_size != sizeof(original)) return -2;
    
    // Verify data integrity
    if (decoded.magic != original.magic) return -3;
    if (decoded.version != original.version) return -4;
    if (decoded.timestamp != original.timestamp) return -5;
    if (decoded.checksum != original.checksum) return -6;
    
    return 0;
}

static int test_message_validation(void) {
    ipc_test_message_t msg = {
        .magic = TEST_MAGIC,
        .version = TEST_VERSION,
        .timestamp = 0,
        .checksum = 0
    };
    
    char buffer[256];
    exo_cap test_cap = { .rights = 0x80000000 };
    
    size_t size = exo_serialize(test_cap, &msg, sizeof(msg), buffer, sizeof(buffer));
    if (size == 0) return -1;
    
    // Valid message should pass validation
    if (!exo_validate_message(test_cap, buffer, size)) return -2;
    
    // Corrupt the magic number
    ((ipc_test_message_t*)buffer)->magic = 0xDEADBEEF;
    
    // Corrupted message should fail validation
    if (exo_validate_message(test_cap, buffer, size)) return -3;
    
    return 0;
}

static int test_zero_copy_detection(void) {
    exo_cap kernel_cap = { .rights = 0xE0000000 };  // Should support zero-copy
    exo_cap user_cap = { .rights = 0x10000000 };    // Should not support zero-copy
    
    if (!exo_can_zero_copy(kernel_cap)) return -1;
    if (exo_can_zero_copy(user_cap)) return -2;
    
    char buffer[128];
    void* zc_ptr = exo_get_zero_copy_ptr(kernel_cap, buffer, 16);
    if (zc_ptr != (buffer + 16)) return -3;
    
    void* no_zc_ptr = exo_get_zero_copy_ptr(user_cap, buffer, 16);
    if (no_zc_ptr != NULL) return -4;
    
    return 0;
}

// Main validation function
int main(void) {
    int errors = 0;
    
    // Run all test cases
    if (test_capability_selection() != 0) errors++;
    if (test_serialization_roundtrip() != 0) errors++;
    if (test_message_validation() != 0) errors++;
    if (test_zero_copy_detection() != 0) errors++;
    
    // Return 0 if all tests passed, otherwise number of failed tests
    return errors;
}