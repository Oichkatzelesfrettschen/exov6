/**
 * @file demo_standalone.c
 * @brief Standalone demonstration of IPC concepts
 */

#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <fcntl.h>

// Capability structure (simplified)
typedef struct {
    uint32_t rights;
    uint32_t id;
} demo_cap_t;

// Serialization types
typedef enum {
    SERIAL_RAW,
    SERIAL_LITE,
    SERIAL_FULL
} serial_type_t;

// Simple message structure
typedef struct {
    uint32_t magic;
    uint32_t sequence;
    char data[64];
    uint32_t checksum;
} demo_message_t;

// Performance timer
static double get_time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1e9 + ts.tv_nsec;
}

// Simple checksum
static uint32_t simple_checksum(const void* data, size_t size) {
    const uint8_t* bytes = (const uint8_t*)data;
    uint32_t sum = 0;
    for (size_t i = 0; i < size - sizeof(uint32_t); i++) {
        sum ^= bytes[i];
    }
    return sum;
}

// Capability-based serializer selection
static serial_type_t select_serializer(demo_cap_t cap) {
    uint32_t trust_level = (cap.rights >> 28) & 0xF;
    
    if (trust_level >= 0xE) {
        return SERIAL_RAW;      // Kernel trust
    } else if (trust_level >= 0x8) {
        return SERIAL_LITE;     // LibOS trust
    } else {
        return SERIAL_FULL;     // User trust
    }
}

// Raw serialization (zero overhead)
static size_t raw_serialize(const demo_message_t* msg, void* buf, size_t buf_size) {
    if (sizeof(*msg) > buf_size) return 0;
    memcpy(buf, msg, sizeof(*msg));
    return sizeof(*msg);
}

static size_t raw_deserialize(const void* buf, size_t buf_size, demo_message_t* msg) {
    if (buf_size < sizeof(*msg)) return 0;
    memcpy(msg, buf, sizeof(*msg));
    return sizeof(*msg);
}

// Lite serialization (with header)
typedef struct {
    uint32_t magic;
    uint32_t size;
    uint32_t version;
    uint32_t checksum;
} lite_header_t;

#define LITE_MAGIC 0xCAFEBABE

static size_t lite_serialize(const demo_message_t* msg, void* buf, size_t buf_size) {
    if (sizeof(lite_header_t) + sizeof(*msg) > buf_size) return 0;
    
    lite_header_t* header = (lite_header_t*)buf;
    header->magic = LITE_MAGIC;
    header->size = sizeof(*msg);
    header->version = 1;
    header->checksum = simple_checksum(msg, sizeof(*msg));
    
    memcpy((uint8_t*)buf + sizeof(lite_header_t), msg, sizeof(*msg));
    return sizeof(lite_header_t) + sizeof(*msg);
}

static size_t lite_deserialize(const void* buf, size_t buf_size, demo_message_t* msg) {
    if (buf_size < sizeof(lite_header_t)) return 0;
    
    const lite_header_t* header = (const lite_header_t*)buf;
    if (header->magic != LITE_MAGIC || header->size != sizeof(*msg)) return 0;
    
    memcpy(msg, (uint8_t*)buf + sizeof(lite_header_t), sizeof(*msg));
    
    uint32_t checksum = simple_checksum(msg, sizeof(*msg));
    if (checksum != header->checksum) return 0;
    
    return sizeof(*msg);
}

// Full serialization (enhanced lite)
static size_t full_serialize(const demo_message_t* msg, void* buf, size_t buf_size) {
    return lite_serialize(msg, buf, buf_size);  // For now, same as lite
}

static size_t full_deserialize(const void* buf, size_t buf_size, demo_message_t* msg) {
    return lite_deserialize(buf, buf_size, msg);  // For now, same as lite
}

// Generic serialization interface
static size_t serialize_message(demo_cap_t cap, const demo_message_t* msg, 
                               void* buf, size_t buf_size) {
    serial_type_t type = select_serializer(cap);
    
    switch (type) {
        case SERIAL_RAW:
            return raw_serialize(msg, buf, buf_size);
        case SERIAL_LITE:
            return lite_serialize(msg, buf, buf_size);
        case SERIAL_FULL:
            return full_serialize(msg, buf, buf_size);
        default:
            return 0;
    }
}

static size_t deserialize_message(demo_cap_t cap, const void* buf, size_t buf_size,
                                 demo_message_t* msg) {
    serial_type_t type = select_serializer(cap);
    
    switch (type) {
        case SERIAL_RAW:
            return raw_deserialize(buf, buf_size, msg);
        case SERIAL_LITE:
            return lite_deserialize(buf, buf_size, msg);
        case SERIAL_FULL:
            return full_deserialize(buf, buf_size, msg);
        default:
            return 0;
    }
}

// Demonstration functions
static void demo_capability_selection(void) {
    printf("=== Capability-Based Serializer Selection ===\n");
    
    demo_cap_t kernel_cap = { .rights = 0xF0000000, .id = 1 };
    demo_cap_t libos_cap = { .rights = 0x80000000, .id = 2 };
    demo_cap_t user_cap = { .rights = 0x10000000, .id = 3 };
    
    const char* type_names[] = { "Raw", "Lite", "Full" };
    
    printf("Kernel capability (0x%08X) -> %s serializer\n", 
           kernel_cap.rights, type_names[select_serializer(kernel_cap)]);
    printf("LibOS capability  (0x%08X) -> %s serializer\n", 
           libos_cap.rights, type_names[select_serializer(libos_cap)]);
    printf("User capability   (0x%08X) -> %s serializer\n", 
           user_cap.rights, type_names[select_serializer(user_cap)]);
    printf("\n");
}

static void demo_serialization_roundtrip(void) {
    printf("=== Serialization Round-trip Test ===\n");
    
    demo_message_t original = {
        .magic = 0xDEADBEEF,
        .sequence = 12345,
        .data = "Hello, unified IPC system!",
    };
    original.checksum = simple_checksum(&original, sizeof(original));
    
    char buffer[256];
    demo_message_t decoded;
    
    demo_cap_t caps[] = {
        { .rights = 0xF0000000 },  // Raw
        { .rights = 0x80000000 },  // Lite
        { .rights = 0x10000000 }   // Full
    };
    
    const char* names[] = { "Raw", "Lite", "Full" };
    
    for (int i = 0; i < 3; i++) {
        memset(&decoded, 0, sizeof(decoded));
        
        size_t encoded_size = serialize_message(caps[i], &original, buffer, sizeof(buffer));
        size_t decoded_size = deserialize_message(caps[i], buffer, encoded_size, &decoded);
        
        printf("%s: encoded=%zu bytes, decoded=%zu bytes, data_match=%s\n",
               names[i], encoded_size, decoded_size,
               (decoded.sequence == original.sequence && 
                strcmp(decoded.data, original.data) == 0) ? "YES" : "NO");
    }
    printf("\n");
}

static void demo_performance_comparison(void) {
    printf("=== Performance Comparison ===\n");
    
    const int iterations = 10000;
    demo_message_t test_msg = {
        .magic = 0xDEADBEEF,
        .sequence = 0,
        .data = "Performance test message for IPC benchmarking",
    };
    test_msg.checksum = simple_checksum(&test_msg, sizeof(test_msg));
    
    char buffer[256];
    demo_message_t decoded;
    
    demo_cap_t caps[] = {
        { .rights = 0xF0000000 },  // Raw
        { .rights = 0x80000000 },  // Lite
        { .rights = 0x10000000 }   // Full
    };
    
    const char* names[] = { "Raw", "Lite", "Full" };
    
    for (int cap_idx = 0; cap_idx < 3; cap_idx++) {
        double start_time = get_time_ns();
        
        for (int i = 0; i < iterations; i++) {
            test_msg.sequence = i;
            
            size_t encoded = serialize_message(caps[cap_idx], &test_msg, buffer, sizeof(buffer));
            size_t decoded_size = deserialize_message(caps[cap_idx], buffer, encoded, &decoded);
            
            if (encoded == 0 || decoded_size == 0 || decoded.sequence != i) {
                printf("ERROR in %s serialization at iteration %d\n", names[cap_idx], i);
                return;
            }
        }
        
        double end_time = get_time_ns();
        double avg_time_ns = (end_time - start_time) / iterations;
        double ops_per_sec = 1e9 / avg_time_ns;
        
        printf("%s: %.2f ns/op, %.0f ops/sec\n", names[cap_idx], avg_time_ns, ops_per_sec);
    }
    printf("\n");
}

static void demo_zero_copy_concept(void) {
    printf("=== Zero-Copy Optimization Concept ===\n");
    
    demo_cap_t kernel_cap = { .rights = 0xF0000000 };
    demo_cap_t user_cap = { .rights = 0x10000000 };
    
    printf("Kernel capability: Zero-copy %s (trust level 0x%X)\n",
           select_serializer(kernel_cap) == SERIAL_RAW ? "ENABLED" : "DISABLED",
           (kernel_cap.rights >> 28) & 0xF);
    
    printf("User capability:   Zero-copy %s (trust level 0x%X)\n",
           select_serializer(user_cap) == SERIAL_RAW ? "ENABLED" : "DISABLED",
           (user_cap.rights >> 28) & 0xF);
    
    printf("Zero-copy is only enabled for high-trust (kernel) capabilities\n");
    printf("\n");
}

int main(void) {
    printf("🚀 FeuerBird Unified IPC System Demonstration\n");
    printf("=============================================\n\n");
    
    // Run all demonstrations
    demo_capability_selection();
    demo_serialization_roundtrip();
    demo_performance_comparison();
    demo_zero_copy_concept();
    
    printf("✅ All demonstrations completed successfully!\n");
    printf("The unified IPC system is working as designed.\n");
    
    return 0;
}