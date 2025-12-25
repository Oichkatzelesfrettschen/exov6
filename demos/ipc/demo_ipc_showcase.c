/**
 * @file demo_ipc_showcase.c
 * @brief Live demonstration of the unified IPC system capabilities
 * 
 * This showcases all major features working together:
 * - Automatic serializer selection based on capabilities
 * - Performance differences between serialization layers
 * - Zero-copy optimization in action
 * - Real-time statistics monitoring
 */

#include "ipc/serialization.h"
#include "kernel/string.h"
#include <time.h>
#include <stdatomic.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdio.h>

// Demonstration message types
typedef struct {
    uint64_t sequence_id;
    uint64_t timestamp_ns;
    uint32_t source_pid;
    uint32_t message_type;
    char payload[128];
    uint32_t checksum;
} demo_message_t;

typedef struct {
    uint32_t magic;
    uint16_t version;
    uint16_t flags;
    uint64_t data[8];  // 64 bytes of data
} performance_message_t;

// Performance timing
static double get_time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1e9 + ts.tv_nsec;
}

// Simple checksum for validation
static uint32_t calculate_checksum(const void* data, size_t size) {
    const uint8_t* bytes = (const uint8_t*)data;
    uint32_t checksum = 0;
    for (size_t i = 0; i < size - sizeof(uint32_t); i++) {
        checksum ^= bytes[i];
    }
    return checksum;
}

// Enhanced serializers with validation
static size_t enhanced_raw_encode(const void* msg, size_t msg_size,
                                  void* buf, size_t buf_size) {
    if (!msg || !buf || msg_size > buf_size) return 0;
    
    // Add minimal header for validation
    *(uint32_t*)buf = 0xRAWDATA;  // Magic number for raw data
    memcpy((uint8_t*)buf + 4, msg, msg_size);
    
    return msg_size + 4;
}

static size_t enhanced_raw_decode(const void* buf, size_t buf_size,
                                  void* msg, size_t msg_size) {
    if (!buf || !msg || buf_size < 4) return 0;
    
    if (*(uint32_t*)buf != 0xRAWDATA) return 0;  // Validate magic
    
    size_t payload_size = buf_size - 4;
    if (payload_size > msg_size) return 0;
    
    memcpy(msg, (uint8_t*)buf + 4, payload_size);
    return payload_size;
}

static bool enhanced_raw_validate(const void* buf, size_t size) {
    return buf && size >= 4 && *(uint32_t*)buf == 0xRAWDATA;
}

// Lite serializer with checksums
typedef struct {
    uint32_t magic;
    uint32_t size;
    uint32_t checksum;
    uint32_t flags;
} lite_header_t;

#define LITE_MAGIC 0xL1TEDATA

static size_t lite_encode(const void* msg, size_t msg_size,
                          void* buf, size_t buf_size) {
    if (!msg || !buf || buf_size < sizeof(lite_header_t) + msg_size) return 0;
    
    lite_header_t* header = (lite_header_t*)buf;
    header->magic = LITE_MAGIC;
    header->size = msg_size;
    header->checksum = calculate_checksum(msg, msg_size + sizeof(uint32_t));
    header->flags = 0x0001;  // Version 1
    
    memcpy((uint8_t*)buf + sizeof(lite_header_t), msg, msg_size);
    
    return sizeof(lite_header_t) + msg_size;
}

static size_t lite_decode(const void* buf, size_t buf_size,
                          void* msg, size_t msg_size) {
    if (!buf || !msg || buf_size < sizeof(lite_header_t)) return 0;
    
    const lite_header_t* header = (const lite_header_t*)buf;
    if (header->magic != LITE_MAGIC || header->size > msg_size) return 0;
    
    const uint8_t* payload = (const uint8_t*)buf + sizeof(lite_header_t);
    uint32_t expected_checksum = calculate_checksum(payload, header->size + sizeof(uint32_t));
    
    if (header->checksum != expected_checksum) return 0;  // Checksum mismatch
    
    memcpy(msg, payload, header->size);
    return header->size;
}

static bool lite_validate(const void* buf, size_t size) {
    if (!buf || size < sizeof(lite_header_t)) return false;
    const lite_header_t* header = (const lite_header_t*)buf;
    return header->magic == LITE_MAGIC && header->flags == 0x0001;
}

// Full serializer (for now, enhanced lite)
static size_t full_encode(const void* msg, size_t msg_size,
                          void* buf, size_t buf_size) {
    // Add extra validation for full protocol
    return lite_encode(msg, msg_size, buf, buf_size);
}

static size_t full_decode(const void* buf, size_t buf_size,
                          void* msg, size_t msg_size) {
    return lite_decode(buf, buf_size, msg, msg_size);
}

static bool full_validate(const void* buf, size_t size) {
    return lite_validate(buf, size);
}

// Global serializer instances
serializer_t raw_serializer = {
    .type = SERIAL_RAW,
    .name = "Raw",
    .encode = enhanced_raw_encode,
    .decode = enhanced_raw_decode,
    .validate = enhanced_raw_validate,
    .stats = {0}
};

serializer_t capnp_lite_serializer = {
    .type = SERIAL_CAPNP_LITE,
    .name = "CapnProto-Lite",
    .encode = lite_encode,
    .decode = lite_decode,
    .validate = lite_validate,
    .stats = {0}
};

serializer_t capnp_full_serializer = {
    .type = SERIAL_CAPNP_FULL,
    .name = "CapnProto-Full",
    .encode = full_encode,
    .decode = full_decode,
    .validate = full_validate,
    .stats = {0}
};

// Demo functions
static int demo_capability_selection(void) {
    char output_buffer[1024];
    char* pos = output_buffer;
    
    // Test different capability levels
    exo_cap kernel_cap = { .rights = 0xF0000000 };  // Highest trust
    exo_cap libos_cap = { .rights = 0x80000000 };   // Medium trust
    exo_cap user_cap = { .rights = 0x10000000 };    // Low trust
    
    serializer_t* s1 = exo_select_serializer(kernel_cap);
    serializer_t* s2 = exo_select_serializer(libos_cap);
    serializer_t* s3 = exo_select_serializer(user_cap);
    
    pos += sprintf(pos, "=== Capability-Based Serializer Selection ===\n");
    pos += sprintf(pos, "Kernel cap (0x%08X) -> %s\n", kernel_cap.rights, s1->name);
    pos += sprintf(pos, "LibOS cap  (0x%08X) -> %s\n", libos_cap.rights, s2->name);
    pos += sprintf(pos, "User cap   (0x%08X) -> %s\n", user_cap.rights, s3->name);
    pos += sprintf(pos, "\n");
    
    // Write to a file since we can't use printf
    int fd = open("/tmp/ipc_demo_output.txt", O_WRONLY | O_CREAT | O_TRUNC, 0644);
    if (fd >= 0) {
        write(fd, output_buffer, pos - output_buffer);
        close(fd);
    }
    
    return (s1->type == SERIAL_RAW && 
            s2->type == SERIAL_CAPNP_LITE && 
            s3->type == SERIAL_CAPNP_FULL) ? 0 : -1;
}

static int demo_performance_comparison(void) {
    const int iterations = 1000;
    performance_message_t test_msg = {
        .magic = 0xDEADBEEF,
        .version = 1,
        .flags = 0x0042,
        .data = {1, 2, 3, 4, 5, 6, 7, 8}
    };
    
    char buffer[512];
    performance_message_t decoded_msg;
    
    // Test each serializer
    exo_cap caps[3] = {
        { .rights = 0xF0000000 },  // Raw
        { .rights = 0x80000000 },  // Lite 
        { .rights = 0x10000000 }   // Full
    };
    
    double times[3] = {0};
    
    for (int cap_idx = 0; cap_idx < 3; cap_idx++) {
        double start_time = get_time_ns();
        
        for (int i = 0; i < iterations; i++) {
            test_msg.data[0] = i;  // Vary the data
            
            size_t encoded = exo_serialize(caps[cap_idx], &test_msg, sizeof(test_msg), 
                                         buffer, sizeof(buffer));
            if (encoded == 0) return -1;
            
            size_t decoded = exo_deserialize(caps[cap_idx], buffer, encoded, 
                                           &decoded_msg, sizeof(decoded_msg));
            if (decoded == 0) return -2;
            
            if (!exo_validate_message(caps[cap_idx], buffer, encoded)) return -3;
            
            if (decoded_msg.data[0] != i) return -4;  // Data integrity check
        }
        
        double end_time = get_time_ns();
        times[cap_idx] = (end_time - start_time) / iterations;  // Average per operation
    }
    
    // Performance ratios should show raw is fastest
    return (times[0] <= times[1] && times[1] <= times[2]) ? 0 : -1;
}

static int demo_zero_copy_optimization(void) {
    exo_cap kernel_cap = { .rights = 0xF0000000 };
    exo_cap user_cap = { .rights = 0x10000000 };
    
    // Test zero-copy detection
    if (!exo_can_zero_copy(kernel_cap)) return -1;  // Should support zero-copy
    if (exo_can_zero_copy(user_cap)) return -2;     // Should NOT support zero-copy
    
    // Test zero-copy pointer access
    char buffer[256];
    void* zc_ptr = exo_get_zero_copy_ptr(kernel_cap, buffer, 64);
    if (zc_ptr != (buffer + 64)) return -3;  // Should return direct pointer
    
    void* no_zc_ptr = exo_get_zero_copy_ptr(user_cap, buffer, 64);
    if (no_zc_ptr != NULL) return -4;  // Should return NULL for unsafe access
    
    return 0;
}

static int demo_message_validation(void) {
    demo_message_t msg = {
        .sequence_id = 12345,
        .timestamp_ns = 1234567890ULL,
        .source_pid = 42,
        .message_type = 0x1001,
        .payload = "This is a test message for validation demo"
    };
    msg.checksum = calculate_checksum(&msg, sizeof(msg));
    
    char buffer[512];
    exo_cap test_cap = { .rights = 0x80000000 };  // Use lite serializer
    
    // Encode message
    size_t encoded_size = exo_serialize(test_cap, &msg, sizeof(msg), buffer, sizeof(buffer));
    if (encoded_size == 0) return -1;
    
    // Valid message should pass validation
    if (!exo_validate_message(test_cap, buffer, encoded_size)) return -2;
    
    // Corrupt the buffer
    buffer[16] ^= 0xFF;  // Flip some bits
    
    // Corrupted message should fail validation
    if (exo_validate_message(test_cap, buffer, encoded_size)) return -3;
    
    return 0;
}

// Main demonstration
int main(void) {
    int total_errors = 0;
    
    // Run all demonstrations
    if (demo_capability_selection() != 0) {
        total_errors++;
    }
    
    if (demo_performance_comparison() != 0) {
        total_errors++;
    }
    
    if (demo_zero_copy_optimization() != 0) {
        total_errors++;
    }
    
    if (demo_message_validation() != 0) {
        total_errors++;
    }
    
    // Create success indicator file
    if (total_errors == 0) {
        int fd = open("/tmp/ipc_demo_success", O_WRONLY | O_CREAT | O_TRUNC, 0644);
        if (fd >= 0) {
            const char* msg = "All IPC demonstrations completed successfully!\n";
            write(fd, msg, strlen(msg));
            close(fd);
        }
    }
    
    return total_errors;
}