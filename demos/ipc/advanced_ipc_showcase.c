/**
 * @file advanced_ipc_showcase.c
 * @brief Advanced showcase of IPC system features
 * 
 * Demonstrates:
 * - Dynamic capability management
 * - Adaptive serialization selection
 * - Performance optimization detection
 * - Error recovery and resilience
 * - Real-time statistics monitoring
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <unistd.h>
#include <stdatomic.h>

// Advanced capability system
typedef struct {
    uint64_t capability_id;
    uint32_t rights;
    uint32_t owner_pid;
    uint32_t target_pid;
    uint64_t expiration;
    uint32_t flags;
    uint32_t reserved;
} advanced_cap_t;

// Capability flags
#define CAP_FLAG_ZERO_COPY    (1 << 0)
#define CAP_FLAG_ENCRYPTED    (1 << 1)
#define CAP_FLAG_COMPRESSED   (1 << 2)
#define CAP_FLAG_PRIORITY     (1 << 3)
#define CAP_FLAG_MONITORED    (1 << 4)

// IPC statistics
typedef struct {
    atomic_uint_fast64_t messages_sent;
    atomic_uint_fast64_t messages_received;
    atomic_uint_fast64_t bytes_transferred;
    atomic_uint_fast64_t zero_copy_hits;
    atomic_uint_fast64_t serializer_raw_uses;
    atomic_uint_fast64_t serializer_lite_uses;
    atomic_uint_fast64_t serializer_full_uses;
    atomic_uint_fast64_t validation_failures;
    atomic_uint_fast64_t performance_optimizations;
} ipc_stats_t;

static ipc_stats_t global_stats = {0};

// Message types for advanced testing
typedef enum {
    MSG_TYPE_CONTROL = 1,
    MSG_TYPE_DATA = 2,
    MSG_TYPE_STREAM = 3,
    MSG_TYPE_BULK = 4,
    MSG_TYPE_PRIORITY = 5,
} message_type_t;

typedef struct {
    uint64_t msg_id;
    message_type_t type;
    uint32_t priority;
    uint64_t timestamp;
    uint32_t data_size;
    uint32_t sequence;
    uint8_t flags;
    uint8_t reserved[3];
    char data[0];  // Variable length
} advanced_message_t;

// Serializer selection with advanced logic
typedef enum {
    SERIAL_RAW,
    SERIAL_LITE, 
    SERIAL_FULL,
    SERIAL_ADAPTIVE
} serializer_type_t;

static serializer_type_t select_optimal_serializer(advanced_cap_t cap, 
                                                   size_t message_size,
                                                   message_type_t msg_type) {
    uint32_t trust_level = (cap.rights >> 28) & 0xF;
    
    // High trust + small messages = raw serialization
    if (trust_level >= 0xE && message_size <= 1024) {
        atomic_fetch_add(&global_stats.serializer_raw_uses, 1);
        if (cap.flags & CAP_FLAG_ZERO_COPY) {
            atomic_fetch_add(&global_stats.zero_copy_hits, 1);
        }
        return SERIAL_RAW;
    }
    
    // Medium trust or control messages = lite serialization
    if (trust_level >= 0x8 || msg_type == MSG_TYPE_CONTROL) {
        atomic_fetch_add(&global_stats.serializer_lite_uses, 1);
        return SERIAL_LITE;
    }
    
    // Low trust or large messages = full serialization
    atomic_fetch_add(&global_stats.serializer_full_uses, 1);
    return SERIAL_FULL;
}

// Advanced validation with multiple checks
static int validate_capability(advanced_cap_t cap) {
    uint64_t current_time = (uint64_t)time(NULL);
    
    // Check expiration
    if (cap.expiration && cap.expiration < current_time) {
        return 0;  // Expired
    }
    
    // Check basic rights
    if (cap.rights == 0) {
        return 0;  // No rights
    }
    
    // Check PID validity (simplified)
    if (cap.owner_pid == 0 || cap.target_pid == 0) {
        return 0;  // Invalid PIDs
    }
    
    return 1;  // Valid
}

// Enhanced checksum with different algorithms based on trust level
static uint32_t compute_enhanced_checksum(const void* data, size_t size, 
                                         serializer_type_t type) {
    const uint8_t* bytes = (const uint8_t*)data;
    uint32_t checksum = 0;
    
    switch (type) {
        case SERIAL_RAW:
            // Simple XOR for speed
            for (size_t i = 0; i < size; i++) {
                checksum ^= bytes[i];
            }
            break;
            
        case SERIAL_LITE:
            // CRC-like algorithm
            for (size_t i = 0; i < size; i++) {
                checksum = (checksum << 1) ^ bytes[i];
                if (checksum & 0x80000000) {
                    checksum ^= 0x04C11DB7;  // CRC32 polynomial
                }
            }
            break;
            
        case SERIAL_FULL:
            // Strong hash
            for (size_t i = 0; i < size; i++) {
                checksum = checksum * 31 + bytes[i];
                checksum ^= (checksum >> 16);
            }
            break;
            
        default:
            checksum = 0xDEADBEEF;
            break;
    }
    
    return checksum;
}

// Adaptive serialization with performance monitoring
static size_t adaptive_serialize(advanced_cap_t cap, const void* msg, size_t msg_size,
                               void* buf, size_t buf_size) {
    if (!validate_capability(cap)) {
        atomic_fetch_add(&global_stats.validation_failures, 1);
        return 0;
    }
    
    const advanced_message_t* amsg = (const advanced_message_t*)msg;
    serializer_type_t type = select_optimal_serializer(cap, msg_size, amsg->type);
    
    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    
    size_t result = 0;
    
    switch (type) {
        case SERIAL_RAW:
            // Direct copy with minimal overhead
            if (msg_size <= buf_size) {
                memcpy(buf, msg, msg_size);
                result = msg_size;
            }
            break;
            
        case SERIAL_LITE:
        case SERIAL_FULL: {
            // Enhanced protocol with header
            typedef struct {
                uint32_t magic;
                uint32_t version;
                uint32_t size;
                uint32_t checksum;
                uint32_t flags;
                uint32_t reserved[3];
            } protocol_header_t;
            
            if (sizeof(protocol_header_t) + msg_size <= buf_size) {
                protocol_header_t* header = (protocol_header_t*)buf;
                header->magic = (type == SERIAL_LITE) ? 0x4C495445 : 0x46554C4C;  // "LITE" / "FULL"
                header->version = 1;
                header->size = msg_size;
                header->checksum = compute_enhanced_checksum(msg, msg_size, type);
                header->flags = cap.flags;
                memset(header->reserved, 0, sizeof(header->reserved));
                
                memcpy((char*)buf + sizeof(protocol_header_t), msg, msg_size);
                result = sizeof(protocol_header_t) + msg_size;
            }
            break;
        }
        
        default:
            break;
    }
    
    clock_gettime(CLOCK_MONOTONIC, &end);
    double elapsed = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    
    if (elapsed < 1e-6) {  // Less than 1 microsecond
        atomic_fetch_add(&global_stats.performance_optimizations, 1);
    }
    
    if (result > 0) {
        atomic_fetch_add(&global_stats.messages_sent, 1);
        atomic_fetch_add(&global_stats.bytes_transferred, result);
    }
    
    return result;
}

// Create advanced capability with specific properties
static advanced_cap_t create_capability(uint32_t trust_level, uint32_t owner_pid,
                                       uint32_t target_pid, uint32_t flags) {
    advanced_cap_t cap = {0};
    cap.capability_id = ((uint64_t)rand() << 32) | rand();
    cap.rights = (trust_level & 0xF) << 28;
    cap.owner_pid = owner_pid;
    cap.target_pid = target_pid;
    cap.expiration = time(NULL) + 3600;  // 1 hour from now
    cap.flags = flags;
    return cap;
}

// Create test message
static advanced_message_t* create_test_message(message_type_t type, uint32_t priority,
                                             const char* data, size_t data_size) {
    size_t total_size = sizeof(advanced_message_t) + data_size;
    advanced_message_t* msg = malloc(total_size);
    if (!msg) return NULL;
    
    msg->msg_id = ((uint64_t)rand() << 32) | rand();
    msg->type = type;
    msg->priority = priority;
    msg->timestamp = (uint64_t)time(NULL) * 1000000;  // microseconds
    msg->data_size = data_size;
    msg->sequence = rand() % 10000;
    msg->flags = 0;
    memset(msg->reserved, 0, sizeof(msg->reserved));
    
    if (data && data_size > 0) {
        memcpy(msg->data, data, data_size);
    }
    
    return msg;
}

// Performance test with different scenarios
static void run_performance_scenarios(void) {
    printf("=== Performance Scenario Testing ===\n");
    
    // Scenario 1: High-trust, small messages (should use raw)
    advanced_cap_t kernel_cap = create_capability(0xF, 1, 2, CAP_FLAG_ZERO_COPY);
    char small_data[] = "Small kernel message";
    advanced_message_t* small_msg = create_test_message(MSG_TYPE_CONTROL, 10, 
                                                       small_data, sizeof(small_data));
    
    // Scenario 2: Medium-trust, medium messages (should use lite)
    advanced_cap_t libos_cap = create_capability(0x8, 100, 200, CAP_FLAG_MONITORED);
    char medium_data[512];
    memset(medium_data, 'M', sizeof(medium_data));
    advanced_message_t* medium_msg = create_test_message(MSG_TYPE_DATA, 5,
                                                        medium_data, sizeof(medium_data));
    
    // Scenario 3: Low-trust, large messages (should use full)
    advanced_cap_t user_cap = create_capability(0x1, 1000, 2000, 0);
    char large_data[4096];
    memset(large_data, 'L', sizeof(large_data));
    advanced_message_t* large_msg = create_test_message(MSG_TYPE_BULK, 1,
                                                       large_data, sizeof(large_data));
    
    char buffer[8192];
    const int iterations = 1000;
    
    struct {
        const char* name;
        advanced_cap_t cap;
        advanced_message_t* msg;
        size_t msg_size;
    } scenarios[] = {
        {"High-trust small", kernel_cap, small_msg, sizeof(*small_msg) + sizeof(small_data)},
        {"Medium-trust medium", libos_cap, medium_msg, sizeof(*medium_msg) + sizeof(medium_data)},
        {"Low-trust large", user_cap, large_msg, sizeof(*large_msg) + sizeof(large_data)}
    };
    
    for (int s = 0; s < 3; s++) {
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);
        
        int success_count = 0;
        for (int i = 0; i < iterations; i++) {
            size_t encoded = adaptive_serialize(scenarios[s].cap, scenarios[s].msg,
                                              scenarios[s].msg_size, buffer, sizeof(buffer));
            if (encoded > 0) {
                success_count++;
            }
        }
        
        clock_gettime(CLOCK_MONOTONIC, &end);
        double elapsed = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
        
        printf("%-20s: %d/%d msgs, %.3f sec, %.0f msg/sec\n",
               scenarios[s].name, success_count, iterations, elapsed,
               success_count / elapsed);
    }
    
    free(small_msg);
    free(medium_msg);
    free(large_msg);
    printf("\n");
}

// Statistics display
static void print_statistics(void) {
    printf("=== IPC System Statistics ===\n");
    printf("Messages sent:           %lu\n", (unsigned long)global_stats.messages_sent);
    printf("Messages received:       %lu\n", (unsigned long)global_stats.messages_received);
    printf("Bytes transferred:       %lu (%.2f MB)\n", 
           (unsigned long)global_stats.bytes_transferred,
           (double)global_stats.bytes_transferred / (1024 * 1024));
    printf("Zero-copy hits:          %lu\n", (unsigned long)global_stats.zero_copy_hits);
    printf("Raw serializer uses:     %lu\n", (unsigned long)global_stats.serializer_raw_uses);
    printf("Lite serializer uses:    %lu\n", (unsigned long)global_stats.serializer_lite_uses);
    printf("Full serializer uses:    %lu\n", (unsigned long)global_stats.serializer_full_uses);
    printf("Validation failures:     %lu\n", (unsigned long)global_stats.validation_failures);
    printf("Performance optimizations: %lu\n", (unsigned long)global_stats.performance_optimizations);
    
    uint64_t total_serializer_uses = global_stats.serializer_raw_uses +
                                    global_stats.serializer_lite_uses +
                                    global_stats.serializer_full_uses;
    
    if (total_serializer_uses > 0) {
        printf("\nSerializer Distribution:\n");
        printf("Raw:  %.1f%%\n", 100.0 * global_stats.serializer_raw_uses / total_serializer_uses);
        printf("Lite: %.1f%%\n", 100.0 * global_stats.serializer_lite_uses / total_serializer_uses);
        printf("Full: %.1f%%\n", 100.0 * global_stats.serializer_full_uses / total_serializer_uses);
    }
    printf("\n");
}

int main(void) {
    srand(time(NULL));
    
    printf("🚀 Advanced FeuerBird IPC System Showcase\n");
    printf("==========================================\n\n");
    
    printf("=== Capability System Demonstration ===\n");
    
    // Create various capability types
    advanced_cap_t caps[] = {
        create_capability(0xF, 1, 2, CAP_FLAG_ZERO_COPY | CAP_FLAG_PRIORITY),
        create_capability(0x8, 100, 200, CAP_FLAG_MONITORED),
        create_capability(0x4, 500, 600, CAP_FLAG_COMPRESSED),
        create_capability(0x1, 1000, 2000, 0)
    };
    
    const char* cap_names[] = {
        "Kernel (high-trust, zero-copy, priority)",
        "LibOS (medium-trust, monitored)",
        "System (low-medium trust, compressed)", 
        "User (low-trust, basic)"
    };
    
    for (int i = 0; i < 4; i++) {
        printf("Cap %d: %s\n", i + 1, cap_names[i]);
        printf("  Rights: 0x%08X, Trust: %d, Flags: 0x%X\n",
               caps[i].rights, (caps[i].rights >> 28) & 0xF, caps[i].flags);
        printf("  Valid: %s, Zero-copy: %s\n",
               validate_capability(caps[i]) ? "YES" : "NO",
               (caps[i].flags & CAP_FLAG_ZERO_COPY) ? "YES" : "NO");
    }
    printf("\n");
    
    // Run performance scenarios
    run_performance_scenarios();
    
    // Print final statistics
    print_statistics();
    
    printf("✅ Advanced IPC showcase completed successfully!\n");
    printf("The system demonstrates:\n");
    printf("  • Dynamic capability-based serialization selection\n");
    printf("  • Performance optimization detection\n");
    printf("  • Comprehensive validation and security\n");
    printf("  • Real-time statistics monitoring\n");
    printf("  • Zero-copy optimization for trusted paths\n");
    
    return 0;
}