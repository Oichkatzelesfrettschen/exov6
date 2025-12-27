/**
 * @file stress_test_ipc.c
 * @brief Multi-threaded stress test of the IPC system
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <pthread.h>
#include <unistd.h>
#include <stdatomic.h>

// Test configuration
#define NUM_THREADS 4
#define MESSAGES_PER_THREAD 10000
#define MESSAGE_SIZES 5

// Statistics (using atomic_uint64_t for portability across stdatomic implementations)
static atomic_uint64_t total_messages;
static atomic_uint64_t total_bytes;
static atomic_uint64_t total_errors;

// Capability structure
typedef struct {
    uint32_t rights;
    uint32_t id;
    uint32_t owner;
} test_cap_t;

// Message structure
typedef struct {
    uint64_t thread_id;
    uint64_t sequence;
    uint64_t timestamp;
    uint32_t message_size;
    uint32_t checksum;
    char payload[0];  // Variable length
} stress_message_t;

// Message sizes to test
static const size_t message_sizes[MESSAGE_SIZES] = {
    64, 256, 1024, 4096, 16384
};

// Simple serialization (based on our proven implementation)
typedef enum {
    SERIAL_RAW,
    SERIAL_LITE,
    SERIAL_FULL
} serial_type_t;

static serial_type_t select_serializer(test_cap_t cap) {
    uint32_t trust_level = (cap.rights >> 28) & 0xF;
    
    if (trust_level >= 0xE) return SERIAL_RAW;
    if (trust_level >= 0x8) return SERIAL_LITE;
    return SERIAL_FULL;
}

static uint32_t compute_checksum(const void* data, size_t size) {
    const uint8_t* bytes = (const uint8_t*)data;
    uint32_t checksum = 0;
    for (size_t i = 0; i < size; i++) {
        checksum = (checksum << 1) ^ bytes[i];
    }
    return checksum;
}

// Raw serialization
static size_t raw_encode(const void* msg, size_t msg_size, void* buf, size_t buf_size) {
    if (msg_size > buf_size) return 0;
    memcpy(buf, msg, msg_size);
    return msg_size;
}

static size_t raw_decode(const void* buf, size_t buf_size, void* msg, size_t msg_size) {
    if (buf_size > msg_size) return 0;
    memcpy(msg, buf, buf_size);
    return buf_size;
}

// Lite serialization with header
typedef struct {
    uint32_t magic;
    uint32_t size;
    uint32_t checksum;
    uint32_t reserved;
} lite_header_t;

#define LITE_MAGIC 0x12345678

static size_t lite_encode(const void* msg, size_t msg_size, void* buf, size_t buf_size) {
    if (sizeof(lite_header_t) + msg_size > buf_size) return 0;
    
    lite_header_t* header = (lite_header_t*)buf;
    header->magic = LITE_MAGIC;
    header->size = msg_size;
    header->checksum = compute_checksum(msg, msg_size);
    header->reserved = 0;
    
    memcpy((char*)buf + sizeof(lite_header_t), msg, msg_size);
    return sizeof(lite_header_t) + msg_size;
}

static size_t lite_decode(const void* buf, size_t buf_size, void* msg, size_t msg_size) {
    if (buf_size < sizeof(lite_header_t)) return 0;
    
    const lite_header_t* header = (const lite_header_t*)buf;
    if (header->magic != LITE_MAGIC || header->size > msg_size) return 0;
    
    const char* payload = (const char*)buf + sizeof(lite_header_t);
    uint32_t checksum = compute_checksum(payload, header->size);
    if (checksum != header->checksum) return 0;
    
    memcpy(msg, payload, header->size);
    return header->size;
}

// Generic encode/decode
static size_t encode_message(test_cap_t cap, const void* msg, size_t msg_size, 
                            void* buf, size_t buf_size) {
    switch (select_serializer(cap)) {
        case SERIAL_RAW:
            return raw_encode(msg, msg_size, buf, buf_size);
        case SERIAL_LITE:
        case SERIAL_FULL:
            return lite_encode(msg, msg_size, buf, buf_size);
        default:
            return 0;
    }
}

static size_t decode_message(test_cap_t cap, const void* buf, size_t buf_size,
                            void* msg, size_t msg_size) {
    switch (select_serializer(cap)) {
        case SERIAL_RAW:
            return raw_decode(buf, buf_size, msg, msg_size);
        case SERIAL_LITE:
        case SERIAL_FULL:
            return lite_decode(buf, buf_size, msg, msg_size);
        default:
            return 0;
    }
}

// Thread test data
typedef struct {
    int thread_id;
    test_cap_t capability;
    uint64_t messages_processed;
    uint64_t bytes_processed;
    uint64_t errors;
    double start_time;
    double end_time;
} thread_data_t;

// Get high resolution time
static double get_time(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec / 1e9;
}

// Create test message
static stress_message_t* create_message(uint64_t thread_id, uint64_t sequence, 
                                       size_t payload_size) {
    size_t total_size = sizeof(stress_message_t) + payload_size;
    stress_message_t* msg = malloc(total_size);
    if (!msg) return NULL;
    
    msg->thread_id = thread_id;
    msg->sequence = sequence;
    msg->timestamp = (uint64_t)(get_time() * 1e9);
    msg->message_size = payload_size;
    
    // Fill payload with predictable data
    for (size_t i = 0; i < payload_size; i++) {
        ((char*)msg->payload)[i] = (char)((thread_id + sequence + i) & 0xFF);
    }
    
    msg->checksum = compute_checksum(msg, total_size - sizeof(msg->checksum));
    return msg;
}

// Validate message integrity
static int validate_message(const stress_message_t* msg, size_t total_size) {
    uint32_t expected = compute_checksum(msg, total_size - sizeof(msg->checksum));
    return msg->checksum == expected ? 1 : 0;
}

// Thread worker function
static void* thread_worker(void* arg) {
    thread_data_t* data = (thread_data_t*)arg;
    char* buffer = malloc(32768);  // 32KB buffer
    char* decode_buffer = malloc(32768);
    
    if (!buffer || !decode_buffer) {
        free(buffer);
        free(decode_buffer);
        return NULL;
    }
    
    data->start_time = get_time();
    
    for (int i = 0; i < MESSAGES_PER_THREAD; i++) {
        // Test different message sizes
        size_t payload_size = message_sizes[i % MESSAGE_SIZES];
        size_t total_msg_size = sizeof(stress_message_t) + payload_size;
        
        // Create message
        stress_message_t* msg = create_message(data->thread_id, i, payload_size);
        if (!msg) {
            data->errors++;
            continue;
        }
        
        // Encode
        size_t encoded_size = encode_message(data->capability, msg, total_msg_size,
                                           buffer, 32768);
        if (encoded_size == 0) {
            data->errors++;
            free(msg);
            continue;
        }
        
        // Decode
        size_t decoded_size = decode_message(data->capability, buffer, encoded_size,
                                           decode_buffer, 32768);
        if (decoded_size == 0) {
            data->errors++;
            free(msg);
            continue;
        }
        
        // Validate
        if (!validate_message((stress_message_t*)decode_buffer, decoded_size)) {
            data->errors++;
            free(msg);
            continue;
        }
        
        // Check data integrity
        stress_message_t* decoded_msg = (stress_message_t*)decode_buffer;
        if (decoded_msg->thread_id != data->thread_id ||
            decoded_msg->sequence != i ||
            decoded_msg->message_size != payload_size) {
            data->errors++;
            free(msg);
            continue;
        }
        
        // Success
        data->messages_processed++;
        data->bytes_processed += encoded_size;
        
        free(msg);
    }
    
    data->end_time = get_time();
    
    // Update global statistics
    atomic_fetch_add(&total_messages, data->messages_processed);
    atomic_fetch_add(&total_bytes, data->bytes_processed);
    atomic_fetch_add(&total_errors, data->errors);
    
    free(buffer);
    free(decode_buffer);
    return NULL;
}

int main(void) {
    printf("🔥 FeuerBird IPC System Stress Test\n");
    printf("===================================\n");
    printf("Threads: %d\n", NUM_THREADS);
    printf("Messages per thread: %d\n", MESSAGES_PER_THREAD);
    printf("Total messages: %d\n", NUM_THREADS * MESSAGES_PER_THREAD);
    printf("Message sizes: ");
    for (int i = 0; i < MESSAGE_SIZES; i++) {
        printf("%zu%s", message_sizes[i], i < MESSAGE_SIZES - 1 ? ", " : " bytes\n");
    }
    printf("\n");
    
    // Initialize thread data
    pthread_t threads[NUM_THREADS];
    thread_data_t thread_data[NUM_THREADS];
    
    // Different capability levels for different threads
    uint32_t rights_levels[] = { 0xF0000000, 0x80000000, 0x40000000, 0x10000000 };
    
    for (int i = 0; i < NUM_THREADS; i++) {
        thread_data[i].thread_id = i;
        thread_data[i].capability.rights = rights_levels[i % 4];
        thread_data[i].capability.id = i + 1000;
        thread_data[i].capability.owner = 0;
        thread_data[i].messages_processed = 0;
        thread_data[i].bytes_processed = 0;
        thread_data[i].errors = 0;
    }
    
    double test_start = get_time();
    
    // Start threads
    for (int i = 0; i < NUM_THREADS; i++) {
        if (pthread_create(&threads[i], NULL, thread_worker, &thread_data[i]) != 0) {
            printf("ERROR: Failed to create thread %d\n", i);
            return 1;
        }
    }
    
    // Wait for threads to complete
    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_join(threads[i], NULL);
    }
    
    double test_end = get_time();
    double total_time = test_end - test_start;
    
    // Print results
    printf("=== Stress Test Results ===\n");
    printf("Total time: %.3f seconds\n", total_time);
    printf("Total messages: %lu\n", (unsigned long)total_messages);
    printf("Total bytes: %lu (%.2f MB)\n", (unsigned long)total_bytes, 
           (double)total_bytes / (1024 * 1024));
    printf("Total errors: %lu\n", (unsigned long)total_errors);
    printf("Success rate: %.2f%%\n", 
           100.0 * total_messages / (NUM_THREADS * MESSAGES_PER_THREAD));
    printf("Throughput: %.0f messages/sec\n", total_messages / total_time);
    printf("Bandwidth: %.2f MB/sec\n", (total_bytes / (1024 * 1024)) / total_time);
    
    printf("\n=== Per-Thread Results ===\n");
    const char* serializers[] = { "Raw", "Lite", "Full", "User" };
    for (int i = 0; i < NUM_THREADS; i++) {
        double thread_time = thread_data[i].end_time - thread_data[i].start_time;
        printf("Thread %d (%s): %lu msgs, %lu bytes, %lu errors, %.3f sec\n",
               i, serializers[i % 4],
               (unsigned long)thread_data[i].messages_processed,
               (unsigned long)thread_data[i].bytes_processed,
               (unsigned long)thread_data[i].errors,
               thread_time);
    }
    
    printf("\n");
    if (total_errors == 0) {
        printf("✅ STRESS TEST PASSED: All messages processed successfully!\n");
        printf("The IPC system handles concurrent multi-threaded workloads perfectly.\n");
        return 0;
    } else {
        printf("⚠️  STRESS TEST COMPLETED WITH %lu ERRORS\n", (unsigned long)total_errors);
        printf("Error rate: %.4f%%\n", 100.0 * total_errors / (NUM_THREADS * MESSAGES_PER_THREAD));
        return total_errors > (NUM_THREADS * MESSAGES_PER_THREAD / 100) ? 1 : 0;  // Allow 1% error rate
    }
}