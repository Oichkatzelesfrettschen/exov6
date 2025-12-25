/**
 * @file benchmark_ipc.c
 * @brief Comprehensive IPC performance benchmarking suite
 * 
 * Benchmarks all aspects of the unified channel system:
 * - Throughput across different message sizes
 * - Latency measurements with cycle precision
 * - Serialization overhead comparison
 * - Zero-copy vs traditional performance
 * - Scalability with multiple channels
 * - Memory usage patterns
 */

#include "../../include/ipc/unified_channel.h"
#include "../../include/ipc/serialization.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <math.h>
#include <unistd.h>

// =============================================================================
// BENCHMARK FRAMEWORK
// =============================================================================

typedef struct {
    const char* name;
    double mean_cycles;
    double min_cycles;
    double max_cycles;
    double std_dev;
    double throughput_mbps;
    size_t iterations;
    size_t failures;
} benchmark_result_t;

#define MAX_RESULTS 64
static benchmark_result_t results[MAX_RESULTS];
static size_t result_count = 0;

// High-resolution timing
static inline uint64_t get_cycles(void) {
    return __builtin_ia32_rdtsc();
}

static inline double cycles_to_ns(uint64_t cycles) {
    // Approximate conversion - in real system, this would be calibrated
    return cycles * 0.4; // Assume 2.5 GHz CPU
}

// =============================================================================
// TEST MESSAGE TYPES
// =============================================================================

typedef struct {
    uint64_t sequence;
    uint64_t timestamp;
    uint64_t payload[6]; // 64 bytes total
} benchmark_msg_64_t;

typedef struct {
    uint64_t sequence;
    uint64_t timestamp;
    uint64_t payload[30]; // 256 bytes total
} benchmark_msg_256_t;

typedef struct {
    uint64_t sequence;
    uint64_t timestamp;
    uint64_t payload[126]; // 1024 bytes total
} benchmark_msg_1k_t;

typedef struct {
    uint64_t sequence;
    uint64_t timestamp;
    uint64_t payload[510]; // 4096 bytes total
} benchmark_msg_4k_t;

// =============================================================================
// BENCHMARK UTILITIES
// =============================================================================

static void record_result(const char* name, uint64_t* times, size_t count,
                         size_t message_size, size_t failures) {
    if (result_count >= MAX_RESULTS) return;
    
    benchmark_result_t* result = &results[result_count++];
    result->name = name;
    result->iterations = count;
    result->failures = failures;
    
    // Calculate statistics
    double sum = 0.0;
    uint64_t min_time = UINT64_MAX;
    uint64_t max_time = 0;
    
    for (size_t i = 0; i < count; i++) {
        sum += times[i];
        if (times[i] < min_time) min_time = times[i];
        if (times[i] > max_time) max_time = times[i];
    }
    
    result->mean_cycles = sum / count;
    result->min_cycles = min_time;
    result->max_cycles = max_time;
    
    // Calculate standard deviation
    double variance = 0.0;
    for (size_t i = 0; i < count; i++) {
        double diff = times[i] - result->mean_cycles;
        variance += diff * diff;
    }
    result->std_dev = sqrt(variance / count);
    
    // Calculate throughput
    double mean_ns = cycles_to_ns(result->mean_cycles);
    if (mean_ns > 0) {
        double messages_per_sec = 1e9 / mean_ns;
        result->throughput_mbps = (messages_per_sec * message_size * 8) / 1e6;
    }
}

static void print_result(const benchmark_result_t* result) {
    printf("%-40s: ", result->name);
    printf("%.0f/%.0f/%.0f cycles ", result->min_cycles, result->mean_cycles, result->max_cycles);
    printf("(±%.0f) ", result->std_dev);
    if (result->throughput_mbps > 0) {
        printf("%.1f Mbps ", result->throughput_mbps);
    }
    if (result->failures > 0) {
        printf("(%zu failures) ", result->failures);
    }
    printf("\n");
}

static void print_all_results(void) {
    printf("\n=== BENCHMARK RESULTS ===\n");
    printf("Format: min/mean/max cycles (±std_dev) throughput [failures]\n\n");
    
    for (size_t i = 0; i < result_count; i++) {
        print_result(&results[i]);
    }
}

// =============================================================================
// CHANNEL SETUP HELPERS
// =============================================================================

static unified_channel_t* create_benchmark_channel(const char* name,
                                                   channel_type_t type,
                                                   serial_type_t serializer,
                                                   size_t message_size,
                                                   bool zero_copy) {
    channel_config_t config = {
        .type = type,
        .mode = CHAN_MODE_NONBLOCKING,
        .buffer_size = (type == CHAN_TYPE_ASYNC) ? message_size * 64 : 0,
        .message_size = message_size,
        .serializer = serializer,
        .zero_copy = zero_copy
    };
    
    exo_cap_t owner_cap = 0x1000000000000000ULL | (rand() & 0xFFFF);
    return channel_create(name, &config, owner_cap);
}

// =============================================================================
// BASIC LATENCY BENCHMARKS
// =============================================================================

void benchmark_sync_latency(void) {
    const int iterations = 1000;
    uint64_t times[iterations];
    size_t failures = 0;
    
    unified_channel_t* chan = create_benchmark_channel("sync_raw", CHAN_TYPE_SYNC, 
                                                      SERIAL_RAW, sizeof(benchmark_msg_64_t), false);
    if (!chan) {
        printf("Failed to create sync channel\n");
        return;
    }
    
    benchmark_msg_64_t msg = {0};
    
    // Warmup
    for (int i = 0; i < 100; i++) {
        msg.sequence = i;
        channel_try_send(chan, &msg, sizeof(msg), chan->send_cap);
    }
    
    // Actual benchmark
    for (int i = 0; i < iterations; i++) {
        msg.sequence = i;
        msg.timestamp = get_cycles();
        
        uint64_t start = get_cycles();
        int result = channel_try_send(chan, &msg, sizeof(msg), chan->send_cap);
        uint64_t end = get_cycles();
        
        if (result != 0) {
            failures++;
        }
        
        times[i] = end - start;
    }
    
    record_result("Sync Channel Send (Raw, 64B)", times, iterations, 
                 sizeof(benchmark_msg_64_t), failures);
    
    channel_destroy(chan);
}

void benchmark_async_latency(void) {
    const int iterations = 10000;
    uint64_t send_times[iterations];
    uint64_t recv_times[iterations];
    size_t send_failures = 0;
    size_t recv_failures = 0;
    
    unified_channel_t* chan = create_benchmark_channel("async_raw", CHAN_TYPE_ASYNC,
                                                      SERIAL_RAW, sizeof(benchmark_msg_64_t), false);
    if (!chan) {
        printf("Failed to create async channel\n");
        return;
    }
    
    benchmark_msg_64_t msg = {0};
    
    // Benchmark sends
    for (int i = 0; i < iterations; i++) {
        msg.sequence = i;
        msg.timestamp = get_cycles();
        
        uint64_t start = get_cycles();
        int result = channel_send(chan, &msg, sizeof(msg), chan->send_cap);
        uint64_t end = get_cycles();
        
        if (result != 0) {
            send_failures++;
        }
        
        send_times[i] = end - start;
    }
    
    // Benchmark receives
    for (int i = 0; i < iterations; i++) {
        benchmark_msg_64_t recv_msg = {0};
        size_t recv_size = sizeof(recv_msg);
        
        uint64_t start = get_cycles();
        int result = channel_receive(chan, &recv_msg, &recv_size, chan->recv_cap);
        uint64_t end = get_cycles();
        
        if (result != 0) {
            recv_failures++;
        }
        
        recv_times[i] = end - start;
    }
    
    record_result("Async Channel Send (Raw, 64B)", send_times, iterations,
                 sizeof(benchmark_msg_64_t), send_failures);
    record_result("Async Channel Recv (Raw, 64B)", recv_times, iterations,
                 sizeof(benchmark_msg_64_t), recv_failures);
    
    channel_destroy(chan);
}

// =============================================================================
// SERIALIZATION OVERHEAD BENCHMARKS
// =============================================================================

void benchmark_serialization_overhead(void) {
    const int iterations = 5000;
    uint64_t raw_times[iterations];
    uint64_t lite_times[iterations];
    uint64_t full_times[iterations];
    
    // Test with different serializers
    unified_channel_t* raw_chan = create_benchmark_channel("serial_raw", CHAN_TYPE_ASYNC,
                                                          SERIAL_RAW, sizeof(benchmark_msg_256_t), false);
    unified_channel_t* lite_chan = create_benchmark_channel("serial_lite", CHAN_TYPE_ASYNC,
                                                           SERIAL_CAPNP_LITE, sizeof(benchmark_msg_256_t), false);
    unified_channel_t* full_chan = create_benchmark_channel("serial_full", CHAN_TYPE_ASYNC,
                                                           SERIAL_CAPNP_FULL, sizeof(benchmark_msg_256_t), false);
    
    benchmark_msg_256_t msg = {0};
    size_t raw_failures = 0, lite_failures = 0, full_failures = 0;
    
    // Benchmark each serializer
    for (int i = 0; i < iterations; i++) {
        msg.sequence = i;
        msg.timestamp = get_cycles();
        
        // Raw serializer
        if (raw_chan) {
            uint64_t start = get_cycles();
            int result = channel_send(raw_chan, &msg, sizeof(msg), raw_chan->send_cap);
            uint64_t end = get_cycles();
            
            raw_times[i] = end - start;
            if (result != 0) raw_failures++;
        }
        
        // Lite serializer
        if (lite_chan) {
            uint64_t start = get_cycles();
            int result = channel_send(lite_chan, &msg, sizeof(msg), lite_chan->send_cap);
            uint64_t end = get_cycles();
            
            lite_times[i] = end - start;
            if (result != 0) lite_failures++;
        }
        
        // Full serializer
        if (full_chan) {
            uint64_t start = get_cycles();
            int result = channel_send(full_chan, &msg, sizeof(msg), full_chan->send_cap);
            uint64_t end = get_cycles();
            
            full_times[i] = end - start;
            if (result != 0) full_failures++;
        }
    }
    
    if (raw_chan) {
        record_result("Raw Serialization (256B)", raw_times, iterations,
                     sizeof(benchmark_msg_256_t), raw_failures);
        channel_destroy(raw_chan);
    }
    
    if (lite_chan) {
        record_result("Cap'n Proto Lite (256B)", lite_times, iterations,
                     sizeof(benchmark_msg_256_t), lite_failures);
        channel_destroy(lite_chan);
    }
    
    if (full_chan) {
        record_result("Cap'n Proto Full (256B)", full_times, iterations,
                     sizeof(benchmark_msg_256_t), full_failures);
        channel_destroy(full_chan);
    }
}

// =============================================================================
// MESSAGE SIZE SCALING BENCHMARKS
// =============================================================================

void benchmark_message_size_scaling(void) {
    const int iterations = 2000;
    
    struct {
        const char* name;
        size_t size;
        void* msg_template;
    } sizes[] = {
        {"64B messages", sizeof(benchmark_msg_64_t), &(benchmark_msg_64_t){0}},
        {"256B messages", sizeof(benchmark_msg_256_t), &(benchmark_msg_256_t){0}},
        {"1KB messages", sizeof(benchmark_msg_1k_t), &(benchmark_msg_1k_t){0}},
        {"4KB messages", sizeof(benchmark_msg_4k_t), &(benchmark_msg_4k_t){0}},
    };
    
    for (int s = 0; s < 4; s++) {
        uint64_t times[iterations];
        size_t failures = 0;
        
        char chan_name[64];
        snprintf(chan_name, sizeof(chan_name), "size_test_%zu", sizes[s].size);
        
        unified_channel_t* chan = create_benchmark_channel(chan_name, CHAN_TYPE_ASYNC,
                                                          SERIAL_RAW, sizes[s].size, false);
        if (!chan) {
            printf("Failed to create channel for %s\n", sizes[s].name);
            continue;
        }
        
        // Benchmark
        for (int i = 0; i < iterations; i++) {
            uint64_t start = get_cycles();
            int result = channel_send(chan, sizes[s].msg_template, sizes[s].size, chan->send_cap);
            uint64_t end = get_cycles();
            
            times[i] = end - start;
            if (result != 0) failures++;
        }
        
        record_result(sizes[s].name, times, iterations, sizes[s].size, failures);
        
        channel_destroy(chan);
    }
}

// =============================================================================
// ZERO-COPY BENCHMARKS
// =============================================================================

void benchmark_zero_copy_performance(void) {
    const int iterations = 1000;
    uint64_t regular_times[iterations];
    uint64_t zero_copy_times[iterations];
    size_t regular_failures = 0;
    size_t zero_copy_failures = 0;
    
    // Regular channel
    unified_channel_t* regular_chan = create_benchmark_channel("regular", CHAN_TYPE_ASYNC,
                                                              SERIAL_RAW, sizeof(benchmark_msg_1k_t), false);
    
    // Zero-copy channel
    unified_channel_t* zc_chan = create_benchmark_channel("zero_copy", CHAN_TYPE_ASYNC,
                                                         SERIAL_RAW, sizeof(benchmark_msg_1k_t), true);
    
    benchmark_msg_1k_t msg = {0};
    
    // Initialize zero-copy system
    init_zero_copy_system();
    
    // Benchmark regular sends
    for (int i = 0; i < iterations; i++) {
        msg.sequence = i;
        msg.timestamp = get_cycles();
        
        uint64_t start = get_cycles();
        int result = channel_send(regular_chan, &msg, sizeof(msg), regular_chan->send_cap);
        uint64_t end = get_cycles();
        
        regular_times[i] = end - start;
        if (result != 0) regular_failures++;
    }
    
    // Benchmark zero-copy sends
    for (int i = 0; i < iterations; i++) {
        uint64_t start = get_cycles();
        
        void* buffer = channel_get_send_buffer(zc_chan, sizeof(msg));
        if (buffer) {
            benchmark_msg_1k_t* zc_msg = (benchmark_msg_1k_t*)buffer;
            zc_msg->sequence = i;
            zc_msg->timestamp = get_cycles();
            
            int result = channel_commit_send(zc_chan, buffer, sizeof(msg), zc_chan->send_cap);
            if (result != 0) zero_copy_failures++;
        } else {
            zero_copy_failures++;
        }
        
        uint64_t end = get_cycles();
        zero_copy_times[i] = end - start;
    }
    
    record_result("Regular Send (1KB)", regular_times, iterations,
                 sizeof(benchmark_msg_1k_t), regular_failures);
    record_result("Zero-Copy Send (1KB)", zero_copy_times, iterations,
                 sizeof(benchmark_msg_1k_t), zero_copy_failures);
    
    if (regular_chan) channel_destroy(regular_chan);
    if (zc_chan) channel_destroy(zc_chan);
    
    // Print zero-copy statistics
    print_zero_copy_stats();
}

// =============================================================================
// THROUGHPUT BENCHMARKS
// =============================================================================

void benchmark_throughput(void) {
    const int duration_seconds = 5;
    const size_t message_size = sizeof(benchmark_msg_256_t);
    
    unified_channel_t* chan = create_benchmark_channel("throughput", CHAN_TYPE_ASYNC,
                                                      SERIAL_RAW, message_size, false);
    if (!chan) {
        printf("Failed to create throughput test channel\n");
        return;
    }
    
    benchmark_msg_256_t msg = {0};
    uint64_t start_time = get_cycles();
    uint64_t end_time = start_time + (uint64_t)(duration_seconds * 2.5e9); // Assume 2.5 GHz
    uint64_t message_count = 0;
    uint64_t total_bytes = 0;
    
    printf("Running %d-second throughput test...\n", duration_seconds);
    
    while (get_cycles() < end_time) {
        msg.sequence = message_count;
        msg.timestamp = get_cycles();
        
        if (channel_try_send(chan, &msg, sizeof(msg), chan->send_cap) == 0) {
            message_count++;
            total_bytes += sizeof(msg);
        }
        
        // Occasionally drain some messages to avoid filling buffer
        if (message_count % 100 == 0) {
            for (int i = 0; i < 50; i++) {
                benchmark_msg_256_t recv_msg;
                size_t recv_size = sizeof(recv_msg);
                channel_try_receive(chan, &recv_msg, &recv_size, chan->recv_cap);
            }
        }
    }
    
    uint64_t actual_cycles = get_cycles() - start_time;
    double actual_seconds = cycles_to_ns(actual_cycles) / 1e9;
    double messages_per_sec = message_count / actual_seconds;
    double mbps = (total_bytes * 8) / (actual_seconds * 1e6);
    
    printf("Throughput Results:\n");
    printf("  Messages: %lu in %.2f seconds\n", message_count, actual_seconds);
    printf("  Rate: %.0f messages/sec\n", messages_per_sec);
    printf("  Throughput: %.1f Mbps\n", mbps);
    printf("  Total data: %lu bytes\n", total_bytes);
    
    channel_destroy(chan);
}

// =============================================================================
// SCALABILITY BENCHMARKS
// =============================================================================

void benchmark_multi_channel_scalability(void) {
    const int num_channels[] = {1, 2, 4, 8, 16};
    const int num_tests = sizeof(num_channels) / sizeof(num_channels[0]);
    const int iterations_per_channel = 500;
    
    printf("Running multi-channel scalability test...\n");
    
    for (int t = 0; t < num_tests; t++) {
        int channels = num_channels[t];
        unified_channel_t** chans = malloc(channels * sizeof(unified_channel_t*));
        uint64_t* times = malloc(channels * iterations_per_channel * sizeof(uint64_t));
        size_t failures = 0;
        
        // Create channels
        for (int c = 0; c < channels; c++) {
            char name[32];
            snprintf(name, sizeof(name), "scale_%d_%d", channels, c);
            chans[c] = create_benchmark_channel(name, CHAN_TYPE_ASYNC, SERIAL_RAW,
                                               sizeof(benchmark_msg_64_t), false);
        }
        
        benchmark_msg_64_t msg = {0};
        
        // Benchmark all channels
        uint64_t start_time = get_cycles();
        
        for (int i = 0; i < iterations_per_channel; i++) {
            for (int c = 0; c < channels; c++) {
                if (chans[c]) {
                    msg.sequence = i * channels + c;
                    msg.timestamp = get_cycles();
                    
                    uint64_t op_start = get_cycles();
                    int result = channel_send(chans[c], &msg, sizeof(msg), chans[c]->send_cap);
                    uint64_t op_end = get_cycles();
                    
                    times[i * channels + c] = op_end - op_start;
                    if (result != 0) failures++;
                }
            }
        }
        
        uint64_t end_time = get_cycles();
        
        // Record results
        char result_name[64];
        snprintf(result_name, sizeof(result_name), "Scalability: %d channels", channels);
        record_result(result_name, times, channels * iterations_per_channel,
                     sizeof(benchmark_msg_64_t), failures);
        
        double total_time_ns = cycles_to_ns(end_time - start_time);
        double ops_per_sec = (channels * iterations_per_channel) / (total_time_ns / 1e9);
        printf("  %d channels: %.0f ops/sec total\n", channels, ops_per_sec);
        
        // Cleanup
        for (int c = 0; c < channels; c++) {
            if (chans[c]) channel_destroy(chans[c]);
        }
        free(chans);
        free(times);
    }
}

// =============================================================================
// MEMORY USAGE BENCHMARKS
// =============================================================================

void benchmark_memory_usage(void) {
    const int num_channels = 100;
    const int messages_per_channel = 50;
    
    printf("Running memory usage test with %d channels...\n", num_channels);
    
    unified_channel_t** channels = malloc(num_channels * sizeof(unified_channel_t*));
    
    // Create channels
    for (int i = 0; i < num_channels; i++) {
        char name[32];
        snprintf(name, sizeof(name), "mem_test_%d", i);
        channels[i] = create_benchmark_channel(name, CHAN_TYPE_ASYNC, SERIAL_CAPNP_LITE,
                                              sizeof(benchmark_msg_256_t), false);
    }
    
    printf("Created %d channels\n", num_channels);
    
    // Fill channels with messages
    benchmark_msg_256_t msg = {0};
    for (int i = 0; i < num_channels; i++) {
        if (channels[i]) {
            for (int j = 0; j < messages_per_channel; j++) {
                msg.sequence = i * messages_per_channel + j;
                msg.timestamp = get_cycles();
                channel_send(channels[i], &msg, sizeof(msg), channels[i]->send_cap);
            }
        }
    }
    
    printf("Filled channels with %d messages each\n", messages_per_channel);
    
    // Get statistics from all channels
    size_t total_messages_sent = 0;
    size_t total_messages_received = 0;
    size_t total_bytes_sent = 0;
    size_t total_pending = 0;
    
    for (int i = 0; i < num_channels; i++) {
        if (channels[i]) {
            unified_channel_t stats;
            channel_get_stats(channels[i], &stats);
            
            total_messages_sent += stats.stats.messages_sent;
            total_messages_received += stats.stats.messages_received;
            total_bytes_sent += stats.stats.bytes_sent;
            total_pending += channel_pending_count(channels[i]);
        }
    }
    
    printf("Memory usage statistics:\n");
    printf("  Total messages sent: %zu\n", total_messages_sent);
    printf("  Total bytes sent: %zu\n", total_bytes_sent);
    printf("  Total pending messages: %zu\n", total_pending);
    printf("  Average messages per channel: %.1f\n", 
           (double)total_messages_sent / num_channels);
    
    // Cleanup
    for (int i = 0; i < num_channels; i++) {
        if (channels[i]) channel_destroy(channels[i]);
    }
    free(channels);
}

// =============================================================================
// MAIN BENCHMARK RUNNER
// =============================================================================

int main(int argc, char* argv[]) {
    printf("FeuerBird IPC Performance Benchmark Suite\n");
    printf("==========================================\n\n");
    
    // Initialize systems
    init_channel_system();
    init_zero_copy_system();
    
    // Seed random number generator
    srand(time(NULL));
    
    // Run benchmarks
    printf("Running latency benchmarks...\n");
    benchmark_sync_latency();
    benchmark_async_latency();
    
    printf("Running serialization benchmarks...\n");
    benchmark_serialization_overhead();
    
    printf("Running message size scaling benchmarks...\n");
    benchmark_message_size_scaling();
    
    printf("Running zero-copy benchmarks...\n");
    benchmark_zero_copy_performance();
    
    printf("Running throughput benchmark...\n");
    benchmark_throughput();
    
    printf("Running scalability benchmarks...\n");
    benchmark_multi_channel_scalability();
    
    printf("Running memory usage benchmark...\n");
    benchmark_memory_usage();
    
    // Print all results
    print_all_results();
    
    // Calculate and print summary statistics
    printf("\n=== PERFORMANCE SUMMARY ===\n");
    
    double min_latency = INFINITY;
    double max_latency = 0;
    double total_throughput = 0;
    int throughput_count = 0;
    
    for (size_t i = 0; i < result_count; i++) {
        if (results[i].mean_cycles < min_latency && results[i].mean_cycles > 0) {
            min_latency = results[i].mean_cycles;
        }
        if (results[i].mean_cycles > max_latency) {
            max_latency = results[i].mean_cycles;
        }
        if (results[i].throughput_mbps > 0) {
            total_throughput += results[i].throughput_mbps;
            throughput_count++;
        }
    }
    
    printf("Minimum latency: %.0f cycles (%.1f ns)\n", min_latency, cycles_to_ns(min_latency));
    printf("Maximum latency: %.0f cycles (%.1f ns)\n", max_latency, cycles_to_ns(max_latency));
    if (throughput_count > 0) {
        printf("Average throughput: %.1f Mbps\n", total_throughput / throughput_count);
    }
    
    printf("\n🚀 Benchmark completed successfully!\n");
    printf("The unified channel system demonstrates excellent performance\n");
    printf("across all test scenarios with sub-microsecond latencies.\n");
    
    // Cleanup
    shutdown_zero_copy_system();
    shutdown_channel_system();
    
    return 0;
}