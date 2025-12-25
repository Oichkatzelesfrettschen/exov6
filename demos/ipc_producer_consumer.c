/**
 * @file ipc_producer_consumer.c
 * @brief Producer-Consumer demo using unified channel system
 * 
 * Demonstrates:
 * - High-performance producer-consumer pattern
 * - Multiple serialization layers
 * - Zero-copy optimizations
 * - Performance monitoring
 * - Error handling and recovery
 */

#include "../include/ipc/unified_channel.h"
#include "../include/ipc/serialization.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <pthread.h>
#include <signal.h>

// =============================================================================
// DEMO CONFIGURATION
// =============================================================================

#define MAX_PRODUCERS 8
#define MAX_CONSUMERS 8
#define MESSAGES_PER_PRODUCER 10000
#define BUFFER_SIZE (1024 * 1024) // 1MB buffer

// =============================================================================
// MESSAGE TYPES
// =============================================================================

typedef enum {
    MSG_TYPE_DATA,
    MSG_TYPE_COMMAND,
    MSG_TYPE_STATUS,
    MSG_TYPE_SHUTDOWN
} message_type_t;

typedef struct {
    message_type_t type;
    uint64_t sequence;
    uint64_t timestamp;
    uint32_t producer_id;
    uint32_t data_size;
    uint8_t data[256];
} work_message_t;

typedef struct {
    uint64_t messages_produced;
    uint64_t messages_consumed;
    uint64_t bytes_transferred;
    uint64_t processing_time_ns;
    uint32_t active_producers;
    uint32_t active_consumers;
} status_message_t;

// Define typed channels
DEFINE_TYPED_CHANNEL(work, work_message_t);
DEFINE_TYPED_CHANNEL(status, status_message_t);

// =============================================================================
// DEMO STATE
// =============================================================================

static volatile bool demo_running = true;
static work_channel_t* work_channel = NULL;
static status_channel_t* status_channel = NULL;

// Statistics
static volatile uint64_t total_produced = 0;
static volatile uint64_t total_consumed = 0;
static volatile uint64_t total_bytes = 0;
static volatile uint32_t active_producers = 0;
static volatile uint32_t active_consumers = 0;

// =============================================================================
// PRODUCER THREAD
// =============================================================================

typedef struct {
    uint32_t producer_id;
    uint32_t message_count;
    serial_type_t serializer;
    bool use_zero_copy;
} producer_args_t;

void* producer_thread(void* arg) {
    producer_args_t* args = (producer_args_t*)arg;
    uint64_t local_produced = 0;
    uint64_t local_bytes = 0;
    
    printf("Producer %u starting (serializer: %s, zero-copy: %s)\n", 
           args->producer_id,
           args->serializer == SERIAL_RAW ? "RAW" : 
           args->serializer == SERIAL_CAPNP_LITE ? "LITE" : "FULL",
           args->use_zero_copy ? "ON" : "OFF");
    
    __sync_fetch_and_add(&active_producers, 1);
    
    for (uint32_t i = 0; i < args->message_count && demo_running; i++) {
        work_message_t msg = {0};
        msg.type = MSG_TYPE_DATA;
        msg.sequence = i;
        msg.timestamp = __builtin_ia32_rdtsc();
        msg.producer_id = args->producer_id;
        msg.data_size = sizeof(msg.data);
        
        // Fill with test data
        for (int j = 0; j < sizeof(msg.data); j++) {
            msg.data[j] = (args->producer_id * 256 + i + j) & 0xFF;
        }
        
        // Send message
        int result;
        if (args->use_zero_copy) {
            void* buffer = channel_get_send_buffer(work_channel->chan, sizeof(msg));
            if (buffer) {
                memcpy(buffer, &msg, sizeof(msg));
                result = channel_commit_send(work_channel->chan, buffer, sizeof(msg),
                                           work_channel->chan->send_cap);
            } else {
                result = work_channel_send(work_channel, &msg, work_channel->chan->send_cap);
            }
        } else {
            result = work_channel_send(work_channel, &msg, work_channel->chan->send_cap);
        }
        
        if (result == 0) {
            local_produced++;
            local_bytes += sizeof(msg);
            __sync_fetch_and_add(&total_produced, 1);
            __sync_fetch_and_add(&total_bytes, sizeof(msg));
        } else if (result == -2) {
            // Would block - try again
            i--;
            usleep(100); // Brief pause
        } else {
            printf("Producer %u: Send failed with error %d\n", args->producer_id, result);
        }
        
        // Occasional status update
        if (i % 1000 == 0) {
            printf("Producer %u: Sent %u messages\n", args->producer_id, i);
        }
    }
    
    // Send shutdown message
    work_message_t shutdown_msg = {0};
    shutdown_msg.type = MSG_TYPE_SHUTDOWN;
    shutdown_msg.producer_id = args->producer_id;
    work_channel_send(work_channel, &shutdown_msg, work_channel->chan->send_cap);
    
    printf("Producer %u completed: %lu messages, %lu bytes\n",
           args->producer_id, local_produced, local_bytes);
    
    __sync_fetch_and_sub(&active_producers, 1);
    return NULL;
}

// =============================================================================
// CONSUMER THREAD
// =============================================================================

typedef struct {
    uint32_t consumer_id;
    bool enable_processing;
    uint32_t processing_delay_us;
} consumer_args_t;

void* consumer_thread(void* arg) {
    consumer_args_t* args = (consumer_args_t*)arg;
    uint64_t local_consumed = 0;
    uint64_t local_bytes = 0;
    uint64_t processing_time = 0;
    uint32_t shutdown_count = 0;
    
    printf("Consumer %u starting (processing: %s, delay: %u μs)\n",
           args->consumer_id,
           args->enable_processing ? "ON" : "OFF",
           args->processing_delay_us);
    
    __sync_fetch_and_add(&active_consumers, 1);
    
    while (demo_running) {
        work_message_t msg = {0};
        
        // Try to receive message
        int result = work_channel_receive(work_channel, &msg, work_channel->chan->recv_cap);
        
        if (result == 0) {
            local_consumed++;
            local_bytes += sizeof(msg);
            __sync_fetch_and_add(&total_consumed, 1);
            
            // Handle different message types
            if (msg.type == MSG_TYPE_SHUTDOWN) {
                shutdown_count++;
                printf("Consumer %u: Received shutdown from producer %u\n",
                       args->consumer_id, msg.producer_id);
                
                // If all producers have shutdown, exit
                if (shutdown_count >= MAX_PRODUCERS || active_producers == 0) {
                    break;
                }
                continue;
            }
            
            // Simulate processing
            if (args->enable_processing) {
                uint64_t start = __builtin_ia32_rdtsc();
                
                // Validate data
                bool valid = true;
                for (int j = 0; j < msg.data_size && valid; j++) {
                    uint8_t expected = (msg.producer_id * 256 + msg.sequence + j) & 0xFF;
                    if (msg.data[j] != expected) {
                        valid = false;
                        printf("Consumer %u: Data corruption in message %lu from producer %u\n",
                               args->consumer_id, msg.sequence, msg.producer_id);
                    }
                }
                
                // Processing delay
                if (args->processing_delay_us > 0) {
                    usleep(args->processing_delay_us);
                }
                
                uint64_t end = __builtin_ia32_rdtsc();
                processing_time += (end - start);
            }
            
            // Periodic status
            if (local_consumed % 2000 == 0) {
                printf("Consumer %u: Processed %lu messages\n", 
                       args->consumer_id, local_consumed);
            }
            
        } else if (result == -2) {
            // Would block - brief pause
            usleep(1000);
        } else {
            printf("Consumer %u: Receive failed with error %d\n", args->consumer_id, result);
            usleep(1000);
        }
    }
    
    printf("Consumer %u completed: %lu messages, %lu bytes, %lu cycles processing\n",
           args->consumer_id, local_consumed, local_bytes, processing_time);
    
    __sync_fetch_and_sub(&active_consumers, 1);
    return NULL;
}

// =============================================================================
// STATUS MONITOR THREAD
// =============================================================================

void* status_monitor_thread(void* arg) {
    (void)arg; // Unused
    
    printf("Status monitor starting\n");
    
    uint64_t last_produced = 0;
    uint64_t last_consumed = 0;
    uint64_t last_bytes = 0;
    time_t last_time = time(NULL);
    
    while (demo_running) {
        sleep(2); // Update every 2 seconds
        
        time_t current_time = time(NULL);
        uint64_t current_produced = total_produced;
        uint64_t current_consumed = total_consumed;
        uint64_t current_bytes = total_bytes;
        
        double elapsed = difftime(current_time, last_time);
        if (elapsed > 0) {
            double produce_rate = (current_produced - last_produced) / elapsed;
            double consume_rate = (current_consumed - last_consumed) / elapsed;
            double byte_rate = (current_bytes - last_bytes) / elapsed;
            double throughput_mbps = (byte_rate * 8) / 1e6;
            
            printf("\n=== STATUS UPDATE ===\n");
            printf("Produced: %lu total (%.0f/sec)\n", current_produced, produce_rate);
            printf("Consumed: %lu total (%.0f/sec)\n", current_consumed, consume_rate);
            printf("Throughput: %.2f MB/sec (%.2f Mbps)\n", byte_rate / 1e6, throughput_mbps);
            printf("Backlog: %lu messages\n", current_produced - current_consumed);
            printf("Active: %u producers, %u consumers\n", active_producers, active_consumers);
            
            // Get channel statistics
            if (work_channel && work_channel->chan) {
                unified_channel_t stats;
                channel_get_stats(work_channel->chan, &stats);
                printf("Channel stats: %lu pending, %lu zero-copy ops\n",
                       channel_pending_count(work_channel->chan),
                       stats.stats.zero_copy_count);
                printf("Errors: %lu send, %lu recv, %lu serial, %lu cap\n",
                       stats.errors.send_errors, stats.errors.recv_errors,
                       stats.errors.serial_errors, stats.errors.cap_errors);
            }
            printf("====================\n\n");
            
            // Send status message
            if (status_channel) {
                status_message_t status_msg = {
                    .messages_produced = current_produced,
                    .messages_consumed = current_consumed,
                    .bytes_transferred = current_bytes,
                    .active_producers = active_producers,
                    .active_consumers = active_consumers
                };
                
                status_channel_send(status_channel, &status_msg, 
                                   status_channel->chan->send_cap);
            }
        }
        
        last_produced = current_produced;
        last_consumed = current_consumed;
        last_bytes = current_bytes;
        last_time = current_time;
    }
    
    printf("Status monitor shutting down\n");
    return NULL;
}

// =============================================================================
// SIGNAL HANDLING
// =============================================================================

void signal_handler(int sig) {
    printf("\nReceived signal %d, shutting down gracefully...\n", sig);
    demo_running = false;
}

// =============================================================================
// MAIN DEMO
// =============================================================================

void print_usage(const char* program) {
    printf("Usage: %s [options]\n", program);
    printf("Options:\n");
    printf("  -p N     Number of producer threads (1-%d, default: 2)\n", MAX_PRODUCERS);
    printf("  -c N     Number of consumer threads (1-%d, default: 2)\n", MAX_CONSUMERS);
    printf("  -m N     Messages per producer (default: %d)\n", MESSAGES_PER_PRODUCER);
    printf("  -s TYPE  Serialization type (raw|lite|full, default: raw)\n");
    printf("  -z       Enable zero-copy optimization\n");
    printf("  -d N     Consumer processing delay in microseconds (default: 0)\n");
    printf("  -h       Show this help\n");
}

int main(int argc, char* argv[]) {
    // Default configuration
    int num_producers = 2;
    int num_consumers = 2;
    int messages_per_producer = MESSAGES_PER_PRODUCER;
    serial_type_t serializer = SERIAL_RAW;
    bool use_zero_copy = false;
    uint32_t processing_delay = 0;
    
    // Parse command line arguments
    int opt;
    while ((opt = getopt(argc, argv, "p:c:m:s:zd:h")) != -1) {
        switch (opt) {
            case 'p':
                num_producers = atoi(optarg);
                if (num_producers < 1 || num_producers > MAX_PRODUCERS) {
                    fprintf(stderr, "Invalid number of producers\n");
                    return 1;
                }
                break;
            case 'c':
                num_consumers = atoi(optarg);
                if (num_consumers < 1 || num_consumers > MAX_CONSUMERS) {
                    fprintf(stderr, "Invalid number of consumers\n");
                    return 1;
                }
                break;
            case 'm':
                messages_per_producer = atoi(optarg);
                if (messages_per_producer < 1) {
                    fprintf(stderr, "Invalid message count\n");
                    return 1;
                }
                break;
            case 's':
                if (strcmp(optarg, "raw") == 0) {
                    serializer = SERIAL_RAW;
                } else if (strcmp(optarg, "lite") == 0) {
                    serializer = SERIAL_CAPNP_LITE;
                } else if (strcmp(optarg, "full") == 0) {
                    serializer = SERIAL_CAPNP_FULL;
                } else {
                    fprintf(stderr, "Invalid serializer type\n");
                    return 1;
                }
                break;
            case 'z':
                use_zero_copy = true;
                break;
            case 'd':
                processing_delay = atoi(optarg);
                break;
            case 'h':
                print_usage(argv[0]);
                return 0;
            default:
                print_usage(argv[0]);
                return 1;
        }
    }
    
    printf("FeuerBird IPC Producer-Consumer Demo\n");
    printf("====================================\n");
    printf("Configuration:\n");
    printf("  Producers: %d\n", num_producers);
    printf("  Consumers: %d\n", num_consumers);
    printf("  Messages per producer: %d\n", messages_per_producer);
    printf("  Serializer: %s\n", 
           serializer == SERIAL_RAW ? "Raw" :
           serializer == SERIAL_CAPNP_LITE ? "Cap'n Proto Lite" : "Cap'n Proto Full");
    printf("  Zero-copy: %s\n", use_zero_copy ? "Enabled" : "Disabled");
    printf("  Processing delay: %u μs\n", processing_delay);
    printf("\n");
    
    // Setup signal handling
    signal(SIGINT, signal_handler);
    signal(SIGTERM, signal_handler);
    
    // Initialize systems
    init_channel_system();
    if (use_zero_copy) {
        init_zero_copy_system();
    }
    
    // Create channels
    channel_config_t work_config = {
        .type = CHAN_TYPE_ASYNC,
        .mode = CHAN_MODE_NONBLOCKING,
        .buffer_size = BUFFER_SIZE,
        .message_size = sizeof(work_message_t),
        .serializer = serializer,
        .zero_copy = use_zero_copy,
        .ordered = true,
        .reliable = true
    };
    
    channel_config_t status_config = {
        .type = CHAN_TYPE_ASYNC,
        .mode = CHAN_MODE_NONBLOCKING,
        .buffer_size = sizeof(status_message_t) * 64,
        .message_size = sizeof(status_message_t),
        .serializer = SERIAL_RAW,
        .zero_copy = false
    };
    
    exo_cap_t owner_cap = 0x1000000000000000ULL;
    
    work_channel = work_channel_create("work_queue", &work_config, owner_cap);
    status_channel = status_channel_create("status_queue", &status_config, owner_cap);
    
    if (!work_channel || !status_channel) {
        fprintf(stderr, "Failed to create channels\n");
        return 1;
    }
    
    printf("Channels created successfully\n");
    
    // Create threads
    pthread_t producer_threads[MAX_PRODUCERS];
    pthread_t consumer_threads[MAX_CONSUMERS];
    pthread_t monitor_thread;
    
    producer_args_t producer_args[MAX_PRODUCERS];
    consumer_args_t consumer_args[MAX_CONSUMERS];
    
    printf("Starting threads...\n");
    
    // Start monitor thread
    if (pthread_create(&monitor_thread, NULL, status_monitor_thread, NULL) != 0) {
        perror("Failed to create monitor thread");
        return 1;
    }
    
    // Start producer threads
    for (int i = 0; i < num_producers; i++) {
        producer_args[i].producer_id = i;
        producer_args[i].message_count = messages_per_producer;
        producer_args[i].serializer = serializer;
        producer_args[i].use_zero_copy = use_zero_copy;
        
        if (pthread_create(&producer_threads[i], NULL, producer_thread, &producer_args[i]) != 0) {
            perror("Failed to create producer thread");
            return 1;
        }
    }
    
    // Start consumer threads
    for (int i = 0; i < num_consumers; i++) {
        consumer_args[i].consumer_id = i;
        consumer_args[i].enable_processing = true;
        consumer_args[i].processing_delay_us = processing_delay;
        
        if (pthread_create(&consumer_threads[i], NULL, consumer_thread, &consumer_args[i]) != 0) {
            perror("Failed to create consumer thread");
            return 1;
        }
    }
    
    printf("All threads started, demo running...\n");
    printf("Press Ctrl+C to stop gracefully\n\n");
    
    // Wait for producers to complete
    for (int i = 0; i < num_producers; i++) {
        pthread_join(producer_threads[i], NULL);
    }
    
    printf("All producers completed\n");
    
    // Wait a bit for consumers to catch up
    sleep(5);
    
    // Signal shutdown
    demo_running = false;
    
    // Wait for consumers and monitor
    for (int i = 0; i < num_consumers; i++) {
        pthread_join(consumer_threads[i], NULL);
    }
    
    pthread_join(monitor_thread, NULL);
    
    // Final statistics
    printf("\n=== FINAL STATISTICS ===\n");
    printf("Total produced: %lu messages\n", total_produced);
    printf("Total consumed: %lu messages\n", total_consumed);
    printf("Total bytes transferred: %lu\n", total_bytes);
    printf("Messages lost: %lu\n", 
           total_produced > total_consumed ? total_produced - total_consumed : 0);
    
    // Channel statistics
    if (work_channel && work_channel->chan) {
        unified_channel_t stats;
        channel_get_stats(work_channel->chan, &stats);
        
        printf("Channel performance:\n");
        printf("  Messages sent: %lu\n", stats.stats.messages_sent);
        printf("  Messages received: %lu\n", stats.stats.messages_received);
        printf("  Bytes sent: %lu\n", stats.stats.bytes_sent);
        printf("  Bytes received: %lu\n", stats.stats.bytes_received);
        printf("  Zero-copy operations: %lu\n", stats.stats.zero_copy_count);
        printf("  Average send time: %.1f ns\n",
               stats.stats.messages_sent > 0 ?
               (double)stats.stats.send_blocked_ns * 0.4 / stats.stats.messages_sent : 0);
        printf("  Average receive time: %.1f ns\n",
               stats.stats.messages_received > 0 ?
               (double)stats.stats.recv_blocked_ns * 0.4 / stats.stats.messages_received : 0);
        printf("Errors:\n");
        printf("  Send errors: %lu\n", stats.errors.send_errors);
        printf("  Receive errors: %lu\n", stats.errors.recv_errors);
        printf("  Serialization errors: %lu\n", stats.errors.serial_errors);
        printf("  Capability errors: %lu\n", stats.errors.cap_errors);
    }
    
    // Zero-copy statistics
    if (use_zero_copy) {
        printf("\n");
        print_zero_copy_stats();
    }
    
    printf("========================\n");
    
    // Cleanup
    if (work_channel) work_channel_destroy(work_channel);
    if (status_channel) status_channel_destroy(status_channel);
    
    if (use_zero_copy) {
        shutdown_zero_copy_system();
    }
    shutdown_channel_system();
    
    printf("Demo completed successfully!\n");
    return 0;
}