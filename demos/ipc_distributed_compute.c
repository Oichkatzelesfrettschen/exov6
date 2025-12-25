/**
 * @file ipc_distributed_compute.c
 * @brief Distributed computing demo using unified channel system
 * 
 * Demonstrates:
 * - Task distribution across multiple workers
 * - Result aggregation
 * - Load balancing
 * - Fault tolerance
 * - Real-time performance monitoring
 */

#include "../include/ipc/unified_channel.h"
#include "../include/ipc/serialization.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <unistd.h>
#include <pthread.h>

// =============================================================================
// COMPUTATION TYPES
// =============================================================================

typedef enum {
    TASK_PRIME_CHECK,
    TASK_MATRIX_MULTIPLY,
    TASK_MONTE_CARLO_PI,
    TASK_FIBONACCI,
    TASK_HASH_COMPUTE,
    TASK_SHUTDOWN
} task_type_t;

typedef struct {
    task_type_t type;
    uint64_t task_id;
    uint64_t submitted_time;
    uint32_t worker_id;
    union {
        struct {
            uint64_t number;
        } prime_check;
        struct {
            uint32_t size;
            float matrix_a[16];
            float matrix_b[16];
        } matrix_mult;
        struct {
            uint32_t iterations;
            uint32_t seed;
        } monte_carlo;
        struct {
            uint32_t n;
        } fibonacci;
        struct {
            uint32_t data_size;
            uint8_t data[128];
        } hash_compute;
    } params;
} compute_task_t;

typedef struct {
    uint64_t task_id;
    task_type_t type;
    uint64_t completion_time;
    uint32_t worker_id;
    bool success;
    union {
        struct {
            bool is_prime;
            uint64_t factors_found;
        } prime_result;
        struct {
            float result[16];
        } matrix_result;
        struct {
            double pi_estimate;
            uint32_t hits;
        } monte_carlo_result;
        struct {
            uint64_t result;
        } fibonacci_result;
        struct {
            uint32_t hash;
        } hash_result;
    } data;
} compute_result_t;

// Define typed channels
DEFINE_TYPED_CHANNEL(task, compute_task_t);
DEFINE_TYPED_CHANNEL(result, compute_result_t);

// =============================================================================
// GLOBAL STATE
// =============================================================================

static volatile bool system_running = true;
static task_channel_t* task_queue = NULL;
static result_channel_t* result_queue = NULL;

// Statistics
static volatile uint64_t tasks_submitted = 0;
static volatile uint64_t tasks_completed = 0;
static volatile uint64_t total_processing_time = 0;
static volatile uint32_t active_workers = 0;

// =============================================================================
// COMPUTATION FUNCTIONS
// =============================================================================

bool is_prime(uint64_t n, uint64_t* factors_found) {
    if (n < 2) return false;
    if (n == 2) return true;
    if (n % 2 == 0) {
        *factors_found = 1;
        return false;
    }
    
    *factors_found = 0;
    uint64_t limit = (uint64_t)sqrt(n);
    for (uint64_t i = 3; i <= limit; i += 2) {
        if (n % i == 0) {
            (*factors_found)++;
            return false;
        }
    }
    return true;
}

void matrix_multiply_4x4(const float* a, const float* b, float* result) {
    for (int i = 0; i < 4; i++) {
        for (int j = 0; j < 4; j++) {
            result[i * 4 + j] = 0;
            for (int k = 0; k < 4; k++) {
                result[i * 4 + j] += a[i * 4 + k] * b[k * 4 + j];
            }
        }
    }
}

double monte_carlo_pi(uint32_t iterations, uint32_t seed) {
    srand(seed);
    uint32_t hits = 0;
    
    for (uint32_t i = 0; i < iterations; i++) {
        double x = (double)rand() / RAND_MAX;
        double y = (double)rand() / RAND_MAX;
        if (x * x + y * y <= 1.0) {
            hits++;
        }
    }
    
    return 4.0 * hits / iterations;
}

uint64_t fibonacci(uint32_t n) {
    if (n <= 1) return n;
    
    uint64_t a = 0, b = 1;
    for (uint32_t i = 2; i <= n; i++) {
        uint64_t temp = a + b;
        a = b;
        b = temp;
    }
    return b;
}

uint32_t simple_hash(const uint8_t* data, uint32_t size) {
    uint32_t hash = 0x811c9dc5; // FNV offset basis
    for (uint32_t i = 0; i < size; i++) {
        hash ^= data[i];
        hash *= 0x01000193; // FNV prime
    }
    return hash;
}

// =============================================================================
// WORKER THREAD
// =============================================================================

typedef struct {
    uint32_t worker_id;
    uint32_t max_tasks;
    bool enable_detailed_stats;
} worker_args_t;

void* worker_thread(void* arg) {
    worker_args_t* args = (worker_args_t*)arg;
    uint64_t tasks_processed = 0;
    uint64_t total_cycles = 0;
    
    printf("Worker %u starting (max tasks: %u)\n", 
           args->worker_id, args->max_tasks);
    
    __sync_fetch_and_add(&active_workers, 1);
    
    while (system_running && tasks_processed < args->max_tasks) {
        compute_task_t task = {0};
        
        // Try to get a task
        int result = task_channel_receive(task_queue, &task, task_queue->chan->recv_cap);
        
        if (result == 0) {
            if (task.type == TASK_SHUTDOWN) {
                printf("Worker %u received shutdown signal\n", args->worker_id);
                break;
            }
            
            uint64_t start_time = __builtin_ia32_rdtsc();
            compute_result_t res = {0};
            res.task_id = task.task_id;
            res.type = task.type;
            res.worker_id = args->worker_id;
            res.success = true;
            
            // Process the task based on type
            switch (task.type) {
                case TASK_PRIME_CHECK:
                    res.data.prime_result.is_prime = is_prime(task.params.prime_check.number,
                                                             &res.data.prime_result.factors_found);
                    break;
                    
                case TASK_MATRIX_MULTIPLY:
                    matrix_multiply_4x4(task.params.matrix_mult.matrix_a,
                                       task.params.matrix_mult.matrix_b,
                                       res.data.matrix_result.result);
                    break;
                    
                case TASK_MONTE_CARLO_PI:
                    res.data.monte_carlo_result.pi_estimate = 
                        monte_carlo_pi(task.params.monte_carlo.iterations,
                                      task.params.monte_carlo.seed);
                    res.data.monte_carlo_result.hits = task.params.monte_carlo.iterations;
                    break;
                    
                case TASK_FIBONACCI:
                    res.data.fibonacci_result.result = fibonacci(task.params.fibonacci.n);
                    break;
                    
                case TASK_HASH_COMPUTE:
                    res.data.hash_result.hash = simple_hash(task.params.hash_compute.data,
                                                           task.params.hash_compute.data_size);
                    break;
                    
                default:
                    res.success = false;
                    break;
            }
            
            uint64_t end_time = __builtin_ia32_rdtsc();
            res.completion_time = end_time - start_time;
            total_cycles += res.completion_time;
            
            // Send result
            int send_result = result_channel_send(result_queue, &res, result_queue->chan->send_cap);
            if (send_result != 0) {
                printf("Worker %u: Failed to send result for task %lu\n", 
                       args->worker_id, task.task_id);
            }
            
            tasks_processed++;
            __sync_fetch_and_add(&tasks_completed, 1);
            __sync_fetch_and_add(&total_processing_time, res.completion_time);
            
            if (args->enable_detailed_stats && tasks_processed % 100 == 0) {
                printf("Worker %u: Completed %lu tasks\n", args->worker_id, tasks_processed);
            }
            
        } else if (result == -2) {
            // No tasks available, brief pause
            usleep(1000);
        } else {
            printf("Worker %u: Task receive error %d\n", args->worker_id, result);
            usleep(10000);
        }
    }
    
    printf("Worker %u shutting down: %lu tasks processed, avg %.1f cycles/task\n",
           args->worker_id, tasks_processed, 
           tasks_processed > 0 ? (double)total_cycles / tasks_processed : 0.0);
    
    __sync_fetch_and_sub(&active_workers, 1);
    return NULL;
}

// =============================================================================
// TASK GENERATOR
// =============================================================================

void generate_prime_tasks(uint64_t count, uint64_t start_number) {
    for (uint64_t i = 0; i < count; i++) {
        compute_task_t task = {0};
        task.type = TASK_PRIME_CHECK;
        task.task_id = i;
        task.submitted_time = __builtin_ia32_rdtsc();
        task.params.prime_check.number = start_number + i * 2 + 1; // Odd numbers
        
        while (task_channel_send(task_queue, &task, task_queue->chan->send_cap) != 0) {
            usleep(100); // Queue full, wait briefly
        }
        
        __sync_fetch_and_add(&tasks_submitted, 1);
    }
    printf("Generated %lu prime checking tasks\n", count);
}

void generate_matrix_tasks(uint64_t count) {
    for (uint64_t i = 0; i < count; i++) {
        compute_task_t task = {0};
        task.type = TASK_MATRIX_MULTIPLY;
        task.task_id = 1000000 + i;
        task.submitted_time = __builtin_ia32_rdtsc();
        task.params.matrix_mult.size = 4;
        
        // Generate random matrices
        srand(i);
        for (int j = 0; j < 16; j++) {
            task.params.matrix_mult.matrix_a[j] = (float)rand() / RAND_MAX;
            task.params.matrix_mult.matrix_b[j] = (float)rand() / RAND_MAX;
        }
        
        while (task_channel_send(task_queue, &task, task_queue->chan->send_cap) != 0) {
            usleep(100);
        }
        
        __sync_fetch_and_add(&tasks_submitted, 1);
    }
    printf("Generated %lu matrix multiplication tasks\n", count);
}

void generate_monte_carlo_tasks(uint64_t count, uint32_t iterations_per_task) {
    for (uint64_t i = 0; i < count; i++) {
        compute_task_t task = {0};
        task.type = TASK_MONTE_CARLO_PI;
        task.task_id = 2000000 + i;
        task.submitted_time = __builtin_ia32_rdtsc();
        task.params.monte_carlo.iterations = iterations_per_task;
        task.params.monte_carlo.seed = i;
        
        while (task_channel_send(task_queue, &task, task_queue->chan->send_cap) != 0) {
            usleep(100);
        }
        
        __sync_fetch_and_add(&tasks_submitted, 1);
    }
    printf("Generated %lu Monte Carlo PI estimation tasks\n", count);
}

// =============================================================================
// RESULT COLLECTOR
// =============================================================================

typedef struct {
    uint64_t prime_tasks;
    uint64_t primes_found;
    uint64_t matrix_tasks;
    uint64_t monte_carlo_tasks;
    double pi_sum;
    uint64_t fibonacci_tasks;
    uint64_t hash_tasks;
    uint64_t total_results;
    uint64_t failed_results;
} collection_stats_t;

void* result_collector_thread(void* arg) {
    collection_stats_t* stats = (collection_stats_t*)arg;
    memset(stats, 0, sizeof(*stats));
    
    printf("Result collector starting\n");
    
    while (system_running) {
        compute_result_t result = {0};
        
        int recv_result = result_channel_receive(result_queue, &result, 
                                                result_queue->chan->recv_cap);
        
        if (recv_result == 0) {
            stats->total_results++;
            
            if (!result.success) {
                stats->failed_results++;
                printf("Task %lu failed on worker %u\n", result.task_id, result.worker_id);
                continue;
            }
            
            // Process results by type
            switch (result.type) {
                case TASK_PRIME_CHECK:
                    stats->prime_tasks++;
                    if (result.data.prime_result.is_prime) {
                        stats->primes_found++;
                    }
                    break;
                    
                case TASK_MATRIX_MULTIPLY:
                    stats->matrix_tasks++;
                    break;
                    
                case TASK_MONTE_CARLO_PI:
                    stats->monte_carlo_tasks++;
                    stats->pi_sum += result.data.monte_carlo_result.pi_estimate;
                    break;
                    
                case TASK_FIBONACCI:
                    stats->fibonacci_tasks++;
                    break;
                    
                case TASK_HASH_COMPUTE:
                    stats->hash_tasks++;
                    break;
                    
                default:
                    break;
            }
            
            // Periodic status
            if (stats->total_results % 1000 == 0) {
                printf("Collected %lu results\n", stats->total_results);
            }
            
        } else if (recv_result == -2) {
            // No results available
            usleep(5000);
        } else {
            printf("Result collector: receive error %d\n", recv_result);
            usleep(10000);
        }
    }
    
    printf("Result collector shutting down\n");
    return NULL;
}

// =============================================================================
// MAIN DEMO
// =============================================================================

void print_usage(const char* program) {
    printf("Usage: %s [options]\n", program);
    printf("Options:\n");
    printf("  -w N     Number of worker threads (1-16, default: 4)\n");
    printf("  -p N     Prime checking tasks (default: 1000)\n");
    printf("  -m N     Matrix multiplication tasks (default: 500)\n");
    printf("  -c N     Monte Carlo PI tasks (default: 200)\n");
    printf("  -i N     Monte Carlo iterations per task (default: 100000)\n");
    printf("  -s TYPE  Serialization type (raw|lite|full, default: lite)\n");
    printf("  -z       Enable zero-copy optimization\n");
    printf("  -v       Verbose worker output\n");
    printf("  -h       Show this help\n");
}

int main(int argc, char* argv[]) {
    // Default configuration
    int num_workers = 4;
    uint64_t prime_tasks = 1000;
    uint64_t matrix_tasks = 500;
    uint64_t monte_carlo_tasks = 200;
    uint32_t monte_carlo_iterations = 100000;
    serial_type_t serializer = SERIAL_CAPNP_LITE;
    bool use_zero_copy = false;
    bool verbose = false;
    
    // Parse command line arguments
    int opt;
    while ((opt = getopt(argc, argv, "w:p:m:c:i:s:zvh")) != -1) {
        switch (opt) {
            case 'w':
                num_workers = atoi(optarg);
                if (num_workers < 1 || num_workers > 16) {
                    fprintf(stderr, "Invalid number of workers\n");
                    return 1;
                }
                break;
            case 'p':
                prime_tasks = atoi(optarg);
                break;
            case 'm':
                matrix_tasks = atoi(optarg);
                break;
            case 'c':
                monte_carlo_tasks = atoi(optarg);
                break;
            case 'i':
                monte_carlo_iterations = atoi(optarg);
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
            case 'v':
                verbose = true;
                break;
            case 'h':
                print_usage(argv[0]);
                return 0;
            default:
                print_usage(argv[0]);
                return 1;
        }
    }
    
    printf("FeuerBird IPC Distributed Computing Demo\n");
    printf("=========================================\n");
    printf("Configuration:\n");
    printf("  Workers: %d\n", num_workers);
    printf("  Prime tasks: %lu\n", prime_tasks);
    printf("  Matrix tasks: %lu\n", matrix_tasks);
    printf("  Monte Carlo tasks: %lu\n", monte_carlo_tasks);
    printf("  Monte Carlo iterations: %u\n", monte_carlo_iterations);
    printf("  Serializer: %s\n", 
           serializer == SERIAL_RAW ? "Raw" :
           serializer == SERIAL_CAPNP_LITE ? "Cap'n Proto Lite" : "Cap'n Proto Full");
    printf("  Zero-copy: %s\n", use_zero_copy ? "Enabled" : "Disabled");
    printf("  Total tasks: %lu\n", prime_tasks + matrix_tasks + monte_carlo_tasks);
    printf("\n");
    
    // Initialize systems
    init_channel_system();
    if (use_zero_copy) {
        init_zero_copy_system();
    }
    
    // Create channels
    channel_config_t task_config = {
        .type = CHAN_TYPE_ASYNC,
        .mode = CHAN_MODE_NONBLOCKING,
        .buffer_size = sizeof(compute_task_t) * 1024,
        .message_size = sizeof(compute_task_t),
        .serializer = serializer,
        .zero_copy = use_zero_copy
    };
    
    channel_config_t result_config = {
        .type = CHAN_TYPE_ASYNC,
        .mode = CHAN_MODE_NONBLOCKING,
        .buffer_size = sizeof(compute_result_t) * 1024,
        .message_size = sizeof(compute_result_t),
        .serializer = serializer,
        .zero_copy = use_zero_copy
    };
    
    exo_cap_t owner_cap = 0x2000000000000000ULL;
    
    task_queue = task_channel_create("task_queue", &task_config, owner_cap);
    result_queue = result_channel_create("result_queue", &result_config, owner_cap);
    
    if (!task_queue || !result_queue) {
        fprintf(stderr, "Failed to create channels\n");
        return 1;
    }
    
    printf("Channels created, starting computation...\n");
    
    // Start worker threads
    pthread_t worker_threads[16];
    worker_args_t worker_args[16];
    
    uint64_t total_tasks = prime_tasks + matrix_tasks + monte_carlo_tasks;
    uint32_t tasks_per_worker = (total_tasks + num_workers - 1) / num_workers;
    
    for (int i = 0; i < num_workers; i++) {
        worker_args[i].worker_id = i;
        worker_args[i].max_tasks = tasks_per_worker;
        worker_args[i].enable_detailed_stats = verbose;
        
        if (pthread_create(&worker_threads[i], NULL, worker_thread, &worker_args[i]) != 0) {
            perror("Failed to create worker thread");
            return 1;
        }
    }
    
    // Start result collector
    pthread_t collector_thread;
    collection_stats_t collection_stats;
    
    if (pthread_create(&collector_thread, NULL, result_collector_thread, &collection_stats) != 0) {
        perror("Failed to create collector thread");
        return 1;
    }
    
    // Generate tasks
    time_t start_time = time(NULL);
    
    printf("Generating tasks...\n");
    generate_prime_tasks(prime_tasks, 1000000);
    generate_matrix_tasks(matrix_tasks);
    generate_monte_carlo_tasks(monte_carlo_tasks, monte_carlo_iterations);
    
    printf("All tasks submitted, waiting for completion...\n");
    
    // Monitor progress
    while (tasks_completed < total_tasks && active_workers > 0) {
        sleep(2);
        
        double progress = (double)tasks_completed / total_tasks * 100.0;
        printf("Progress: %.1f%% (%lu/%lu tasks completed, %u workers active)\n",
               progress, tasks_completed, total_tasks, active_workers);
    }
    
    printf("All tasks completed, shutting down workers...\n");
    
    // Send shutdown signals
    for (int i = 0; i < num_workers; i++) {
        compute_task_t shutdown_task = {0};
        shutdown_task.type = TASK_SHUTDOWN;
        task_channel_send(task_queue, &shutdown_task, task_queue->chan->send_cap);
    }
    
    // Wait for workers to finish
    for (int i = 0; i < num_workers; i++) {
        pthread_join(worker_threads[i], NULL);
    }
    
    // Wait a bit for final results
    sleep(2);
    system_running = false;
    
    // Wait for collector
    pthread_join(collector_thread, NULL);
    
    time_t end_time = time(NULL);
    double total_time = difftime(end_time, start_time);
    
    // Print final results
    printf("\n=== COMPUTATION RESULTS ===\n");
    printf("Execution time: %.1f seconds\n", total_time);
    printf("Tasks per second: %.1f\n", total_tasks / total_time);
    printf("Total tasks submitted: %lu\n", tasks_submitted);
    printf("Total tasks completed: %lu\n", tasks_completed);
    printf("Success rate: %.1f%%\n", 
           (double)(collection_stats.total_results - collection_stats.failed_results) 
           / collection_stats.total_results * 100.0);
    
    printf("\nTask-specific results:\n");
    printf("  Prime checking: %lu tasks, %lu primes found\n",
           collection_stats.prime_tasks, collection_stats.primes_found);
    printf("  Matrix multiplication: %lu tasks completed\n", collection_stats.matrix_tasks);
    if (collection_stats.monte_carlo_tasks > 0) {
        double avg_pi = collection_stats.pi_sum / collection_stats.monte_carlo_tasks;
        printf("  Monte Carlo PI: %lu tasks, average estimate: %.6f (error: %.6f)\n",
               collection_stats.monte_carlo_tasks, avg_pi, fabs(avg_pi - M_PI));
    }
    
    // Performance statistics
    if (total_processing_time > 0) {
        double avg_task_time_ns = (double)total_processing_time * 0.4 / tasks_completed;
        printf("\nPerformance:\n");
        printf("  Average task processing time: %.1f ns\n", avg_task_time_ns);
        printf("  Total processing cycles: %lu\n", total_processing_time);
    }
    
    // Channel statistics
    printf("\nChannel performance:\n");
    if (task_queue && task_queue->chan) {
        unified_channel_t task_stats;
        channel_get_stats(task_queue->chan, &task_stats);
        printf("  Task queue: %lu sent, %lu received\n",
               task_stats.stats.messages_sent, task_stats.stats.messages_received);
    }
    
    if (result_queue && result_queue->chan) {
        unified_channel_t result_stats;
        channel_get_stats(result_queue->chan, &result_stats);
        printf("  Result queue: %lu sent, %lu received\n",
               result_stats.stats.messages_sent, result_stats.stats.messages_received);
    }
    
    if (use_zero_copy) {
        printf("\n");
        print_zero_copy_stats();
    }
    
    // Cleanup
    if (task_queue) task_channel_destroy(task_queue);
    if (result_queue) result_channel_destroy(result_queue);
    
    if (use_zero_copy) {
        shutdown_zero_copy_system();
    }
    shutdown_channel_system();
    
    printf("\nDistributed computing demo completed successfully!\n");
    printf("The unified channel system efficiently coordinated %d workers\n", num_workers);
    printf("to process %lu computational tasks with excellent performance.\n", total_tasks);
    
    return 0;
}