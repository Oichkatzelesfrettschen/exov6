/**
 * @file bench_dag.c
 * @brief Performance benchmarks for DAG lock ordering system
 *
 * Measures overhead of DAG validation at various granularities:
 * - Pure validation latency
 * - Acquisition overhead (with vs without DAG)
 * - Stack tracking overhead
 * - Release overhead
 * - Deep chain performance
 * - Concurrent validation scalability
 *
 * Target: < 20 cycles overhead for typical 2-3 lock depth
 *
 * @version 1.0
 * @date 2025-11-17
 */

#define _GNU_SOURCE
#define _POSIX_C_SOURCE 200809L

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <pthread.h>
#include <assert.h>
#include <stdatomic.h>
#include <time.h>

/* ========================================================================
 * Benchmark Configuration
 * ======================================================================== */

#define ITERATIONS       1000000    // Iterations per benchmark
#define WARMUP_ITERS     10000      // Warmup iterations
#define MAX_HELD_LOCKS   16
#define LOCK_LEVEL_MAX   100

/* Thread configuration for concurrent benchmarks */
#define NUM_THREADS      4

/* ========================================================================
 * Mock Types and Structures (Same as test_dag.c)
 * ======================================================================== */

#define LOCK_TYPE_QSPIN    1
#define LOCK_TYPE_ADAPTIVE 2
#define LOCK_TYPE_TOKEN    3

#define LOCK_LEVEL_SCHEDULER    10
#define LOCK_LEVEL_MEMORY       20
#define LOCK_LEVEL_PROCESS      30
#define LOCK_LEVEL_FILESYSTEM   40

struct lock_acquisition {
    void *lock_addr;
    const char *lock_name;
    uint32_t dag_level;
    uint32_t lock_type;
    uint64_t acquire_tsc;
    const char *file;
    int line;
};

struct thread_lock_tracker {
    struct lock_acquisition stack[MAX_HELD_LOCKS];
    uint32_t depth;
    uint32_t highest_level;
    uint32_t max_depth;
    uint64_t violations;
};

struct dag_stats {
    uint64_t total_acquisitions;
    uint64_t dag_checks;
    uint64_t violations_detected;
    uint64_t max_chain_length;
    uint64_t violations_by_level[LOCK_LEVEL_MAX];
};

struct dag_stats global_dag_stats;
_Thread_local struct thread_lock_tracker current_tracker;

/* ========================================================================
 * TSC Timing Utilities
 * ======================================================================== */

/**
 * Read TSC with serializing instruction
 */
static inline uint64_t rdtsc_begin(void) {
    uint32_t lo, hi;
    __asm__ __volatile__(
        "cpuid\n\t"           // Serialize
        "rdtsc\n\t"
        : "=a"(lo), "=d"(hi)
        :
        : "%rbx", "%rcx");
    return ((uint64_t)hi << 32) | lo;
}

/**
 * Read TSC with serializing instruction (end)
 */
static inline uint64_t rdtsc_end(void) {
    uint32_t lo, hi;
    __asm__ __volatile__(
        "rdtscp\n\t"          // Serialize
        "mov %%edx, %0\n\t"
        "mov %%eax, %1\n\t"
        "cpuid\n\t"
        : "=r"(hi), "=r"(lo)
        :
        : "%rax", "%rbx", "%rcx", "%rdx");
    return ((uint64_t)hi << 32) | lo;
}

/**
 * Simple TSC read (fast, non-serializing)
 */
static inline uint64_t rdtsc(void) {
    uint32_t lo, hi;
    __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
    return ((uint64_t)hi << 32) | lo;
}

/* ========================================================================
 * DAG Implementation (Minimal, Optimized for Benchmarking)
 * ======================================================================== */

struct thread_lock_tracker *get_lock_tracker(void) {
    return &current_tracker;
}

static const char *lock_type_name(uint32_t lock_type) {
    switch (lock_type) {
        case LOCK_TYPE_QSPIN:    return "qspinlock";
        case LOCK_TYPE_ADAPTIVE: return "adaptive_mutex";
        case LOCK_TYPE_TOKEN:    return "lwkt_token";
        default:                 return "unknown";
    }
}

/**
 * DAG validation (benchmark version - no reporting)
 */
int dag_validate_acquisition(void *lock_addr, const char *name,
                             uint32_t dag_level, uint32_t lock_type,
                             const char *file, int line) {
    (void)name;  // Unused in benchmark version
    (void)file;  // Unused in benchmark version
    (void)line;  // Unused in benchmark version

    struct thread_lock_tracker *tracker = get_lock_tracker();

    if (!tracker) {
        return 1;
    }

    __sync_fetch_and_add(&global_dag_stats.dag_checks, 1);

    // Check reacquisition
    for (uint32_t i = 0; i < tracker->depth; i++) {
        if (tracker->stack[i].lock_addr == lock_addr) {
            if (lock_type == LOCK_TYPE_TOKEN) {
                return 1;  // Tokens allow reacquisition
            }
            return 0;  // Error
        }
    }

    // Check DAG ordering
    for (uint32_t i = 0; i < tracker->depth; i++) {
        if (dag_level <= tracker->stack[i].dag_level) {
            __sync_fetch_and_add(&global_dag_stats.violations_detected, 1);
            tracker->violations++;
            return 0;
        }
    }

    return 1;
}

/**
 * Track lock acquisition (benchmark version)
 */
void dag_lock_acquired(void *lock_addr, const char *name,
                      uint32_t dag_level, uint32_t lock_type,
                      const char *file, int line) {
    struct thread_lock_tracker *tracker = get_lock_tracker();

    if (!tracker || tracker->depth >= MAX_HELD_LOCKS) {
        return;
    }

    struct lock_acquisition *acq = &tracker->stack[tracker->depth];
    acq->lock_addr = lock_addr;
    acq->lock_name = name;
    acq->dag_level = dag_level;
    acq->lock_type = lock_type;
    acq->acquire_tsc = rdtsc();
    acq->file = file;
    acq->line = line;

    tracker->depth++;

    if (tracker->depth > tracker->max_depth) {
        tracker->max_depth = tracker->depth;

        uint64_t old_max = global_dag_stats.max_chain_length;
        while (tracker->depth > old_max) {
            if (__sync_bool_compare_and_swap(&global_dag_stats.max_chain_length,
                                             old_max, tracker->depth)) {
                break;
            }
            old_max = global_dag_stats.max_chain_length;
        }
    }

    if (dag_level > tracker->highest_level) {
        tracker->highest_level = dag_level;
    }

    __sync_fetch_and_add(&global_dag_stats.total_acquisitions, 1);
}

/**
 * Track lock release (benchmark version)
 */
void dag_lock_released(void *lock_addr) {
    struct thread_lock_tracker *tracker = get_lock_tracker();

    if (!tracker || tracker->depth == 0) {
        return;
    }

    // Find and remove lock
    for (int i = tracker->depth - 1; i >= 0; i--) {
        if (tracker->stack[i].lock_addr == lock_addr) {
            // Shift stack down
            for (uint32_t j = i; j < tracker->depth - 1; j++) {
                tracker->stack[j] = tracker->stack[j + 1];
            }

            tracker->depth--;

            // Recalculate highest level
            tracker->highest_level = 0;
            for (uint32_t j = 0; j < tracker->depth; j++) {
                if (tracker->stack[j].dag_level > tracker->highest_level) {
                    tracker->highest_level = tracker->stack[j].dag_level;
                }
            }

            return;
        }
    }
}

void dag_reset_stats(void) {
    memset(&global_dag_stats, 0, sizeof(global_dag_stats));
}

/* ========================================================================
 * Benchmark Utilities
 * ======================================================================== */

/**
 * Calculate statistics for latency measurements
 */
struct bench_stats {
    uint64_t min;
    uint64_t max;
    uint64_t median;
    double mean;
    double stddev;
    uint64_t p50;
    uint64_t p95;
    uint64_t p99;
};

int compare_uint64(const void *a, const void *b) {
    uint64_t ua = *(const uint64_t *)a;
    uint64_t ub = *(const uint64_t *)b;
    if (ua < ub) return -1;
    if (ua > ub) return 1;
    return 0;
}

void calculate_stats(uint64_t *samples, size_t n, struct bench_stats *stats) {
    // Sort for percentiles
    qsort(samples, n, sizeof(uint64_t), compare_uint64);

    stats->min = samples[0];
    stats->max = samples[n - 1];
    stats->median = samples[n / 2];
    stats->p50 = samples[n / 2];
    stats->p95 = samples[(size_t)(n * 0.95)];
    stats->p99 = samples[(size_t)(n * 0.99)];

    // Calculate mean
    double sum = 0.0;
    for (size_t i = 0; i < n; i++) {
        sum += samples[i];
    }
    stats->mean = sum / n;

    // Calculate standard deviation
    double var_sum = 0.0;
    for (size_t i = 0; i < n; i++) {
        double diff = samples[i] - stats->mean;
        var_sum += diff * diff;
    }
    stats->stddev = sqrt(var_sum / n);
}

void print_stats(const char *name, struct bench_stats *stats) {
    printf("\n%s:\n", name);
    printf("  Min:      %5lu cycles\n", stats->min);
    printf("  Median:   %5lu cycles\n", stats->median);
    printf("  Mean:     %5.1f cycles\n", stats->mean);
    printf("  P95:      %5lu cycles\n", stats->p95);
    printf("  P99:      %5lu cycles\n", stats->p99);
    printf("  Max:      %5lu cycles\n", stats->max);
    printf("  Std Dev:  %5.1f cycles\n", stats->stddev);
}

/* ========================================================================
 * Benchmark 1: Pure DAG Validation Overhead
 * ======================================================================== */

void bench_validation_overhead(void) {
    printf("\n=== Benchmark 1: Pure Validation Overhead ===\n");

    uint64_t *samples = malloc(ITERATIONS * sizeof(uint64_t));
    int lock1, lock2, lock3;

    // Setup: Pre-acquire 2 locks to simulate typical state
    memset(&current_tracker, 0, sizeof(current_tracker));
    dag_lock_acquired(&lock1, "lock1", 10, LOCK_TYPE_QSPIN, __FILE__, __LINE__);
    dag_lock_acquired(&lock2, "lock2", 20, LOCK_TYPE_QSPIN, __FILE__, __LINE__);

    // Warmup
    for (int i = 0; i < WARMUP_ITERS; i++) {
        dag_validate_acquisition(&lock3, "lock3", 30, LOCK_TYPE_QSPIN,
                                __FILE__, __LINE__);
    }

    // Benchmark: Just validation, no acquisition
    for (int i = 0; i < ITERATIONS; i++) {
        uint64_t start = rdtsc_begin();
        dag_validate_acquisition(&lock3, "lock3", 30, LOCK_TYPE_QSPIN,
                                __FILE__, __LINE__);
        uint64_t end = rdtsc_end();
        samples[i] = end - start;
    }

    struct bench_stats stats;
    calculate_stats(samples, ITERATIONS, &stats);
    print_stats("Validation (depth=2, valid acquisition)", &stats);

    printf("\n  Target: < 20 cycles\n");
    if (stats.median <= 20) {
        printf("  ✓ PASS: Median %lu cycles <= 20 cycles\n", stats.median);
    } else {
        printf("  ✗ FAIL: Median %lu cycles > 20 cycles\n", stats.median);
    }

    free(samples);
}

/* ========================================================================
 * Benchmark 2: Acquisition Tracking Overhead
 * ======================================================================== */

void bench_acquisition_overhead(void) {
    printf("\n=== Benchmark 2: Acquisition Tracking Overhead ===\n");

    uint64_t *samples = malloc(ITERATIONS * sizeof(uint64_t));
    int locks[ITERATIONS];

    // Warmup
    for (int i = 0; i < WARMUP_ITERS; i++) {
        dag_lock_acquired(&locks[i], "lock", 10, LOCK_TYPE_QSPIN, __FILE__, __LINE__);
        dag_lock_released(&locks[i]);
    }

    // Benchmark: dag_lock_acquired
    memset(&current_tracker, 0, sizeof(current_tracker));
    for (int i = 0; i < ITERATIONS; i++) {
        uint64_t start = rdtsc_begin();
        dag_lock_acquired(&locks[i], "lock", 10, LOCK_TYPE_QSPIN, __FILE__, __LINE__);
        uint64_t end = rdtsc_end();
        samples[i] = end - start;

        // Release to prevent overflow
        dag_lock_released(&locks[i]);
    }

    struct bench_stats stats;
    calculate_stats(samples, ITERATIONS, &stats);
    print_stats("dag_lock_acquired() latency", &stats);

    printf("\n  Target: < 20 cycles\n");
    if (stats.median <= 20) {
        printf("  ✓ PASS: Median %lu cycles <= 20 cycles\n", stats.median);
    } else {
        printf("  ✗ FAIL: Median %lu cycles > 20 cycles\n", stats.median);
    }

    free(samples);
}

/* ========================================================================
 * Benchmark 3: Release Overhead
 * ======================================================================== */

void bench_release_overhead(void) {
    printf("\n=== Benchmark 3: Release Overhead ===\n");

    uint64_t *samples_lifo = malloc(ITERATIONS * sizeof(uint64_t));
    uint64_t *samples_recalc = malloc(ITERATIONS * sizeof(uint64_t));

    // Benchmark LIFO release (no recalculation needed)
    memset(&current_tracker, 0, sizeof(current_tracker));
    for (int i = 0; i < WARMUP_ITERS; i++) {
        int lock;
        dag_lock_acquired(&lock, "lock", 10, LOCK_TYPE_QSPIN, __FILE__, __LINE__);
        dag_lock_released(&lock);
    }

    for (int i = 0; i < ITERATIONS; i++) {
        int lock;
        dag_lock_acquired(&lock, "lock", 10, LOCK_TYPE_QSPIN, __FILE__, __LINE__);

        uint64_t start = rdtsc_begin();
        dag_lock_released(&lock);
        uint64_t end = rdtsc_end();
        samples_lifo[i] = end - start;
    }

    // Benchmark worst-case release (recalculation needed)
    memset(&current_tracker, 0, sizeof(current_tracker));
    for (int i = 0; i < ITERATIONS; i++) {
        int lock1, lock2, lock3;

        // Acquire 3 locks
        dag_lock_acquired(&lock1, "lock1", 10, LOCK_TYPE_QSPIN, __FILE__, __LINE__);
        dag_lock_acquired(&lock2, "lock2", 20, LOCK_TYPE_QSPIN, __FILE__, __LINE__);
        dag_lock_acquired(&lock3, "lock3", 30, LOCK_TYPE_QSPIN, __FILE__, __LINE__);

        // Release middle one (triggers recalculation)
        uint64_t start = rdtsc_begin();
        dag_lock_released(&lock2);
        uint64_t end = rdtsc_end();
        samples_recalc[i] = end - start;

        // Clean up
        dag_lock_released(&lock3);
        dag_lock_released(&lock1);
    }

    struct bench_stats stats_lifo, stats_recalc;
    calculate_stats(samples_lifo, ITERATIONS, &stats_lifo);
    calculate_stats(samples_recalc, ITERATIONS, &stats_recalc);

    print_stats("LIFO release (depth=1, no recalc)", &stats_lifo);
    print_stats("Non-LIFO release (depth=3, recalc)", &stats_recalc);

    printf("\n  Recalculation overhead: %.1f cycles\n",
           stats_recalc.mean - stats_lifo.mean);

    free(samples_lifo);
    free(samples_recalc);
}

/* ========================================================================
 * Benchmark 4: Deep Chain Performance
 * ======================================================================== */

void bench_deep_chain(void) {
    printf("\n=== Benchmark 4: Deep Chain Performance ===\n");

    int depths[] = {1, 2, 4, 8, 12, 16};
    int num_depths = sizeof(depths) / sizeof(depths[0]);

    printf("\n  Validation latency vs chain depth:\n\n");
    printf("  Depth  |  Min  | Median |  Mean  |  P95   |  P99   |  Max\n");
    printf("  -------+-------+--------+--------+--------+--------+-------\n");

    for (int d = 0; d < num_depths; d++) {
        int depth = depths[d];
        uint64_t *samples = malloc(ITERATIONS * sizeof(uint64_t));
        int locks[16];

        for (int i = 0; i < ITERATIONS; i++) {
            memset(&current_tracker, 0, sizeof(current_tracker));

            // Acquire 'depth' locks
            for (int j = 0; j < depth; j++) {
                dag_lock_acquired(&locks[j], "lock", 10 + j * 10, LOCK_TYPE_QSPIN,
                                 __FILE__, __LINE__);
            }

            // Measure validation at next level
            int test_lock;
            uint64_t start = rdtsc_begin();
            dag_validate_acquisition(&test_lock, "test_lock",
                                    10 + depth * 10, LOCK_TYPE_QSPIN,
                                    __FILE__, __LINE__);
            uint64_t end = rdtsc_end();
            samples[i] = end - start;
        }

        struct bench_stats stats;
        calculate_stats(samples, ITERATIONS, &stats);

        printf("  %5d  | %5lu | %6lu | %6.1f | %6lu | %6lu | %6lu\n",
               depth, stats.min, stats.median, stats.mean,
               stats.p95, stats.p99, stats.max);

        free(samples);
    }

    printf("\n  Expected: O(depth) linear scaling\n");
}

/* ========================================================================
 * Benchmark 5: Full Acquire-Release Cycle
 * ======================================================================== */

void bench_full_cycle(void) {
    printf("\n=== Benchmark 5: Full Acquire-Release Cycle ===\n");

    uint64_t *samples_with_dag = malloc(ITERATIONS * sizeof(uint64_t));
    uint64_t *samples_no_dag = malloc(ITERATIONS * sizeof(uint64_t));
    int locks[ITERATIONS];

    // Warmup
    memset(&current_tracker, 0, sizeof(current_tracker));
    for (int i = 0; i < WARMUP_ITERS; i++) {
        dag_validate_acquisition(&locks[i], "lock", 10, LOCK_TYPE_QSPIN,
                                __FILE__, __LINE__);
        dag_lock_acquired(&locks[i], "lock", 10, LOCK_TYPE_QSPIN,
                         __FILE__, __LINE__);
        dag_lock_released(&locks[i]);
    }

    // Benchmark WITH DAG
    memset(&current_tracker, 0, sizeof(current_tracker));
    for (int i = 0; i < ITERATIONS; i++) {
        uint64_t start = rdtsc_begin();
        dag_validate_acquisition(&locks[i], "lock", 10, LOCK_TYPE_QSPIN,
                                __FILE__, __LINE__);
        dag_lock_acquired(&locks[i], "lock", 10, LOCK_TYPE_QSPIN,
                         __FILE__, __LINE__);
        dag_lock_released(&locks[i]);
        uint64_t end = rdtsc_end();
        samples_with_dag[i] = end - start;
    }

    // Benchmark WITHOUT DAG (just rdtsc overhead)
    for (int i = 0; i < ITERATIONS; i++) {
        uint64_t start = rdtsc_begin();
        // Empty critical section
        __asm__ __volatile__("" ::: "memory");
        uint64_t end = rdtsc_end();
        samples_no_dag[i] = end - start;
    }

    struct bench_stats stats_with, stats_without;
    calculate_stats(samples_with_dag, ITERATIONS, &stats_with);
    calculate_stats(samples_no_dag, ITERATIONS, &stats_without);

    print_stats("Full cycle WITH DAG", &stats_with);
    print_stats("Baseline (measurement overhead)", &stats_without);

    printf("\n  Net DAG overhead: %.1f cycles\n",
           stats_with.mean - stats_without.mean);
    printf("  Target: < 30 cycles\n");

    double overhead = stats_with.mean - stats_without.mean;
    if (overhead <= 30.0) {
        printf("  ✓ PASS: Overhead %.1f cycles <= 30 cycles\n", overhead);
    } else {
        printf("  ✗ FAIL: Overhead %.1f cycles > 30 cycles\n", overhead);
    }

    free(samples_with_dag);
    free(samples_no_dag);
}

/* ========================================================================
 * Benchmark 6: Concurrent Validation Scalability
 * ======================================================================== */

struct thread_bench_args {
    int thread_id;
    uint64_t *samples;
    pthread_barrier_t *barrier;
};

void *concurrent_worker(void *arg) {
    struct thread_bench_args *args = (struct thread_bench_args *)arg;
    int locks[5];

    // Warmup
    for (int i = 0; i < WARMUP_ITERS / NUM_THREADS; i++) {
        for (int j = 0; j < 5; j++) {
            dag_validate_acquisition(&locks[j], "lock", 10 + j * 10,
                                    LOCK_TYPE_QSPIN, __FILE__, __LINE__);
            dag_lock_acquired(&locks[j], "lock", 10 + j * 10,
                            LOCK_TYPE_QSPIN, __FILE__, __LINE__);
        }
        for (int j = 4; j >= 0; j--) {
            dag_lock_released(&locks[j]);
        }
    }

    // Synchronize
    pthread_barrier_wait(args->barrier);

    // Benchmark
    for (int i = 0; i < ITERATIONS / NUM_THREADS; i++) {
        uint64_t start = rdtsc_begin();

        for (int j = 0; j < 5; j++) {
            dag_validate_acquisition(&locks[j], "lock", 10 + j * 10,
                                    LOCK_TYPE_QSPIN, __FILE__, __LINE__);
            dag_lock_acquired(&locks[j], "lock", 10 + j * 10,
                            LOCK_TYPE_QSPIN, __FILE__, __LINE__);
        }

        for (int j = 4; j >= 0; j--) {
            dag_lock_released(&locks[j]);
        }

        uint64_t end = rdtsc_end();
        args->samples[i] = (end - start) / 5;  // Per-lock average
    }

    return NULL;
}

void bench_concurrent_scalability(void) {
    printf("\n=== Benchmark 6: Concurrent Validation ===\n");

    pthread_t threads[NUM_THREADS];
    struct thread_bench_args args[NUM_THREADS];
    pthread_barrier_t barrier;

    pthread_barrier_init(&barrier, NULL, NUM_THREADS);

    // Allocate per-thread sample arrays
    for (int i = 0; i < NUM_THREADS; i++) {
        args[i].thread_id = i;
        args[i].samples = malloc((ITERATIONS / NUM_THREADS) * sizeof(uint64_t));
        args[i].barrier = &barrier;
    }

    // Create threads
    dag_reset_stats();
    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_create(&threads[i], NULL, concurrent_worker, &args[i]);
    }

    // Wait for completion
    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_join(threads[i], NULL);
    }

    // Aggregate results
    uint64_t *all_samples = malloc(ITERATIONS * sizeof(uint64_t));
    for (int i = 0; i < NUM_THREADS; i++) {
        memcpy(all_samples + i * (ITERATIONS / NUM_THREADS),
               args[i].samples,
               (ITERATIONS / NUM_THREADS) * sizeof(uint64_t));
        free(args[i].samples);
    }

    struct bench_stats stats;
    calculate_stats(all_samples, ITERATIONS, &stats);
    print_stats("Concurrent validation (4 threads, per-lock)", &stats);

    printf("\n  Total DAG checks: %lu\n", global_dag_stats.dag_checks);
    printf("  Total acquisitions: %lu\n", global_dag_stats.total_acquisitions);
    printf("  Violations: %lu\n", global_dag_stats.violations_detected);

    free(all_samples);
    pthread_barrier_destroy(&barrier);
}

/* ========================================================================
 * Main Benchmark Runner
 * ======================================================================== */

int main(void) {
    printf("========================================\n");
    printf("DAG Lock Ordering Performance Benchmarks\n");
    printf("========================================\n");
    printf("Iterations: %d\n", ITERATIONS);
    printf("Warmup:     %d\n", WARMUP_ITERS);
    printf("Threads:    %d\n", NUM_THREADS);

    // Run all benchmarks
    bench_validation_overhead();
    bench_acquisition_overhead();
    bench_release_overhead();
    bench_deep_chain();
    bench_full_cycle();
    bench_concurrent_scalability();

    printf("\n========================================\n");
    printf("Benchmark Summary\n");
    printf("========================================\n");
    printf("All benchmarks completed successfully.\n");
    printf("Review results above for performance analysis.\n");

    return 0;
}
