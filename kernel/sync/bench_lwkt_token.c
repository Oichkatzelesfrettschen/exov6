/**
 * @file bench_lwkt_token.c
 * @brief Microbenchmarks for LWKT token implementation
 *
 * Benchmarks cover:
 * 1. Uncontended latency (acquire/release cycles)
 * 2. Reacquisition performance (fast path effectiveness)
 * 3. Pool lookup overhead (hash distribution)
 * 4. 2-CPU contention (moderate contention)
 * 5. 4-CPU contention (high contention)
 * 6. Release-all batch performance
 *
 * @version 1.0
 * @date 2025-11-17
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdarg.h>
#include <string.h>
#include <pthread.h>
#include <unistd.h>
#include <sched.h>
#include <sys/time.h>

/* ========================================================================
 * Atomic Type Compatibility
 * ======================================================================== */

#define _Atomic(T) T

#define atomic_store_explicit(obj, val, order) __atomic_store_n(obj, val, order)
#define atomic_load_explicit(obj, order) __atomic_load_n(obj, order)
#define atomic_compare_exchange_strong_explicit(obj, expected, desired, succ, fail) \
    __atomic_compare_exchange_n(obj, expected, desired, 0, succ, fail)
#define atomic_fetch_add_explicit(obj, val, order) __atomic_fetch_add(obj, val, order)
#define atomic_fetch_sub_explicit(obj, val, order) __atomic_fetch_sub(obj, val, order)

#define memory_order_relaxed __ATOMIC_RELAXED
#define memory_order_acquire __ATOMIC_ACQUIRE
#define memory_order_release __ATOMIC_RELEASE
#define memory_order_seq_cst __ATOMIC_SEQ_CST

/* ========================================================================
 * Kernel Compatibility Layer
 * ======================================================================== */

struct cpu {
    int id;
    void *proc;
};

#define NCPU 8

struct cpu cpus[NCPU];

__thread struct cpu *current_cpu = NULL;

static inline struct cpu *mycpu(void) {
    if (!current_cpu) {
        int cpu_id = sched_getcpu();
        if (cpu_id < 0 || cpu_id >= NCPU) cpu_id = 0;
        current_cpu = &cpus[cpu_id];
    }
    return current_cpu;
}

static void panic(const char *fmt, ...) {
    va_list args;
    va_start(args, fmt);
    fprintf(stderr, "PANIC: ");
    vfprintf(stderr, fmt, args);
    fprintf(stderr, "\n");
    va_end(args);
    exit(1);
}

static void cprintf(const char *fmt, ...) {
    va_list args;
    va_start(args, fmt);
    vprintf(fmt, args);
    va_end(args);
}

/* ========================================================================
 * LWKT Token Definitions
 * ======================================================================== */

#define TOKEN_POOL_SIZE 256
#define MAX_TOKENS_PER_CPU 16
#define TOKEN_FREE_MARKER NCPU

#define likely(x)       __builtin_expect(!!(x), 1)
#define unlikely(x)     __builtin_expect(!!(x), 0)
#define EXO_ALWAYS_INLINE __attribute__((always_inline)) inline

struct cpu_token_list {
    struct lwkt_token *tokens[MAX_TOKENS_PER_CPU];
    uint32_t count;
} __attribute__((aligned(64)));

struct lwkt_token_stats {
    uint64_t acquire_count;
    uint64_t release_count;
    uint64_t contention_count;
    uint64_t total_hold_cycles;
    uint64_t max_hold_cycles;
    uint64_t reacquire_count;
    uint64_t cpu_acquire_count[NCPU];
} __attribute__((aligned(128)));

struct lwkt_token {
    _Atomic uint32_t owner_cpu;
    uint32_t hash;
    const char *name;
    uint32_t dag_level;
    uint64_t acquire_tsc;
    struct lwkt_token_stats stats;
} __attribute__((aligned(256)));

/* Global token pool */
struct lwkt_token token_pool[TOKEN_POOL_SIZE];
struct cpu_token_list cpu_tokens[NCPU];

/* Token API declarations */
void token_pool_init(void);
void token_init(struct lwkt_token *token, const char *name, uint32_t dag_level);
void token_acquire(struct lwkt_token *token);
void token_release(struct lwkt_token *token);
void token_release_all(void);
struct lwkt_token *token_pool_get(void *resource);
int token_holding(struct lwkt_token *token);

/* ========================================================================
 * LWKT Token Implementation (embedded)
 * ======================================================================== */

static inline uint64_t rdtsc(void) {
    uint32_t lo, hi;
    __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
    return ((uint64_t)hi << 32) | lo;
}

static inline void cpu_pause(void) {
    __asm__ __volatile__("pause" ::: "memory");
}

static EXO_ALWAYS_INLINE uint32_t hash_ptr(void *ptr) {
    uintptr_t val = (uintptr_t)ptr;
    val = (val >> 6) ^ (val >> 12) ^ (val >> 18) ^ (val >> 24);
    return val & (TOKEN_POOL_SIZE - 1);
}

static void cpu_token_add(uint32_t cpu, struct lwkt_token *token) {
    struct cpu_token_list *list = &cpu_tokens[cpu];
    if (unlikely(list->count >= MAX_TOKENS_PER_CPU)) {
        panic("cpu_token_add: too many tokens (max %d)", MAX_TOKENS_PER_CPU);
    }
    list->tokens[list->count++] = token;
}

static void cpu_token_remove(uint32_t cpu, struct lwkt_token *token) {
    struct cpu_token_list *list = &cpu_tokens[cpu];
    for (uint32_t i = 0; i < list->count; i++) {
        if (list->tokens[i] == token) {
            for (uint32_t j = i; j < list->count - 1; j++) {
                list->tokens[j] = list->tokens[j + 1];
            }
            list->count--;
            return;
        }
    }
    panic("cpu_token_remove: token not found");
}

void token_pool_init(void) {
    for (int i = 0; i < TOKEN_POOL_SIZE; i++) {
        token_init(&token_pool[i], "pool_token", 0);
        token_pool[i].hash = i;
    }
    for (int i = 0; i < NCPU; i++) {
        cpu_tokens[i].count = 0;
        for (int j = 0; j < MAX_TOKENS_PER_CPU; j++) {
            cpu_tokens[i].tokens[j] = NULL;
        }
    }
}

struct lwkt_token *token_pool_get(void *resource) {
    if (!resource) panic("token_pool_get: NULL resource");
    uint32_t hash = hash_ptr(resource);
    return &token_pool[hash];
}

void token_init(struct lwkt_token *token, const char *name, uint32_t dag_level) {
    atomic_store_explicit(&token->owner_cpu, TOKEN_FREE_MARKER, memory_order_relaxed);
    token->hash = hash_ptr(token);
    token->name = name;
    token->dag_level = dag_level;
    token->dag_level = dag_level;
    token->acquire_tsc = 0;
    memset(&token->stats, 0, sizeof(token->stats));
}

void token_acquire(struct lwkt_token *token) {
    uint32_t my_cpu = mycpu() - cpus;

    uint32_t owner = atomic_load_explicit(&token->owner_cpu, memory_order_relaxed);
    if (likely(owner == my_cpu)) {
        __sync_fetch_and_add(&token->stats.reacquire_count, 1);
        return;
    }

    int backoff = 10;
    int contended = 0;

    while (1) {
        uint32_t expected = TOKEN_FREE_MARKER;

        if (atomic_compare_exchange_strong_explicit(
                &token->owner_cpu, &expected, my_cpu,
                memory_order_acquire, memory_order_relaxed)) {
            token->acquire_tsc = rdtsc();
            __sync_fetch_and_add(&token->stats.acquire_count, 1);
            __sync_fetch_and_add(&token->stats.cpu_acquire_count[my_cpu], 1);

            if (contended) {
                __sync_fetch_and_add(&token->stats.contention_count, 1);
            }

            cpu_token_add(my_cpu, token);
            return;
        }

        contended = 1;

        for (int i = 0; i < backoff; i++) {
            cpu_pause();
        }

        backoff = (backoff < 1000) ? backoff * 2 : 1000;

        if (atomic_load_explicit(&token->owner_cpu, memory_order_relaxed) == TOKEN_FREE_MARKER) {
            continue;
        }
    }
}

void token_release(struct lwkt_token *token) {
    uint32_t my_cpu = mycpu() - cpus;
    uint32_t owner = atomic_load_explicit(&token->owner_cpu, memory_order_relaxed);

    if (unlikely(owner != my_cpu)) {
        panic("token_release: not owner (owner=%u, my_cpu=%u)", owner, my_cpu);
    }

    uint64_t hold_cycles = rdtsc() - token->acquire_tsc;

    __sync_fetch_and_add(&token->stats.release_count, 1);
    __sync_fetch_and_add(&token->stats.total_hold_cycles, hold_cycles);

    uint64_t old_max = token->stats.max_hold_cycles;
    while (hold_cycles > old_max) {
        if (__sync_bool_compare_and_swap(&token->stats.max_hold_cycles,
                                         old_max, hold_cycles)) {
            break;
        }
        old_max = token->stats.max_hold_cycles;
    }

    cpu_token_remove(my_cpu, token);
    atomic_store_explicit(&token->owner_cpu, TOKEN_FREE_MARKER, memory_order_release);
}

void token_release_all(void) {
    uint32_t my_cpu = mycpu() - cpus;
    struct cpu_token_list *list = &cpu_tokens[my_cpu];

    for (uint32_t i = 0; i < list->count; i++) {
        struct lwkt_token *token = list->tokens[i];
        uint64_t hold_cycles = rdtsc() - token->acquire_tsc;

        __sync_fetch_and_add(&token->stats.release_count, 1);
        __sync_fetch_and_add(&token->stats.total_hold_cycles, hold_cycles);

        uint64_t old_max = token->stats.max_hold_cycles;
        while (hold_cycles > old_max) {
            if (__sync_bool_compare_and_swap(&token->stats.max_hold_cycles,
                                             old_max, hold_cycles)) {
                break;
            }
            old_max = token->stats.max_hold_cycles;
        }

        atomic_store_explicit(&token->owner_cpu, TOKEN_FREE_MARKER, memory_order_release);
    }

    list->count = 0;
}

int token_holding(struct lwkt_token *token) {
    uint32_t my_cpu = mycpu() - cpus;
    uint32_t owner = atomic_load_explicit(&token->owner_cpu, memory_order_relaxed);
    return owner == my_cpu;
}

/* ========================================================================
 * Benchmark Infrastructure
 * ======================================================================== */

#define ITERATIONS 1000000

static double get_time_ms(void) {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return tv.tv_sec * 1000.0 + tv.tv_usec / 1000.0;
}

static void print_benchmark_header(const char *name) {
    printf("\n=== %s ===\n", name);
}

static void print_cycles(const char *operation, uint64_t cycles, int iterations) {
    printf("  %s:\n", operation);
    printf("    Total cycles:   %lu\n", cycles);
    printf("    Iterations:     %d\n", iterations);
    printf("    Avg cycles:     %.1f\n", (double)cycles / iterations);
}

/* ========================================================================
 * Benchmark 1: Uncontended Latency
 * ======================================================================== */

static void bench_uncontended_latency(void) {
    print_benchmark_header("Benchmark 1: Uncontended Latency");

    struct lwkt_token token;
    token_init(&token, "bench_token", 0);

    // Warmup
    for (int i = 0; i < 1000; i++) {
        token_acquire(&token);
        token_release(&token);
    }

    // Measure acquire/release latency
    uint64_t total_cycles = 0;

    for (int i = 0; i < ITERATIONS; i++) {
        uint64_t start = rdtsc();
        token_acquire(&token);
        token_release(&token);
        uint64_t end = rdtsc();

        total_cycles += (end - start);
    }

    print_cycles("Acquire + Release", total_cycles, ITERATIONS);
    printf("    Per operation:  %.1f cycles\n", (double)total_cycles / (ITERATIONS * 2));
}

/* ========================================================================
 * Benchmark 2: Reacquisition Performance (Fast Path)
 * ======================================================================== */

static void bench_reacquisition(void) {
    print_benchmark_header("Benchmark 2: Reacquisition Performance");

    struct lwkt_token token;
    token_init(&token, "bench_reacq", 0);

    // First acquisition (slow path)
    uint64_t start = rdtsc();
    token_acquire(&token);
    uint64_t first_acquire = rdtsc() - start;

    // Reacquisitions (fast path)
    uint64_t total_reacq = 0;

    for (int i = 0; i < ITERATIONS; i++) {
        uint64_t reacq_start = rdtsc();
        token_acquire(&token);
        total_reacq += (rdtsc() - reacq_start);
    }

    token_release(&token);

    printf("  First acquisition:   %lu cycles\n", first_acquire);
    print_cycles("Reacquisitions", total_reacq, ITERATIONS);
    printf("  Speedup:             %.1fx\n",
           (double)first_acquire / (total_reacq / ITERATIONS));
}

/* ========================================================================
 * Benchmark 3: Pool Lookup Overhead
 * ======================================================================== */

static void bench_pool_lookup(void) {
    print_benchmark_header("Benchmark 3: Pool Lookup Overhead");

    token_pool_init();

    // Create diverse resource pointers
    void *resources[100];
    for (int i = 0; i < 100; i++) {
        resources[i] = (void *)(uintptr_t)(0x1000 * (i + 1));
    }

    // Measure pool lookup latency
    uint64_t total_cycles = 0;

    for (int i = 0; i < ITERATIONS; i++) {
        uint64_t start = rdtsc();
        struct lwkt_token *token = token_pool_get(resources[i % 100]);
        uint64_t end = rdtsc();

        total_cycles += (end - start);

        // Prevent optimization
        (void)token;
    }

    print_cycles("Pool lookups", total_cycles, ITERATIONS);
}

/* ========================================================================
 * Benchmark 4: 2-CPU Contention
 * ======================================================================== */

static struct lwkt_token contention_token;
static volatile int contention_ready = 0;
static volatile int contention_done = 0;

static void *contention_worker_2(void *arg) {
    int cpu_id = *(int *)arg;

    // Set CPU affinity
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(cpu_id % sysconf(_SC_NPROCESSORS_ONLN), &cpuset);
    pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset);

    current_cpu = &cpus[cpu_id % NCPU];

    // Wait for signal
    while (!contention_ready) {
        cpu_pause();
    }

    // Run benchmark
    for (int i = 0; i < ITERATIONS / 2; i++) {
        token_acquire(&contention_token);
        token_release(&contention_token);
    }

    return NULL;
}

static void bench_2cpu_contention(void) {
    print_benchmark_header("Benchmark 4: 2-CPU Contention");

    token_init(&contention_token, "contention_2", 0);
    contention_ready = 0;
    contention_done = 0;

    pthread_t thread;
    int cpu_id = 1;
    pthread_create(&thread, NULL, contention_worker_2, &cpu_id);

    // Set own affinity
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(0, &cpuset);
    pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset);

    current_cpu = &cpus[0];

    // Start benchmark
    uint64_t start = rdtsc();
    contention_ready = 1;

    for (int i = 0; i < ITERATIONS / 2; i++) {
        token_acquire(&contention_token);
        token_release(&contention_token);
    }

    pthread_join(thread, NULL);
    uint64_t total = rdtsc() - start;

    printf("  Total cycles:       %lu\n", total);
    printf("  Operations:         %d (per thread: %d)\n", ITERATIONS, ITERATIONS/2);
    printf("  Avg per op:         %.1f cycles\n", (double)total / ITERATIONS);
    printf("  Contention events:  %lu\n", contention_token.stats.contention_count);
    printf("  Contention rate:    %.1f%%\n",
           100.0 * contention_token.stats.contention_count / contention_token.stats.acquire_count);
}

/* ========================================================================
 * Benchmark 5: 4-CPU Contention
 * ======================================================================== */

static void *contention_worker_4(void *arg) {
    int cpu_id = *(int *)arg;

    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(cpu_id % sysconf(_SC_NPROCESSORS_ONLN), &cpuset);
    pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset);

    current_cpu = &cpus[cpu_id % NCPU];

    while (!contention_ready) {
        cpu_pause();
    }

    for (int i = 0; i < ITERATIONS / 4; i++) {
        token_acquire(&contention_token);
        token_release(&contention_token);
    }

    return NULL;
}

static void bench_4cpu_contention(void) {
    print_benchmark_header("Benchmark 5: 4-CPU Contention");

    token_init(&contention_token, "contention_4", 0);
    contention_ready = 0;

    const int NUM_THREADS = 4;
    pthread_t threads[NUM_THREADS];
    int cpu_ids[NUM_THREADS];

    for (int i = 0; i < NUM_THREADS; i++) {
        cpu_ids[i] = i;
        pthread_create(&threads[i], NULL, contention_worker_4, &cpu_ids[i]);
    }

    double start_time = get_time_ms();
    contention_ready = 1;

    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_join(threads[i], NULL);
    }

    double elapsed_ms = get_time_ms() - start_time;

    printf("  Total time:         %.2f ms\n", elapsed_ms);
    printf("  Operations:         %d (per thread: %d)\n", ITERATIONS, ITERATIONS/NUM_THREADS);
    printf("  Throughput:         %.0f ops/sec\n", ITERATIONS / (elapsed_ms / 1000.0));
    printf("  Contention events:  %lu\n", contention_token.stats.contention_count);
    printf("  Contention rate:    %.1f%%\n",
           100.0 * contention_token.stats.contention_count / contention_token.stats.acquire_count);
}

/* ========================================================================
 * Benchmark 6: Release-All Batch Performance
 * ======================================================================== */

static void bench_release_all(void) {
    print_benchmark_header("Benchmark 6: Release-All Batch Performance");

    // Test with varying batch sizes
    int batch_sizes[] = {1, 4, 8, 12, 16};

    for (int b = 0; b < 5; b++) {
        int batch_size = batch_sizes[b];
        struct lwkt_token tokens[16];

        for (int i = 0; i < batch_size; i++) {
            char name[32];
            snprintf(name, sizeof(name), "token_%d", i);
            token_init(&tokens[i], name, 0);
        }

        // Warmup
        for (int i = 0; i < 100; i++) {
            for (int j = 0; j < batch_size; j++) {
                token_acquire(&tokens[j]);
            }
            token_release_all();
        }

        // Measure batch release
        uint64_t total_cycles = 0;
        int iterations = 10000;

        for (int i = 0; i < iterations; i++) {
            // Acquire all
            for (int j = 0; j < batch_size; j++) {
                token_acquire(&tokens[j]);
            }

            // Release all (measured)
            uint64_t start = rdtsc();
            token_release_all();
            total_cycles += (rdtsc() - start);
        }

        printf("  Batch size %2d:\n", batch_size);
        printf("    Total cycles:   %lu\n", total_cycles);
        printf("    Iterations:     %d\n", iterations);
        printf("    Avg per batch:  %.1f cycles\n", (double)total_cycles / iterations);
        printf("    Avg per token:  %.1f cycles\n",
               (double)total_cycles / (iterations * batch_size));
    }
}

/* ========================================================================
 * Main Benchmark Runner
 * ======================================================================== */

int main(void) {
    printf("=== LWKT Token Microbenchmarks ===\n");
    printf("Iterations: %d\n", ITERATIONS);

    // Initialize CPU structures
    for (int i = 0; i < NCPU; i++) {
        cpus[i].id = i;
        cpus[i].proc = NULL;
    }

    current_cpu = &cpus[0];

    // Run benchmarks
    bench_uncontended_latency();
    bench_reacquisition();
    bench_pool_lookup();
    bench_2cpu_contention();
    bench_4cpu_contention();
    bench_release_all();

    printf("\n=== Benchmarks Complete ===\n");

    return 0;
}
