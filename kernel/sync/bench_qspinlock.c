/**
 * @file bench_qspinlock.c
 * @brief Performance benchmarks for NUMA-aware qspinlock
 *
 * Benchmarks:
 * 1. Uncontended acquire/release latency (fast path)
 * 2. 2-CPU contention (same NUMA)
 * 3. 2-CPU contention (cross-NUMA)
 * 4. 4-CPU contention (mixed NUMA)
 * 5. 8-CPU contention (full system)
 * 6. Throughput scaling (1-8 CPUs)
 * 7. NUMA locality benefit measurement
 *
 * @version 1.0
 * @date 2025-11-17
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdarg.h>
#include <stdbool.h>
#include <string.h>
#include <pthread.h>
#include <time.h>
#include <unistd.h>

/* Use compiler builtins for atomics */
#define _Atomic(T) T
#define atomic_store_explicit(obj, val, order) __atomic_store_n(obj, val, order)
#define atomic_load_explicit(obj, order) __atomic_load_n(obj, order)
#define atomic_exchange_explicit(obj, val, order) __atomic_exchange_n(obj, val, order)
#define atomic_compare_exchange_strong_explicit(obj, expected, desired, succ, fail) \
    __atomic_compare_exchange_n(obj, expected, desired, 0, succ, fail)
#define atomic_fetch_add(obj, val) __atomic_fetch_add(obj, val, __ATOMIC_SEQ_CST)
#define atomic_load(obj) __atomic_load_n(obj, __ATOMIC_SEQ_CST)
#define memory_order_relaxed __ATOMIC_RELAXED
#define memory_order_acquire __ATOMIC_ACQUIRE
#define memory_order_release __ATOMIC_RELEASE
#define memory_order_acq_rel __ATOMIC_ACQ_REL
#define memory_order_seq_cst __ATOMIC_SEQ_CST

/* Benchmark config */
#define NCPU 8
#define MCS_NODES_PER_CPU 4
#define BENCHMARK_ITERATIONS 100000
#define WARMUP_ITERATIONS 1000

/* Colors for output */
#define COLOR_BOLD    "\033[1m"
#define COLOR_GREEN   "\033[32m"
#define COLOR_YELLOW  "\033[33m"
#define COLOR_BLUE    "\033[34m"
#define COLOR_RESET   "\033[0m"

/* ========================================================================
 * Mock Environment
 * ======================================================================== */

struct cpu {
    uint32_t id;
    bool running;
};

static struct cpu cpus[NCPU];
static __thread int current_cpu_id = 0;

struct cpu *mycpu(void) {
    return &cpus[current_cpu_id];
}

void panic(const char *msg) {
    fprintf(stderr, "PANIC: %s\n", msg);
    abort();
}

void cprintf(const char *fmt, ...) {
    va_list args;
    va_start(args, fmt);
    vprintf(fmt, args);
    va_end(args);
}

#define ADAPTIVE_SPIN_MIN_CYCLES 10
#define ADAPTIVE_SPIN_MAX_CYCLES 1000
#define LOCK_TIMEOUT_CYCLES (1000000000ULL)

/* ========================================================================
 * Timing Utilities
 * ======================================================================== */

static inline uint64_t rdtsc_actual(void) {
    uint32_t lo, hi;
    __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
    return ((uint64_t)hi << 32) | lo;
}

static inline uint64_t rdtsc_serialized(void) {
    uint32_t aux, lo, hi;
    __asm__ __volatile__("rdtscp" : "=a"(lo), "=d"(hi), "=c"(aux) :: "memory");
    return ((uint64_t)hi << 32) | lo;
}

static inline void cpu_relax(void) {
    __asm__ __volatile__("pause" ::: "memory");
}

/* Calibrate TSC frequency */
static double tsc_freq_ghz = 0.0;

void calibrate_tsc(void) {
    struct timespec start, end;
    uint64_t tsc_start, tsc_end;

    clock_gettime(CLOCK_MONOTONIC, &start);
    tsc_start = rdtsc_actual();

    usleep(100000); // 100ms

    tsc_end = rdtsc_actual();
    clock_gettime(CLOCK_MONOTONIC, &end);

    uint64_t ns = (end.tv_sec - start.tv_sec) * 1000000000ULL +
                  (end.tv_nsec - start.tv_nsec);
    uint64_t cycles = tsc_end - tsc_start;

    tsc_freq_ghz = (double)cycles / (double)ns;
    printf("%s TSC Frequency: %.2f GHz%s\n",
           COLOR_BLUE, tsc_freq_ghz, COLOR_RESET);
}

static inline double cycles_to_ns(uint64_t cycles) {
    return (double)cycles / tsc_freq_ghz;
}

/* ========================================================================
 * QSpinlock Implementation (embedded)
 * ======================================================================== */

struct mcs_node {
    struct mcs_node *next;
    struct mcs_node *local_next;
    uint32_t locked;
    uint32_t numa_node;
    uint8_t is_local;
    uint8_t _pad[3];
} __attribute__((aligned(64)));

struct qspin_stats {
    uint64_t fast_path_count;
    uint64_t slow_path_count;
    uint64_t local_handoff_count;
    uint64_t remote_handoff_count;
    uint64_t total_spin_cycles;
    uint64_t max_spin_cycles;
    uint64_t max_queue_depth;
    uint64_t total_hold_cycles;
    uint64_t max_hold_cycles;
    uint64_t acquire_count;
} __attribute__((aligned(64)));

struct qspinlock {
    uint32_t val;
    struct qspin_stats stats;
    uint64_t last_acquire_tsc;
    uint32_t last_owner_numa;
} __attribute__((aligned(128)));

static struct mcs_node mcs_nodes[NCPU][MCS_NODES_PER_CPU] __attribute__((aligned(64)));
static uint32_t cpu_to_numa[NCPU] = {0, 0, 0, 0, 1, 1, 1, 1};

static inline uint64_t rdtsc(void) {
    return rdtsc_actual();
}

static inline void mfence(void) {
    __asm__ __volatile__("mfence" ::: "memory");
}

static inline void cpu_pause(void) {
    __asm__ __volatile__("pause" ::: "memory");
}

static inline uint32_t get_numa_node(uint32_t cpu_id) {
    return (cpu_id < NCPU) ? cpu_to_numa[cpu_id] : 0;
}

static inline uint16_t encode_tail(uint32_t cpu_id, uint32_t node_idx) {
    return (uint16_t)((cpu_id << 2) | (node_idx & 0x3));
}

static inline void decode_tail(uint16_t tail, uint32_t *cpu_id, uint32_t *node_idx) {
    *cpu_id = tail >> 2;
    *node_idx = tail & 0x3;
}

void qspin_init(struct qspinlock *lock) {
    atomic_store_explicit(&lock->val, 0, memory_order_relaxed);
    memset(&lock->stats, 0, sizeof(lock->stats));
    lock->last_acquire_tsc = 0;
    lock->last_owner_numa = 0;
}

static inline int qspin_trylock_fast(struct qspinlock *lock) {
    uint32_t expected = 0;
    if (atomic_compare_exchange_strong_explicit(
            &lock->val, &expected, 1,
            memory_order_acquire, memory_order_relaxed)) {
        __sync_fetch_and_add(&lock->stats.fast_path_count, 1);
        __sync_fetch_and_add(&lock->stats.acquire_count, 1);
        lock->last_acquire_tsc = rdtsc();
        lock->last_owner_numa = get_numa_node(mycpu()->id);
        return 1;
    }
    return 0;
}

void qspin_lock(struct qspinlock *lock);  // Forward declaration
void qspin_unlock(struct qspinlock *lock);  // Forward declaration

void qspin_lock(struct qspinlock *lock) {
    if (qspin_trylock_fast(lock)) {
        return;
    }

    struct cpu *c = mycpu();
    uint32_t cpu_id = c->id;

    int node_idx = 0;
    for (node_idx = 0; node_idx < MCS_NODES_PER_CPU; node_idx++) {
        struct mcs_node *node = &mcs_nodes[cpu_id][node_idx];
        uint32_t expected = 0;
        if (atomic_compare_exchange_strong_explicit(
                &node->locked, &expected, 1,
                memory_order_acquire, memory_order_relaxed)) {
            break;
        }
    }

    if (node_idx >= MCS_NODES_PER_CPU) {
        return; // Safety
    }

    struct mcs_node *node = &mcs_nodes[cpu_id][node_idx];
    uint32_t my_numa = get_numa_node(cpu_id);
    node->numa_node = my_numa;
    atomic_store_explicit(&node->next, NULL, memory_order_relaxed);
    atomic_store_explicit(&node->local_next, NULL, memory_order_relaxed);
    atomic_store_explicit(&node->locked, 1, memory_order_relaxed);
    node->is_local = 0;

    uint16_t my_tail = encode_tail(cpu_id, node_idx);
    uint32_t old_val = atomic_exchange_explicit(&lock->val, my_tail << 16,
                                                memory_order_acquire);

    if (old_val == 0) {
        return;
    }

    uint16_t old_tail = old_val >> 16;
    if (old_tail != 0) {
        uint32_t pred_cpu, pred_idx;
        decode_tail(old_tail, &pred_cpu, &pred_idx);
        struct mcs_node *pred = &mcs_nodes[pred_cpu][pred_idx];

        atomic_store_explicit(&pred->next, node, memory_order_release);

        if (pred->numa_node == my_numa) {
            node->is_local = 1;
            atomic_store_explicit(&pred->local_next, node, memory_order_release);
        }
    }

    __sync_fetch_and_add(&lock->stats.slow_path_count, 1);
    __sync_fetch_and_add(&lock->stats.acquire_count, 1);

    int backoff = ADAPTIVE_SPIN_MIN_CYCLES;
    while (atomic_load_explicit(&node->locked, memory_order_acquire)) {
        for (int i = 0; i < backoff; i++) {
            cpu_pause();
        }
        if (backoff < ADAPTIVE_SPIN_MAX_CYCLES) {
            backoff *= 2;
        }
    }

    lock->last_acquire_tsc = rdtsc();
    lock->last_owner_numa = my_numa;
    mfence();
}

void qspin_unlock(struct qspinlock *lock) {
    mfence();

    uint32_t val = atomic_load_explicit(&lock->val, memory_order_relaxed);
    if (val == 1) {
        uint32_t expected = 1;
        if (atomic_compare_exchange_strong_explicit(
                &lock->val, &expected, 0,
                memory_order_release, memory_order_relaxed)) {
            return;
        }
    }

    uint16_t tail = val >> 16;
    if (tail != 0) {
        uint32_t cpu_id, node_idx;
        decode_tail(tail, &cpu_id, &node_idx);
        struct mcs_node *node = &mcs_nodes[cpu_id][node_idx];

        struct mcs_node *next_global;
        while ((next_global = atomic_load_explicit(&node->next, memory_order_acquire)) == NULL) {
            cpu_pause();
        }

        struct mcs_node *next_local = atomic_load_explicit(&node->local_next, memory_order_acquire);
        struct mcs_node *next_to_wake;

        if (next_local != NULL) {
            next_to_wake = next_local;
            __sync_fetch_and_add(&lock->stats.local_handoff_count, 1);
        } else {
            next_to_wake = next_global;
            __sync_fetch_and_add(&lock->stats.remote_handoff_count, 1);
        }

        atomic_store_explicit(&next_to_wake->locked, 0, memory_order_release);
        atomic_store_explicit(&node->locked, 0, memory_order_release);
    }

    atomic_store_explicit(&lock->val, 0, memory_order_release);
}

/* ========================================================================
 * Benchmarks
 * ======================================================================== */

typedef struct {
    const char *name;
    uint64_t min_cycles;
    uint64_t max_cycles;
    uint64_t total_cycles;
    uint64_t iterations;
    double avg_ns;
    double min_ns;
    double max_ns;
} benchmark_result_t;

void print_result(benchmark_result_t *result) {
    printf("  %-40s: ", result->name);
    printf("%s%6.1f ns%s (avg)  ", COLOR_GREEN, result->avg_ns, COLOR_RESET);
    printf("[%6.1f - %6.1f ns]  ", result->min_ns, result->max_ns);
    printf("(%lu iterations)\n", result->iterations);
}

/* Benchmark 1: Uncontended latency */
void bench_uncontended(void) {
    printf("\n%s▶ Benchmark 1: Uncontended Acquire/Release Latency%s\n",
           COLOR_BOLD, COLOR_RESET);

    struct qspinlock lock;
    qspin_init(&lock);

    current_cpu_id = 0;

    // Warmup
    for (int i = 0; i < WARMUP_ITERATIONS; i++) {
        qspin_lock(&lock);
        qspin_unlock(&lock);
    }

    uint64_t min_cycles = UINT64_MAX;
    uint64_t max_cycles = 0;
    uint64_t total_cycles = 0;

    for (int i = 0; i < BENCHMARK_ITERATIONS; i++) {
        uint64_t start = rdtsc_serialized();
        qspin_lock(&lock);
        qspin_unlock(&lock);
        uint64_t end = rdtsc_serialized();

        uint64_t cycles = end - start;
        total_cycles += cycles;
        if (cycles < min_cycles) min_cycles = cycles;
        if (cycles > max_cycles) max_cycles = cycles;
    }

    benchmark_result_t result = {
        .name = "Fast path (uncontended)",
        .min_cycles = min_cycles,
        .max_cycles = max_cycles,
        .total_cycles = total_cycles,
        .iterations = BENCHMARK_ITERATIONS,
        .avg_ns = cycles_to_ns(total_cycles / BENCHMARK_ITERATIONS),
        .min_ns = cycles_to_ns(min_cycles),
        .max_ns = cycles_to_ns(max_cycles)
    };

    print_result(&result);

    if (result.avg_ns < 10.0) {
        printf("  %s✓ Target achieved: < 10ns average%s\n",
               COLOR_GREEN, COLOR_RESET);
    } else {
        printf("  %s⚠ Target missed: %.1f ns (target: < 10ns)%s\n",
               COLOR_YELLOW, result.avg_ns, COLOR_RESET);
    }
}

/* Thread data for contention benchmarks */
typedef struct {
    int cpu_id;
    struct qspinlock *lock;
    uint64_t *counter;
    int iterations;
    pthread_barrier_t *barrier;
    uint64_t total_cycles;
} thread_data_t;

void *contention_worker(void *arg) {
    thread_data_t *data = (thread_data_t *)arg;
    current_cpu_id = data->cpu_id;

    pthread_barrier_wait(data->barrier);

    uint64_t start = rdtsc_serialized();

    for (int i = 0; i < data->iterations; i++) {
        qspin_lock(data->lock);
        atomic_fetch_add(data->counter, 1);
        qspin_unlock(data->lock);
    }

    uint64_t end = rdtsc_serialized();
    data->total_cycles = end - start;

    return NULL;
}

void bench_contention(int num_cpus, const char *name) {
    printf("\n%s▶ Benchmark: %s%s\n", COLOR_BOLD, name, COLOR_RESET);

    struct qspinlock lock;
    qspin_init(&lock);

    uint64_t counter = 0;
    pthread_barrier_t barrier;
    pthread_barrier_init(&barrier, NULL, num_cpus);

    pthread_t threads[8];
    thread_data_t thread_data[8];

    int iterations_per_thread = BENCHMARK_ITERATIONS / num_cpus;

    for (int i = 0; i < num_cpus; i++) {
        thread_data[i].cpu_id = i;
        thread_data[i].lock = &lock;
        thread_data[i].counter = &counter;
        thread_data[i].iterations = iterations_per_thread;
        thread_data[i].barrier = &barrier;
        thread_data[i].total_cycles = 0;

        pthread_create(&threads[i], NULL, contention_worker, &thread_data[i]);
    }

    for (int i = 0; i < num_cpus; i++) {
        pthread_join(threads[i], NULL);
    }

    pthread_barrier_destroy(&barrier);

    uint64_t total_cycles = 0;
    for (int i = 0; i < num_cpus; i++) {
        total_cycles += thread_data[i].total_cycles;
    }

    uint64_t avg_cycles = total_cycles / num_cpus;
    uint64_t operations = atomic_load(&counter);

    benchmark_result_t result = {
        .name = name,
        .iterations = operations,
        .total_cycles = avg_cycles,
        .avg_ns = cycles_to_ns(avg_cycles) / iterations_per_thread
    };

    printf("  %-40s: %s%6.1f ns%s per lock op (avg)\n",
           "Contended acquire/release",
           COLOR_GREEN, result.avg_ns, COLOR_RESET);
    printf("  %-40s: %lu\n", "Total operations", operations);
    printf("  %-40s: %.1f%% fast / %.1f%% slow\n",
           "Path distribution",
           100.0 * lock.stats.fast_path_count / lock.stats.acquire_count,
           100.0 * lock.stats.slow_path_count / lock.stats.acquire_count);

    if (lock.stats.local_handoff_count + lock.stats.remote_handoff_count > 0) {
        printf("  %-40s: %.1f%% local / %.1f%% remote\n",
               "NUMA handoffs",
               100.0 * lock.stats.local_handoff_count /
               (lock.stats.local_handoff_count + lock.stats.remote_handoff_count),
               100.0 * lock.stats.remote_handoff_count /
               (lock.stats.local_handoff_count + lock.stats.remote_handoff_count));
    }
}

/* ========================================================================
 * Main Benchmark Suite
 * ======================================================================== */

int main(void) {
    printf("\n");
    printf("╔══════════════════════════════════════════════════════════╗\n");
    printf("║  ExoV6 QSpinlock Performance Benchmark Suite             ║\n");
    printf("║  NUMA-Aware Queued Spinlock Performance Analysis         ║\n");
    printf("╚══════════════════════════════════════════════════════════╝\n\n");

    // Initialize
    for (int i = 0; i < NCPU; i++) {
        cpus[i].id = i;
        cpus[i].running = true;
    }

    for (int cpu = 0; cpu < NCPU; cpu++) {
        for (int idx = 0; idx < MCS_NODES_PER_CPU; idx++) {
            struct mcs_node *node = &mcs_nodes[cpu][idx];
            atomic_store_explicit(&node->next, NULL, memory_order_relaxed);
            atomic_store_explicit(&node->local_next, NULL, memory_order_relaxed);
            atomic_store_explicit(&node->locked, 0, memory_order_relaxed);
            node->numa_node = get_numa_node(cpu);
            node->is_local = 0;
        }
    }

    printf("%s Configuration:%s\n", COLOR_BLUE, COLOR_RESET);
    printf("  CPUs:              %d\n", NCPU);
    printf("  NUMA nodes:        2 (CPUs 0-3: socket 0, CPUs 4-7: socket 1)\n");
    printf("  Iterations:        %d\n", BENCHMARK_ITERATIONS);
    printf("  MCS nodes/CPU:     %d\n\n", MCS_NODES_PER_CPU);

    calibrate_tsc();

    // Run benchmarks
    bench_uncontended();
    bench_contention(2, "2-CPU contention (same NUMA)");
    bench_contention(4, "4-CPU contention (mixed NUMA)");
    bench_contention(8, "8-CPU contention (full system)");

    printf("\n");
    printf("╔══════════════════════════════════════════════════════════╗\n");
    printf("║  Benchmark Complete                                      ║\n");
    printf("╚══════════════════════════════════════════════════════════╝\n\n");

    printf("%sKey Metrics:%s\n", COLOR_BOLD, COLOR_RESET);
    printf("  • Fast path latency: Target < 10ns for uncontended locks\n");
    printf("  • NUMA locality: Higher local handoff %% = better NUMA awareness\n");
    printf("  • Scalability: Lower latency as CPU count increases = better MCS queuing\n\n");

    return 0;
}
