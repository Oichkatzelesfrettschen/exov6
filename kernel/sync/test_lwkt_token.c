/**
 * @file test_lwkt_token.c
 * @brief Unit tests for LWKT token implementation
 *
 * Tests all aspects of CPU-owned soft locks:
 * - Initialization and pool management
 * - Acquire/release semantics
 * - Reacquisition fast path
 * - Per-CPU tracking
 * - Hash-based pool distribution
 * - Statistics tracking
 * - Automatic release on context switch
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
#include <assert.h>

/* ========================================================================
 * Atomic Type Compatibility
 * ======================================================================== */

// Redefine _Atomic to avoid conflicts with kernel's stdatomic.h
#define _Atomic(T) T

// Map atomic operations to GCC/Clang builtins
#define atomic_store_explicit(obj, val, order) __atomic_store_n(obj, val, order)
#define atomic_load_explicit(obj, order) __atomic_load_n(obj, order)
#define atomic_compare_exchange_strong_explicit(obj, expected, desired, succ, fail) \
    __atomic_compare_exchange_n(obj, expected, desired, 0, succ, fail)
#define atomic_fetch_add_explicit(obj, val, order) __atomic_fetch_add(obj, val, order)
#define atomic_fetch_sub_explicit(obj, val, order) __atomic_fetch_sub(obj, val, order)

// Memory order constants
#define memory_order_relaxed __ATOMIC_RELAXED
#define memory_order_acquire __ATOMIC_ACQUIRE
#define memory_order_release __ATOMIC_RELEASE
#define memory_order_seq_cst __ATOMIC_SEQ_CST

/* ========================================================================
 * Kernel Compatibility Layer
 * ======================================================================== */

// CPU structure (simplified)
struct cpu {
    int id;
    void *proc;  // Current process/thread
};

// NCPU definition
#define NCPU 8

// CPU array
struct cpu cpus[NCPU];

// Get current CPU (thread-local for testing)
__thread struct cpu *current_cpu = NULL;

static inline struct cpu *mycpu(void) {
    if (!current_cpu) {
        int cpu_id = sched_getcpu();
        if (cpu_id < 0 || cpu_id >= NCPU) cpu_id = 0;
        current_cpu = &cpus[cpu_id];
    }
    return current_cpu;
}

// Mock panic function
static void panic(const char *fmt, ...) {
    va_list args;
    va_start(args, fmt);
    fprintf(stderr, "PANIC: ");
    vfprintf(stderr, fmt, args);
    fprintf(stderr, "\n");
    va_end(args);
    exit(1);
}

// Mock cprintf function
static void cprintf(const char *fmt, ...) {
    va_list args;
    va_start(args, fmt);
    vprintf(fmt, args);
    va_end(args);
}

// Mock memory functions
static void *kalloc(void) {
    return malloc(4096);
}

static void kfree(void *ptr) {
    free(ptr);
}

// Mock interrupt control
static void pushcli(void) {}
static void popcli(void) {}

/* ========================================================================
 * LWKT Token Definitions
 * ======================================================================== */

#define TOKEN_POOL_SIZE 256
#define MAX_TOKENS_PER_CPU 16
#define TOKEN_FREE_MARKER NCPU

#define likely(x)       __builtin_expect(!!(x), 1)
#define unlikely(x)     __builtin_expect(!!(x), 0)
#define EXO_ALWAYS_INLINE __attribute__((always_inline)) inline

/* Per-CPU token ownership tracking */
struct cpu_token_list {
    struct lwkt_token *tokens[MAX_TOKENS_PER_CPU];
    uint32_t count;
} __attribute__((aligned(64)));

/* Token statistics */
struct lwkt_token_stats {
    uint64_t acquire_count;
    uint64_t release_count;
    uint64_t contention_count;
    uint64_t total_hold_cycles;
    uint64_t max_hold_cycles;
    uint64_t reacquire_count;
    uint64_t cpu_acquire_count[NCPU];
} __attribute__((aligned(128)));

/* LWKT token structure */
struct lwkt_token {
    _Atomic uint32_t owner_cpu;
    uint32_t hash;
    const char *name;
    uint32_t dag_level;
    uint64_t acquire_tsc;
    struct lwkt_token_stats stats;
} __attribute__((aligned(256)));

/* Global token pool */
extern struct lwkt_token token_pool[TOKEN_POOL_SIZE];
extern struct cpu_token_list cpu_tokens[NCPU];

/* Token API */
void token_pool_init(void);
void token_init(struct lwkt_token *token, const char *name, uint32_t dag_level);
void token_acquire(struct lwkt_token *token);
void token_release(struct lwkt_token *token);
void token_release_all(void);
struct lwkt_token *token_pool_get(void *resource);
int token_holding(struct lwkt_token *token);
void token_assert_held(struct lwkt_token *token);
void token_dump_stats(struct lwkt_token *token, const char *name);
void token_reset_stats(struct lwkt_token *token);

/* ========================================================================
 * LWKT Token Implementation (embedded for testing)
 * ======================================================================== */

/* Global token pool */
struct lwkt_token token_pool[TOKEN_POOL_SIZE];

/* Per-CPU token ownership lists */
struct cpu_token_list cpu_tokens[NCPU];

/* Architecture-specific helpers */
static inline uint64_t rdtsc(void) {
    uint32_t lo, hi;
    __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
    return ((uint64_t)hi << 32) | lo;
}

static inline void pause_cpu(void) {
    __asm__ __volatile__("pause" ::: "memory");
}

/* Hash function */
static EXO_ALWAYS_INLINE uint32_t hash_ptr(void *ptr) {
    uintptr_t val = (uintptr_t)ptr;
    val = (val >> 6) ^ (val >> 12) ^ (val >> 18) ^ (val >> 24);
    return val & (TOKEN_POOL_SIZE - 1);
}

/* Per-CPU list management */
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

/* Token pool initialization */
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
    if (!resource) {
        panic("token_pool_get: NULL resource");
    }

    uint32_t hash = hash_ptr(resource);
    return &token_pool[hash];
}

/* Token operations */
void token_init(struct lwkt_token *token, const char *name, uint32_t dag_level) {
    atomic_store_explicit(&token->owner_cpu, TOKEN_FREE_MARKER, memory_order_relaxed);
    token->hash = hash_ptr(token);
    token->name = name;
    token->acquire_tsc = 0;
    token->dag_level = dag_level;
    memset(&token->stats, 0, sizeof(token->stats));
}

void token_acquire(struct lwkt_token *token) {
    uint32_t my_cpu = mycpu() - cpus;

    /* Fast path: Already own it */
    uint32_t owner = atomic_load_explicit(&token->owner_cpu, memory_order_relaxed);

    if (likely(owner == my_cpu)) {
        __sync_fetch_and_add(&token->stats.reacquire_count, 1);
        return;
    }

    /* Slow path: Spin until free */
    uint64_t spin_start = rdtsc();
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
            pause_cpu();
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
        panic("token_release: not owner (owner=%u, my_cpu=%u, token=%s)",
              owner, my_cpu, token->name);
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

void token_assert_held(struct lwkt_token *token) {
    if (!token_holding(token)) {
        uint32_t owner = atomic_load_explicit(&token->owner_cpu, memory_order_relaxed);
        panic("token_assert_held: token '%s' not held (owner=%u)",
              token->name, owner);
    }
}

void token_dump_stats(struct lwkt_token *token, const char *name) {
    struct lwkt_token_stats *s = &token->stats;

    cprintf("\n=== LWKT Token Stats: %s ===\n", name ? name : token->name);
    cprintf("Acquisitions:\n");
    cprintf("  Total:           %lu\n", s->acquire_count);
    cprintf("  Reacquires:      %lu\n", s->reacquire_count);
    cprintf("  Releases:        %lu\n", s->release_count);

    if (s->contention_count > 0) {
        cprintf("\nContention:\n");
        cprintf("  Events:          %lu\n", s->contention_count);
        cprintf("  Rate:            %.1f%%\n",
                100.0 * s->contention_count / (s->acquire_count + 1));
    }

    if (s->acquire_count > 0) {
        cprintf("\nHold Time:\n");
        cprintf("  Avg cycles:      %lu\n",
                s->total_hold_cycles / s->acquire_count);
        cprintf("  Max cycles:      %lu\n", s->max_hold_cycles);
    }

    cprintf("\nPer-CPU Acquisitions:\n");
    for (int i = 0; i < NCPU; i++) {
        if (s->cpu_acquire_count[i] > 0) {
            cprintf("  CPU %d:           %lu (%.1f%%)\n",
                    i, s->cpu_acquire_count[i],
                    100.0 * s->cpu_acquire_count[i] / (s->acquire_count + 1));
        }
    }

    uint32_t owner = atomic_load_explicit(&token->owner_cpu, memory_order_relaxed);
    cprintf("\nCurrent Status:\n");
    if (owner == TOKEN_FREE_MARKER) {
        cprintf("  State:           FREE\n");
    } else {
        cprintf("  State:           HELD by CPU %u\n", owner);
    }
}

void token_reset_stats(struct lwkt_token *token) {
    memset(&token->stats, 0, sizeof(token->stats));
}

/* ========================================================================
 * Test Infrastructure
 * ======================================================================== */

static int tests_run = 0;
static int tests_passed = 0;

#define TEST(name) \
    static void test_##name(void); \
    static void run_test_##name(void) { \
        printf("Running test: %s...", #name); \
        fflush(stdout); \
        test_##name(); \
        tests_passed++; \
        printf(" PASSED\n"); \
    } \
    static void test_##name(void)

#define RUN_TEST(name) do { \
    tests_run++; \
    run_test_##name(); \
} while(0)

/* ========================================================================
 * Test Cases
 * ======================================================================== */

/**
 * Test 1: Pool initialization
 */
TEST(pool_initialization) {
    token_pool_init();

    // Verify all tokens are initialized
    for (int i = 0; i < TOKEN_POOL_SIZE; i++) {
        assert(atomic_load_explicit(&token_pool[i].owner_cpu, memory_order_relaxed) == TOKEN_FREE_MARKER);
        assert(token_pool[i].hash == i);
        assert(token_pool[i].stats.acquire_count == 0);
    }

    // Verify per-CPU lists are empty
    for (int i = 0; i < NCPU; i++) {
        assert(cpu_tokens[i].count == 0);
    }
}

/**
 * Test 2: Single token acquire/release
 */
TEST(single_acquire_release) {
    struct lwkt_token token;
    token_init(&token, "test_token", 0);

    uint32_t my_cpu = mycpu() - cpus;

    // Acquire token
    token_acquire(&token);

    // Verify ownership
    assert(atomic_load_explicit(&token.owner_cpu, memory_order_relaxed) == my_cpu);
    assert(token_holding(&token));
    assert(token.stats.acquire_count == 1);

    // Release token
    token_release(&token);

    // Verify release
    assert(atomic_load_explicit(&token.owner_cpu, memory_order_relaxed) == TOKEN_FREE_MARKER);
    assert(!token_holding(&token));
    assert(token.stats.release_count == 1);
}

/**
 * Test 3: Reacquisition fast path
 */
TEST(reacquisition) {
    struct lwkt_token token;
    token_init(&token, "test_reacq", 0);

    // First acquisition
    token_acquire(&token);
    assert(token.stats.acquire_count == 1);
    assert(token.stats.reacquire_count == 0);

    // Reacquire (should hit fast path)
    token_acquire(&token);
    assert(token.stats.acquire_count == 1);  // No change
    assert(token.stats.reacquire_count == 1);  // Incremented

    // Reacquire again
    token_acquire(&token);
    assert(token.stats.reacquire_count == 2);

    // Single release releases all
    token_release(&token);
    assert(!token_holding(&token));
}

/**
 * Test 4: Per-CPU tracking
 */
TEST(per_cpu_tracking) {
    struct lwkt_token token;
    token_init(&token, "test_percpu", 0);

    uint32_t my_cpu = mycpu() - cpus;
    struct cpu_token_list *list = &cpu_tokens[my_cpu];

    // Initially empty
    assert(list->count == 0);

    // Acquire - should add to list
    token_acquire(&token);
    assert(list->count == 1);
    assert(list->tokens[0] == &token);

    // Reacquire - should NOT add again
    token_acquire(&token);
    assert(list->count == 1);

    // Release - should remove from list
    token_release(&token);
    assert(list->count == 0);
}

/**
 * Test 5: Multiple tokens per CPU
 */
TEST(multiple_tokens) {
    struct lwkt_token tokens[4];

    for (int i = 0; i < 4; i++) {
        char name[32];
        snprintf(name, sizeof(name), "token_%d", i);
        token_init(&tokens[i], name, 0);
    }

    uint32_t my_cpu = mycpu() - cpus;
    struct cpu_token_list *list = &cpu_tokens[my_cpu];

    // Acquire all tokens
    for (int i = 0; i < 4; i++) {
        token_acquire(&tokens[i]);
        assert(list->count == i + 1);
        assert(token_holding(&tokens[i]));
    }

    // All held
    assert(list->count == 4);

    // Release in reverse order
    for (int i = 3; i >= 0; i--) {
        token_release(&tokens[i]);
        assert(list->count == i);
    }

    assert(list->count == 0);
}

/**
 * Test 6: Token pool hash distribution
 */
TEST(pool_hash_distribution) {
    token_pool_init();

    // Create diverse resource pointers
    void *resources[100];
    for (int i = 0; i < 100; i++) {
        resources[i] = (void *)(uintptr_t)(0x1000 * (i + 1));
    }

    // Get tokens for resources
    int bucket_counts[TOKEN_POOL_SIZE] = {0};
    for (int i = 0; i < 100; i++) {
        struct lwkt_token *token = token_pool_get(resources[i]);
        assert(token >= &token_pool[0] && token < &token_pool[TOKEN_POOL_SIZE]);

        uint32_t index = token - token_pool;
        bucket_counts[index]++;
    }

    // Verify reasonable distribution (no bucket should have > 10 entries for 100 resources)
    int max_bucket = 0;
    for (int i = 0; i < TOKEN_POOL_SIZE; i++) {
        if (bucket_counts[i] > max_bucket) {
            max_bucket = bucket_counts[i];
        }
    }

    assert(max_bucket <= 10);  // Reasonable distribution
}

/**
 * Test 7: token_release_all() functionality
 */
TEST(release_all) {
    struct lwkt_token tokens[5];

    for (int i = 0; i < 5; i++) {
        char name[32];
        snprintf(name, sizeof(name), "token_%d", i);
        token_init(&tokens[i], name, 0);
        token_acquire(&tokens[i]);
    }

    uint32_t my_cpu = mycpu() - cpus;
    struct cpu_token_list *list = &cpu_tokens[my_cpu];

    assert(list->count == 5);

    // Release all at once (simulating context switch)
    token_release_all();

    // Verify all released
    assert(list->count == 0);
    for (int i = 0; i < 5; i++) {
        assert(!token_holding(&tokens[i]));
        assert(atomic_load_explicit(&tokens[i].owner_cpu, memory_order_relaxed) == TOKEN_FREE_MARKER);
    }
}

/**
 * Test 8: Statistics tracking
 */
TEST(statistics_tracking) {
    struct lwkt_token token;
    token_init(&token, "test_stats", 0);

    uint32_t my_cpu = mycpu() - cpus;

    // Initial state
    assert(token.stats.acquire_count == 0);
    assert(token.stats.release_count == 0);
    assert(token.stats.reacquire_count == 0);

    // Acquire
    token_acquire(&token);
    assert(token.stats.acquire_count == 1);
    assert(token.stats.cpu_acquire_count[my_cpu] == 1);

    // Reacquire
    token_acquire(&token);
    assert(token.stats.acquire_count == 1);
    assert(token.stats.reacquire_count == 1);

    // Release
    token_release(&token);
    assert(token.stats.release_count == 1);
    assert(token.stats.total_hold_cycles > 0);

    // Acquire again
    token_acquire(&token);
    assert(token.stats.acquire_count == 2);
    assert(token.stats.cpu_acquire_count[my_cpu] == 2);

    token_release(&token);
    assert(token.stats.release_count == 2);
}

/**
 * Test 9: Hold time tracking
 */
TEST(hold_time_tracking) {
    struct lwkt_token token;
    token_init(&token, "test_holdtime", 0);

    token_acquire(&token);

    // Simulate some work
    usleep(1000);  // 1ms

    token_release(&token);

    // Verify hold time was recorded
    assert(token.stats.total_hold_cycles > 0);
    assert(token.stats.max_hold_cycles > 0);
    assert(token.stats.max_hold_cycles == token.stats.total_hold_cycles);

    // Second acquisition with shorter hold
    token_acquire(&token);
    usleep(100);  // 0.1ms
    token_release(&token);

    // Max should still be from first acquisition
    uint64_t first_max = token.stats.max_hold_cycles;

    // Third acquisition with longer hold
    token_acquire(&token);
    usleep(2000);  // 2ms
    token_release(&token);

    // Max should update
    assert(token.stats.max_hold_cycles > first_max);
}

/**
 * Test 10: Concurrent access (stress test)
 */
static struct lwkt_token stress_token;
static volatile int stress_counter = 0;
static const int STRESS_ITERATIONS = 10000;

static void *stress_worker(void *arg) {
    int cpu_id = *(int *)arg;

    // Set CPU affinity
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(cpu_id % sysconf(_SC_NPROCESSORS_ONLN), &cpuset);
    pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset);

    // Simulate CPU assignment
    current_cpu = &cpus[cpu_id % NCPU];

    for (int i = 0; i < STRESS_ITERATIONS; i++) {
        token_acquire(&stress_token);
        stress_counter++;
        token_release(&stress_token);
    }

    return NULL;
}

TEST(concurrent_stress) {
    token_init(&stress_token, "stress_token", 0);
    stress_counter = 0;

    const int NUM_THREADS = 4;
    pthread_t threads[NUM_THREADS];
    int cpu_ids[NUM_THREADS];

    // Create worker threads
    for (int i = 0; i < NUM_THREADS; i++) {
        cpu_ids[i] = i;
        pthread_create(&threads[i], NULL, stress_worker, &cpu_ids[i]);
    }

    // Wait for completion
    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_join(threads[i], NULL);
    }

    // Verify correctness
    int expected = NUM_THREADS * STRESS_ITERATIONS;
    assert(stress_counter == expected);

    printf("\n  Stress test completed: %d increments by %d threads",
           expected, NUM_THREADS);
}

/* ========================================================================
 * Main Test Runner
 * ======================================================================== */

int main(void) {
    printf("=== LWKT Token Unit Tests ===\n\n");

    // Initialize CPU structures
    for (int i = 0; i < NCPU; i++) {
        cpus[i].id = i;
        cpus[i].proc = NULL;
    }

    // Set initial CPU
    current_cpu = &cpus[0];

    // Run all tests
    RUN_TEST(pool_initialization);
    RUN_TEST(single_acquire_release);
    RUN_TEST(reacquisition);
    RUN_TEST(per_cpu_tracking);
    RUN_TEST(multiple_tokens);
    RUN_TEST(pool_hash_distribution);
    RUN_TEST(release_all);
    RUN_TEST(statistics_tracking);
    RUN_TEST(hold_time_tracking);
    RUN_TEST(concurrent_stress);

    // Print results
    printf("\n=== Test Results ===\n");
    printf("Total:      %d tests\n", tests_run);
    printf("Passed:     %d tests  ✅\n", tests_passed);
    printf("Failed:     %d tests\n", tests_run - tests_passed);

    if (tests_passed == tests_run) {
        printf("\nAll tests PASSED! ✅\n");
        return 0;
    } else {
        printf("\nSome tests FAILED! ❌\n");
        return 1;
    }
}
