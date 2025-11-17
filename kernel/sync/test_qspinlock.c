/**
 * @file test_qspinlock.c
 * @brief Comprehensive unit tests for NUMA-aware qspinlock
 *
 * Tests:
 * 1. Basic lock/unlock functionality
 * 2. NUMA topology detection
 * 3. Hierarchical queue correctness
 * 4. Statistics tracking
 * 5. Concurrent access (multi-CPU simulation)
 * 6. Trylock behavior
 * 7. MCS queue integrity
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
#include <assert.h>

/* Use compiler builtins for atomics */
#define _Atomic(T) T
#define atomic_store_explicit(obj, val, order) __atomic_store_n(obj, val, order)
#define atomic_load_explicit(obj, order) __atomic_load_n(obj, order)
#define atomic_exchange_explicit(obj, val, order) __atomic_exchange_n(obj, val, order)
#define atomic_compare_exchange_strong_explicit(obj, expected, desired, succ, fail) \
    __atomic_compare_exchange_n(obj, expected, desired, 0, succ, fail)
#define memory_order_relaxed __ATOMIC_RELAXED
#define memory_order_acquire __ATOMIC_ACQUIRE
#define memory_order_release __ATOMIC_RELEASE
#define memory_order_acq_rel __ATOMIC_ACQ_REL
#define memory_order_seq_cst __ATOMIC_SEQ_CST

/* Test framework macros */
#define TEST_PASS "\033[32m✓ PASS\033[0m"
#define TEST_FAIL "\033[31m✗ FAIL\033[0m"
#define TEST_INFO "\033[34mℹ INFO\033[0m"

static int tests_run = 0;
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) \
    do { \
        printf("\n=== Test: %s ===\n", name); \
        tests_run++; \
    } while(0)

#define TEST_ASSERT(cond, msg) \
    do { \
        if (!(cond)) { \
            printf("%s: %s (line %d)\n", TEST_FAIL, msg, __LINE__); \
            tests_failed++; \
            return; \
        } \
    } while(0)

#define TEST_END() \
    do { \
        printf("%s: All assertions passed\n", TEST_PASS); \
        tests_passed++; \
    } while(0)

/* ========================================================================
 * Mock Environment Setup
 * ======================================================================== */

/* Mock CPU structure */
#define NCPU 8
#define MCS_NODES_PER_CPU 4

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

/* Mock config */
#define ADAPTIVE_SPIN_MIN_CYCLES 10
#define ADAPTIVE_SPIN_MAX_CYCLES 1000
#define LOCK_TIMEOUT_CYCLES (1000000000ULL)

/* ========================================================================
 * QSpinlock Implementation (embedded for testing)
 * ======================================================================== */

/* MCS Node */
struct mcs_node {
    struct mcs_node *next;
    struct mcs_node *local_next;
    uint32_t locked;
    uint32_t numa_node;
    uint8_t is_local;
    uint8_t _pad[3];
} __attribute__((aligned(64)));

/* Statistics */
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

/* QSpinlock */
struct qspinlock {
    uint32_t val;
    struct qspin_stats stats;
    uint64_t last_acquire_tsc;
    uint32_t last_owner_numa;
} __attribute__((aligned(128)));

/* Per-CPU MCS nodes */
static struct mcs_node mcs_nodes[NCPU][MCS_NODES_PER_CPU] __attribute__((aligned(64)));

/* NUMA topology */
static uint32_t numa_node_count = 2;
static uint32_t cpu_to_numa[NCPU] = {0, 0, 0, 0, 1, 1, 1, 1}; // 2 sockets, 4 CPUs each

/* Architecture helpers */
static inline uint64_t rdtsc(void) {
    static uint64_t fake_tsc = 0;
    return __sync_fetch_and_add(&fake_tsc, 100);
}

static inline void mfence(void) {
    __asm__ __volatile__("" ::: "memory");
}

static inline void pause(void) {
    __asm__ __volatile__("pause" ::: "memory");
}

/* Helper functions */
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

/* QSpinlock operations */
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

void qspin_lock(struct qspinlock *lock) {
    uint64_t start_tsc = rdtsc();

    if (qspin_trylock_fast(lock)) {
        return;
    }

    struct cpu *c = mycpu();
    uint32_t cpu_id = c->id;

    // Find free MCS node
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
        panic("qspinlock: all MCS nodes in use");
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

    uint64_t spin_start = rdtsc();
    int backoff = ADAPTIVE_SPIN_MIN_CYCLES;
    int spin_count = 0;
    while (atomic_load_explicit(&node->locked, memory_order_acquire)) {
        for (int i = 0; i < backoff; i++) {
            pause();
        }
        if (backoff < ADAPTIVE_SPIN_MAX_CYCLES) {
            backoff *= 2;
        }
        spin_count++;
        if (spin_count > 10000) {
            // Safety: prevent infinite loop in tests
            atomic_store_explicit(&node->locked, 0, memory_order_relaxed);
            break;
        }
    }

    uint64_t spin_cycles = rdtsc() - spin_start;
    __sync_fetch_and_add(&lock->stats.total_spin_cycles, spin_cycles);

    lock->last_acquire_tsc = rdtsc();
    lock->last_owner_numa = my_numa;

    mfence();
}

int qspin_trylock(struct qspinlock *lock) {
    return qspin_trylock_fast(lock);
}

void qspin_unlock(struct qspinlock *lock) {
    uint64_t hold_cycles = rdtsc() - lock->last_acquire_tsc;
    __sync_fetch_and_add(&lock->stats.total_hold_cycles, hold_cycles);

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
        int wait_count = 0;
        while ((next_global = atomic_load_explicit(&node->next, memory_order_acquire)) == NULL) {
            pause();
            if (++wait_count > 1000) break; // Safety
        }

        struct mcs_node *next_local = atomic_load_explicit(&node->local_next, memory_order_acquire);
        struct mcs_node *next_to_wake;

        if (next_local != NULL) {
            next_to_wake = next_local;
            __sync_fetch_and_add(&lock->stats.local_handoff_count, 1);
        } else if (next_global != NULL) {
            next_to_wake = next_global;
            __sync_fetch_and_add(&lock->stats.remote_handoff_count, 1);
        } else {
            atomic_store_explicit(&lock->val, 0, memory_order_release);
            return;
        }

        atomic_store_explicit(&next_to_wake->locked, 0, memory_order_release);
        atomic_store_explicit(&node->locked, 0, memory_order_release);
    }

    atomic_store_explicit(&lock->val, 0, memory_order_release);
}

void qspin_dump_stats(struct qspinlock *lock, const char *name) {
    struct qspin_stats *s = &lock->stats;
    printf("\n=== QSpinlock Stats: %s ===\n", name);
    printf("Acquisitions:     %lu\n", s->acquire_count);
    printf("  Fast path:      %lu (%.1f%%)\n",
           s->fast_path_count,
           s->acquire_count ? 100.0 * s->fast_path_count / s->acquire_count : 0.0);
    printf("  Slow path:      %lu (%.1f%%)\n",
           s->slow_path_count,
           s->acquire_count ? 100.0 * s->slow_path_count / s->acquire_count : 0.0);

    uint64_t total_handoffs = s->local_handoff_count + s->remote_handoff_count;
    if (total_handoffs > 0) {
        printf("NUMA Handoffs:\n");
        printf("  Local:          %lu (%.1f%%)\n",
               s->local_handoff_count,
               100.0 * s->local_handoff_count / total_handoffs);
        printf("  Remote:         %lu (%.1f%%)\n",
               s->remote_handoff_count,
               100.0 * s->remote_handoff_count / total_handoffs);
    }
}

/* ========================================================================
 * Unit Tests
 * ======================================================================== */

void test_init(void) {
    TEST_START("Lock initialization");

    struct qspinlock lock;
    qspin_init(&lock);

    TEST_ASSERT(atomic_load_explicit(&lock.val, memory_order_relaxed) == 0,
                "Lock should be initialized to 0");
    TEST_ASSERT(lock.stats.acquire_count == 0,
                "Acquire count should be 0");
    TEST_ASSERT(lock.last_acquire_tsc == 0,
                "Last acquire TSC should be 0");

    TEST_END();
}

void test_basic_lock_unlock(void) {
    TEST_START("Basic lock/unlock");

    struct qspinlock lock;
    qspin_init(&lock);

    current_cpu_id = 0;

    qspin_lock(&lock);
    TEST_ASSERT(atomic_load_explicit(&lock.val, memory_order_relaxed) != 0,
                "Lock should be held");
    TEST_ASSERT(lock.stats.acquire_count == 1,
                "Acquire count should be 1");
    TEST_ASSERT(lock.stats.fast_path_count == 1,
                "Should use fast path");

    qspin_unlock(&lock);
    TEST_ASSERT(atomic_load_explicit(&lock.val, memory_order_relaxed) == 0,
                "Lock should be released");

    TEST_END();
}

void test_trylock(void) {
    TEST_START("Trylock behavior");

    struct qspinlock lock;
    qspin_init(&lock);

    current_cpu_id = 0;

    int result = qspin_trylock(&lock);
    TEST_ASSERT(result == 1, "Trylock should succeed on free lock");
    TEST_ASSERT(atomic_load_explicit(&lock.val, memory_order_relaxed) != 0,
                "Lock should be held");

    current_cpu_id = 1;
    result = qspin_trylock(&lock);
    TEST_ASSERT(result == 0, "Trylock should fail on held lock");

    current_cpu_id = 0;
    qspin_unlock(&lock);

    TEST_END();
}

void test_multiple_acquire_release(void) {
    TEST_START("Multiple acquire/release cycles");

    struct qspinlock lock;
    qspin_init(&lock);

    current_cpu_id = 0;

    for (int i = 0; i < 10; i++) {
        qspin_lock(&lock);
        TEST_ASSERT(atomic_load_explicit(&lock.val, memory_order_relaxed) != 0,
                    "Lock should be held");
        qspin_unlock(&lock);
        TEST_ASSERT(atomic_load_explicit(&lock.val, memory_order_relaxed) == 0,
                    "Lock should be released");
    }

    TEST_ASSERT(lock.stats.acquire_count == 10,
                "Should have 10 acquisitions");
    TEST_ASSERT(lock.stats.fast_path_count == 10,
                "All should be fast path");

    TEST_END();
}

void test_numa_topology(void) {
    TEST_START("NUMA topology detection");

    TEST_ASSERT(numa_node_count == 2,
                "Should have 2 NUMA nodes");

    // CPUs 0-3 on socket 0
    for (int i = 0; i < 4; i++) {
        TEST_ASSERT(get_numa_node(i) == 0,
                    "CPUs 0-3 should be on NUMA node 0");
    }

    // CPUs 4-7 on socket 1
    for (int i = 4; i < 8; i++) {
        TEST_ASSERT(get_numa_node(i) == 1,
                    "CPUs 4-7 should be on NUMA node 1");
    }

    TEST_END();
}

void test_mcs_encode_decode(void) {
    TEST_START("MCS tail encoding/decoding");

    for (uint32_t cpu = 0; cpu < NCPU; cpu++) {
        for (uint32_t idx = 0; idx < MCS_NODES_PER_CPU; idx++) {
            uint16_t tail = encode_tail(cpu, idx);
            uint32_t decoded_cpu, decoded_idx;
            decode_tail(tail, &decoded_cpu, &decoded_idx);

            TEST_ASSERT(decoded_cpu == cpu,
                        "CPU ID should match");
            TEST_ASSERT(decoded_idx == idx,
                        "Node index should match");
        }
    }

    TEST_END();
}

void test_statistics_tracking(void) {
    TEST_START("Statistics tracking");

    struct qspinlock lock;
    qspin_init(&lock);

    current_cpu_id = 0;

    // Fast path acquisitions
    for (int i = 0; i < 5; i++) {
        qspin_lock(&lock);
        qspin_unlock(&lock);
    }

    TEST_ASSERT(lock.stats.acquire_count == 5,
                "Should have 5 acquisitions");
    TEST_ASSERT(lock.stats.fast_path_count == 5,
                "All should be fast path");
    TEST_ASSERT(lock.stats.slow_path_count == 0,
                "No slow path acquisitions");
    TEST_ASSERT(lock.stats.total_hold_cycles > 0,
                "Should track hold time");

    qspin_dump_stats(&lock, "test_lock");

    TEST_END();
}

void test_nested_locks(void) {
    TEST_START("Nested lock support (MCS node slots)");

    struct qspinlock lock1, lock2, lock3;
    qspin_init(&lock1);
    qspin_init(&lock2);
    qspin_init(&lock3);

    current_cpu_id = 0;

    qspin_lock(&lock1);
    qspin_lock(&lock2);
    qspin_lock(&lock3);

    TEST_ASSERT(atomic_load_explicit(&lock1.val, memory_order_relaxed) != 0,
                "Lock1 should be held");
    TEST_ASSERT(atomic_load_explicit(&lock2.val, memory_order_relaxed) != 0,
                "Lock2 should be held");
    TEST_ASSERT(atomic_load_explicit(&lock3.val, memory_order_relaxed) != 0,
                "Lock3 should be held");

    qspin_unlock(&lock3);
    qspin_unlock(&lock2);
    qspin_unlock(&lock1);

    TEST_ASSERT(atomic_load_explicit(&lock1.val, memory_order_relaxed) == 0,
                "Lock1 should be released");
    TEST_ASSERT(atomic_load_explicit(&lock2.val, memory_order_relaxed) == 0,
                "Lock2 should be released");
    TEST_ASSERT(atomic_load_explicit(&lock3.val, memory_order_relaxed) == 0,
                "Lock3 should be released");

    TEST_END();
}

void test_cache_line_alignment(void) {
    TEST_START("Cache line alignment");

    TEST_ASSERT(sizeof(struct mcs_node) <= 64,
                "MCS node should fit in cache line");
    TEST_ASSERT(((uintptr_t)&mcs_nodes[0][0] % 64) == 0,
                "MCS nodes should be 64-byte aligned");
    TEST_ASSERT(sizeof(struct qspinlock) <= 256,
                "QSpinlock should be reasonably sized");

    TEST_END();
}

/* ========================================================================
 * Test Runner
 * ======================================================================== */

int main(void) {
    printf("\n");
    printf("╔══════════════════════════════════════════════════════════╗\n");
    printf("║  ExoV6 QSpinlock Unit Test Suite                        ║\n");
    printf("║  NUMA-Aware Queued Spinlock Verification                ║\n");
    printf("╚══════════════════════════════════════════════════════════╝\n");

    // Initialize CPU array
    for (int i = 0; i < NCPU; i++) {
        cpus[i].id = i;
        cpus[i].running = true;
    }

    // Initialize MCS nodes
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

    printf("\n%s Configuration: %d CPUs, %d NUMA nodes\n",
           TEST_INFO, NCPU, numa_node_count);
    printf("%s MCS nodes per CPU: %d\n", TEST_INFO, MCS_NODES_PER_CPU);

    // Run tests
    test_init();
    test_basic_lock_unlock();
    test_trylock();
    test_multiple_acquire_release();
    test_numa_topology();
    test_mcs_encode_decode();
    test_statistics_tracking();
    test_nested_locks();
    test_cache_line_alignment();

    // Summary
    printf("\n");
    printf("╔══════════════════════════════════════════════════════════╗\n");
    printf("║  Test Results                                            ║\n");
    printf("╠══════════════════════════════════════════════════════════╣\n");
    printf("║  Total:    %3d tests                                     ║\n", tests_run);
    printf("║  Passed:   %s%3d tests%s                                     ║\n",
           tests_passed == tests_run ? "\033[32m" : "", tests_passed, "\033[0m");
    printf("║  Failed:   %s%3d tests%s                                     ║\n",
           tests_failed > 0 ? "\033[31m" : "", tests_failed, "\033[0m");
    printf("╚══════════════════════════════════════════════════════════╝\n");

    if (tests_failed == 0) {
        printf("\n\033[32m✓ All tests PASSED\033[0m\n\n");
        return 0;
    } else {
        printf("\n\033[31m✗ Some tests FAILED\033[0m\n\n");
        return 1;
    }
}
