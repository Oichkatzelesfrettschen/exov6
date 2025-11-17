/**
 * @file test_dag.c
 * @brief Comprehensive unit tests for DAG lock ordering system
 *
 * Tests all aspects of the DAG (Directed Acyclic Graph) lock ordering
 * subsystem for deadlock prevention:
 * - Proper hierarchical ordering validation
 * - Violation detection and reporting
 * - Token reacquisition handling
 * - Lock release tracking
 * - Stack overflow protection
 * - Deep lock chains
 * - Concurrent validation
 * - Statistics accuracy
 *
 * @version 1.0
 * @date 2025-11-17
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>
#include <assert.h>
#include <stdatomic.h>

/* ========================================================================
 * Test Framework Configuration
 * ======================================================================== */

#define USE_DAG_CHECKING  1
#define MAX_HELD_LOCKS    16
#define LOCK_LEVEL_MAX    100

/* Test result tracking */
static int tests_passed = 0;
static int tests_failed = 0;
static int violation_detected = 0;  // Flag set by mock panic handler

/* ========================================================================
 * Mock Types and Structures
 * ======================================================================== */

/* Lock type identifiers */
#define LOCK_TYPE_QSPIN    1
#define LOCK_TYPE_ADAPTIVE 2
#define LOCK_TYPE_TOKEN    3
#define LOCK_TYPE_SLEEP    4

/* Lock hierarchy levels (same as production) */
#define LOCK_LEVEL_SCHEDULER    10
#define LOCK_LEVEL_MEMORY       20
#define LOCK_LEVEL_PROCESS      30
#define LOCK_LEVEL_FILESYSTEM   40
#define LOCK_LEVEL_DEVICE       50
#define LOCK_LEVEL_NETWORK      60
#define LOCK_LEVEL_CAPABILITY   70
#define LOCK_LEVEL_USER         80

/**
 * Lock acquisition record
 */
struct lock_acquisition {
    void *lock_addr;           // Address of lock
    const char *lock_name;     // Name (debug)
    uint32_t dag_level;        // DAG hierarchy level
    uint32_t lock_type;        // Type (LOCK_TYPE_*)
    uint64_t acquire_tsc;      // TSC at acquisition
    const char *file;          // Source file
    int line;                  // Source line
};

/**
 * Per-thread lock tracker
 */
struct thread_lock_tracker {
    struct lock_acquisition stack[MAX_HELD_LOCKS];
    uint32_t depth;            // Current stack depth
    uint32_t highest_level;    // Highest DAG level held
    uint32_t max_depth;        // Maximum depth reached
    uint64_t violations;       // Violations by this thread
};

/**
 * Global DAG statistics
 */
struct dag_stats {
    uint64_t total_acquisitions;
    uint64_t dag_checks;
    uint64_t violations_detected;
    uint64_t max_chain_length;
    uint64_t violations_by_level[LOCK_LEVEL_MAX];
};

/* Global statistics */
struct dag_stats global_dag_stats;

/* Thread-local tracker (simulating per-thread storage) */
_Thread_local struct thread_lock_tracker current_tracker;

/* ========================================================================
 * DAG Implementation (Embedded for Testing)
 * ======================================================================== */

/**
 * Get current thread's lock tracker (test version)
 */
struct thread_lock_tracker *get_lock_tracker(void) {
    return &current_tracker;
}

/**
 * Read TSC (test version)
 */
static inline uint64_t rdtsc(void) {
    uint32_t lo, hi;
    __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
    return ((uint64_t)hi << 32) | lo;
}

/**
 * Get lock type name
 */
static const char *lock_type_name(uint32_t lock_type) {
    switch (lock_type) {
        case LOCK_TYPE_QSPIN:    return "qspinlock";
        case LOCK_TYPE_ADAPTIVE: return "adaptive_mutex";
        case LOCK_TYPE_TOKEN:    return "lwkt_token";
        case LOCK_TYPE_SLEEP:    return "sleep_lock";
        default:                 return "unknown";
    }
}

/**
 * Mock panic handler (sets flag instead of crashing)
 */
static void mock_panic(const char *msg) {
    (void)msg;  // Unused - just for API compatibility
    violation_detected = 1;
    // Don't actually crash - just record the violation
}

/**
 * Report DAG violation
 */
static void dag_report_violation(struct thread_lock_tracker *tracker,
                                void *new_lock, const char *new_name,
                                uint32_t new_level, uint32_t new_type,
                                const char *file, int line) {
    printf("\n=== DAG VIOLATION DETECTED ===\n");
    printf("Attempted acquisition:\n");
    printf("  Lock:   %s (%p)\n", new_name, new_lock);
    printf("  Level:  %u\n", new_level);
    printf("  Type:   %s\n", lock_type_name(new_type));
    printf("  Source: %s:%d\n", file, line);

    printf("\nCurrently held locks (%u):\n", tracker->depth);
    for (uint32_t i = 0; i < tracker->depth; i++) {
        struct lock_acquisition *acq = &tracker->stack[i];
        printf("  [%u] %s (level %u, %s) at %s:%d\n",
               i, acq->lock_name, acq->dag_level,
               lock_type_name(acq->lock_type),
               acq->file, acq->line);
    }

    printf("\nViolation: Level %u <= %u (must be strictly increasing)\n",
           new_level, tracker->highest_level);

    tracker->violations++;
    mock_panic("DAG violation");
}

/**
 * Validate lock acquisition against DAG ordering
 */
int dag_validate_acquisition(void *lock_addr, const char *name,
                             uint32_t dag_level, uint32_t lock_type,
                             const char *file, int line) {
    struct thread_lock_tracker *tracker = get_lock_tracker();

    if (!tracker) {
        return 1;
    }

    __sync_fetch_and_add(&global_dag_stats.dag_checks, 1);

    // Check for reacquisition
    for (uint32_t i = 0; i < tracker->depth; i++) {
        if (tracker->stack[i].lock_addr == lock_addr) {
            if (lock_type == LOCK_TYPE_TOKEN) {
                // Tokens allow reacquisition
                return 1;
            }

            // Other lock types don't allow reacquisition
            printf("\nERROR: Reacquisition of non-token lock detected:\n");
            printf("  Lock: %s (%p)\n", name, lock_addr);
            printf("  Type: %s\n", lock_type_name(lock_type));
            printf("  Location: %s:%d\n", file, line);
            mock_panic("Lock reacquisition");
            return 0;
        }
    }

    // Check DAG ordering
    for (uint32_t i = 0; i < tracker->depth; i++) {
        if (dag_level <= tracker->stack[i].dag_level) {
            // DAG VIOLATION
            __sync_fetch_and_add(&global_dag_stats.violations_detected, 1);

            if (dag_level < LOCK_LEVEL_MAX) {
                __sync_fetch_and_add(&global_dag_stats.violations_by_level[dag_level], 1);
            }

            dag_report_violation(tracker, lock_addr, name, dag_level,
                               lock_type, file, line);
            return 0;
        }
    }

    return 1;
}

/**
 * Track lock acquisition
 */
void dag_lock_acquired(void *lock_addr, const char *name,
                      uint32_t dag_level, uint32_t lock_type,
                      const char *file, int line) {
    struct thread_lock_tracker *tracker = get_lock_tracker();

    if (!tracker) {
        return;
    }

    if (tracker->depth >= MAX_HELD_LOCKS) {
        printf("ERROR: Lock stack overflow (max %d)\n", MAX_HELD_LOCKS);
        mock_panic("Stack overflow");
        return;
    }

    // Record acquisition
    struct lock_acquisition *acq = &tracker->stack[tracker->depth];
    acq->lock_addr = lock_addr;
    acq->lock_name = name;
    acq->dag_level = dag_level;
    acq->lock_type = lock_type;
    acq->acquire_tsc = rdtsc();
    acq->file = file;
    acq->line = line;

    tracker->depth++;

    // Update statistics
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
 * Track lock release
 */
void dag_lock_released(void *lock_addr) {
    struct thread_lock_tracker *tracker = get_lock_tracker();

    if (!tracker || tracker->depth == 0) {
        return;
    }

    // Find lock in stack
    for (int i = tracker->depth - 1; i >= 0; i--) {
        if (tracker->stack[i].lock_addr == lock_addr) {
            // Found it - remove from stack

            if (i != (int)(tracker->depth - 1)) {
                printf("WARNING: Non-LIFO lock release: %s (depth %d, expected %d)\n",
                       tracker->stack[i].lock_name, i, tracker->depth - 1);
            }

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

/**
 * Reset DAG statistics
 */
void dag_reset_stats(void) {
    memset(&global_dag_stats, 0, sizeof(global_dag_stats));
}

/* ========================================================================
 * Test Helper Macros
 * ======================================================================== */

#define TEST_START(name) \
    do { \
        printf("\n--- Test: %s ---\n", name); \
        memset(&current_tracker, 0, sizeof(current_tracker)); \
        violation_detected = 0; \
    } while (0)

#define TEST_EXPECT(cond, msg) \
    do { \
        if (cond) { \
            printf("  ✓ %s\n", msg); \
            tests_passed++; \
        } else { \
            printf("  ✗ %s\n", msg); \
            tests_failed++; \
        } \
    } while (0)

#define TEST_EXPECT_VIOLATION(msg) \
    TEST_EXPECT(violation_detected, msg)

#define TEST_EXPECT_NO_VIOLATION(msg) \
    TEST_EXPECT(!violation_detected, msg)

/* ========================================================================
 * Test Cases
 * ======================================================================== */

/**
 * Test 1: Proper hierarchical ordering
 *
 * Acquire locks in strictly increasing DAG level order.
 * Should succeed without violations.
 */
void test_proper_ordering(void) {
    TEST_START("Proper hierarchical ordering");

    // Mock locks
    int lock1, lock2, lock3, lock4;

    // Acquire in increasing order: 10 -> 20 -> 30 -> 40
    int ok1 = dag_validate_acquisition(&lock1, "scheduler_lock",
                                       LOCK_LEVEL_SCHEDULER, LOCK_TYPE_QSPIN,
                                       __FILE__, __LINE__);
    if (ok1) {
        dag_lock_acquired(&lock1, "scheduler_lock",
                         LOCK_LEVEL_SCHEDULER, LOCK_TYPE_QSPIN,
                         __FILE__, __LINE__);
    }

    int ok2 = dag_validate_acquisition(&lock2, "memory_lock",
                                       LOCK_LEVEL_MEMORY, LOCK_TYPE_ADAPTIVE,
                                       __FILE__, __LINE__);
    if (ok2) {
        dag_lock_acquired(&lock2, "memory_lock",
                         LOCK_LEVEL_MEMORY, LOCK_TYPE_ADAPTIVE,
                         __FILE__, __LINE__);
    }

    int ok3 = dag_validate_acquisition(&lock3, "process_lock",
                                       LOCK_LEVEL_PROCESS, LOCK_TYPE_QSPIN,
                                       __FILE__, __LINE__);
    if (ok3) {
        dag_lock_acquired(&lock3, "process_lock",
                         LOCK_LEVEL_PROCESS, LOCK_TYPE_QSPIN,
                         __FILE__, __LINE__);
    }

    int ok4 = dag_validate_acquisition(&lock4, "fs_lock",
                                       LOCK_LEVEL_FILESYSTEM, LOCK_TYPE_ADAPTIVE,
                                       __FILE__, __LINE__);
    if (ok4) {
        dag_lock_acquired(&lock4, "fs_lock",
                         LOCK_LEVEL_FILESYSTEM, LOCK_TYPE_ADAPTIVE,
                         __FILE__, __LINE__);
    }

    TEST_EXPECT_NO_VIOLATION("All acquisitions succeeded");
    TEST_EXPECT(ok1 && ok2 && ok3 && ok4, "All validations passed");
    TEST_EXPECT(current_tracker.depth == 4, "Stack depth is 4");
    TEST_EXPECT(current_tracker.highest_level == LOCK_LEVEL_FILESYSTEM,
                "Highest level is FILESYSTEM");

    // Release in reverse order (LIFO)
    dag_lock_released(&lock4);
    dag_lock_released(&lock3);
    dag_lock_released(&lock2);
    dag_lock_released(&lock1);

    TEST_EXPECT(current_tracker.depth == 0, "All locks released");
}

/**
 * Test 2: Reverse ordering violation
 *
 * Attempt to acquire locks in decreasing order.
 * Should detect violation.
 */
void test_reverse_ordering(void) {
    TEST_START("Reverse ordering violation");

    int lock1, lock2;

    // Acquire high-level lock first
    dag_validate_acquisition(&lock1, "fs_lock",
                            LOCK_LEVEL_FILESYSTEM, LOCK_TYPE_QSPIN,
                            __FILE__, __LINE__);
    dag_lock_acquired(&lock1, "fs_lock",
                     LOCK_LEVEL_FILESYSTEM, LOCK_TYPE_QSPIN,
                     __FILE__, __LINE__);

    // Try to acquire lower-level lock (should fail)
    violation_detected = 0;  // Reset flag
    int ok = dag_validate_acquisition(&lock2, "memory_lock",
                                     LOCK_LEVEL_MEMORY, LOCK_TYPE_QSPIN,
                                     __FILE__, __LINE__);

    TEST_EXPECT_VIOLATION("Violation detected for reverse ordering");
    TEST_EXPECT(!ok, "Validation returned failure");
    TEST_EXPECT(current_tracker.violations == 1, "Violation count incremented");
    TEST_EXPECT(global_dag_stats.violations_detected == 1,
                "Global violation count incremented");

    // Clean up
    dag_lock_released(&lock1);
}

/**
 * Test 3: Equal level violation
 *
 * Attempt to acquire two locks at the same DAG level.
 * Should detect violation (must be strictly increasing).
 */
void test_equal_level_violation(void) {
    TEST_START("Equal level violation");

    int lock1, lock2;

    // Acquire first lock
    dag_validate_acquisition(&lock1, "memory_lock_1",
                            LOCK_LEVEL_MEMORY, LOCK_TYPE_QSPIN,
                            __FILE__, __LINE__);
    dag_lock_acquired(&lock1, "memory_lock_1",
                     LOCK_LEVEL_MEMORY, LOCK_TYPE_QSPIN,
                     __FILE__, __LINE__);

    // Try to acquire another lock at same level (should fail)
    violation_detected = 0;
    int ok = dag_validate_acquisition(&lock2, "memory_lock_2",
                                     LOCK_LEVEL_MEMORY, LOCK_TYPE_QSPIN,
                                     __FILE__, __LINE__);

    TEST_EXPECT_VIOLATION("Violation detected for equal level");
    TEST_EXPECT(!ok, "Validation returned failure");

    dag_lock_released(&lock1);
}

/**
 * Test 4: Token reacquisition (allowed)
 *
 * Tokens should allow reacquisition since they're CPU-owned.
 */
void test_token_reacquisition(void) {
    TEST_START("Token reacquisition (allowed)");

    int token;

    // Acquire token
    dag_validate_acquisition(&token, "test_token",
                            LOCK_LEVEL_MEMORY, LOCK_TYPE_TOKEN,
                            __FILE__, __LINE__);
    dag_lock_acquired(&token, "test_token",
                     LOCK_LEVEL_MEMORY, LOCK_TYPE_TOKEN,
                     __FILE__, __LINE__);

    TEST_EXPECT(current_tracker.depth == 1, "Token acquired");

    // Reacquire same token (should succeed)
    violation_detected = 0;
    int ok = dag_validate_acquisition(&token, "test_token",
                                     LOCK_LEVEL_MEMORY, LOCK_TYPE_TOKEN,
                                     __FILE__, __LINE__);

    TEST_EXPECT_NO_VIOLATION("No violation for token reacquisition");
    TEST_EXPECT(ok, "Token reacquisition allowed");

    dag_lock_released(&token);
}

/**
 * Test 5: Non-token reacquisition (forbidden)
 *
 * Other lock types should not allow reacquisition.
 */
void test_spinlock_reacquisition(void) {
    TEST_START("Spinlock reacquisition (forbidden)");

    int lock;

    // Acquire spinlock
    dag_validate_acquisition(&lock, "test_spinlock",
                            LOCK_LEVEL_MEMORY, LOCK_TYPE_QSPIN,
                            __FILE__, __LINE__);
    dag_lock_acquired(&lock, "test_spinlock",
                     LOCK_LEVEL_MEMORY, LOCK_TYPE_QSPIN,
                     __FILE__, __LINE__);

    // Try to reacquire (should fail)
    violation_detected = 0;
    int ok = dag_validate_acquisition(&lock, "test_spinlock",
                                     LOCK_LEVEL_MEMORY, LOCK_TYPE_QSPIN,
                                     __FILE__, __LINE__);

    TEST_EXPECT_VIOLATION("Violation detected for spinlock reacquisition");
    TEST_EXPECT(!ok, "Spinlock reacquisition forbidden");

    dag_lock_released(&lock);
}

/**
 * Test 6: Lock release tracking
 *
 * Verify that lock release correctly updates tracker state.
 */
void test_lock_release(void) {
    TEST_START("Lock release tracking");

    int lock1, lock2, lock3;

    // Acquire 3 locks
    dag_validate_acquisition(&lock1, "lock1", 10, LOCK_TYPE_QSPIN, __FILE__, __LINE__);
    dag_lock_acquired(&lock1, "lock1", 10, LOCK_TYPE_QSPIN, __FILE__, __LINE__);

    dag_validate_acquisition(&lock2, "lock2", 20, LOCK_TYPE_QSPIN, __FILE__, __LINE__);
    dag_lock_acquired(&lock2, "lock2", 20, LOCK_TYPE_QSPIN, __FILE__, __LINE__);

    dag_validate_acquisition(&lock3, "lock3", 30, LOCK_TYPE_QSPIN, __FILE__, __LINE__);
    dag_lock_acquired(&lock3, "lock3", 30, LOCK_TYPE_QSPIN, __FILE__, __LINE__);

    TEST_EXPECT(current_tracker.depth == 3, "3 locks acquired");
    TEST_EXPECT(current_tracker.highest_level == 30, "Highest level is 30");

    // Release middle lock (non-LIFO)
    dag_lock_released(&lock2);

    TEST_EXPECT(current_tracker.depth == 2, "Depth decreased to 2");
    TEST_EXPECT(current_tracker.highest_level == 30, "Highest level still 30");

    // Release remaining locks
    dag_lock_released(&lock3);
    TEST_EXPECT(current_tracker.depth == 1, "Depth decreased to 1");
    TEST_EXPECT(current_tracker.highest_level == 10, "Highest level recalculated to 10");

    dag_lock_released(&lock1);
    TEST_EXPECT(current_tracker.depth == 0, "All locks released");
    TEST_EXPECT(current_tracker.highest_level == 0, "Highest level reset to 0");
}

/**
 * Test 7: Stack overflow protection
 *
 * Attempt to acquire more than MAX_HELD_LOCKS.
 * Should detect overflow.
 */
void test_stack_overflow(void) {
    TEST_START("Stack overflow protection");

    int locks[MAX_HELD_LOCKS + 1];

    // Acquire MAX_HELD_LOCKS locks (should succeed)
    for (int i = 0; i < MAX_HELD_LOCKS; i++) {
        char name[32];
        snprintf(name, sizeof(name), "lock_%d", i);
        dag_validate_acquisition(&locks[i], name, 10 + i, LOCK_TYPE_QSPIN,
                                __FILE__, __LINE__);
        dag_lock_acquired(&locks[i], name, 10 + i, LOCK_TYPE_QSPIN,
                         __FILE__, __LINE__);
    }

    TEST_EXPECT(current_tracker.depth == MAX_HELD_LOCKS,
                "MAX_HELD_LOCKS acquired successfully");

    // Try to acquire one more (should trigger overflow)
    violation_detected = 0;
    dag_validate_acquisition(&locks[MAX_HELD_LOCKS], "overflow_lock",
                            10 + MAX_HELD_LOCKS, LOCK_TYPE_QSPIN,
                            __FILE__, __LINE__);
    dag_lock_acquired(&locks[MAX_HELD_LOCKS], "overflow_lock",
                     10 + MAX_HELD_LOCKS, LOCK_TYPE_QSPIN,
                     __FILE__, __LINE__);

    TEST_EXPECT_VIOLATION("Overflow detected");

    // Clean up
    for (int i = MAX_HELD_LOCKS - 1; i >= 0; i--) {
        dag_lock_released(&locks[i]);
    }
}

/**
 * Test 8: Deep lock chain
 *
 * Acquire 8+ locks in proper order to test deep chains.
 */
void test_deep_chain(void) {
    TEST_START("Deep lock chain (8+ locks)");

    int locks[10];

    // Acquire 10 locks in increasing order
    for (int i = 0; i < 10; i++) {
        char name[32];
        snprintf(name, sizeof(name), "lock_%d", i);
        dag_validate_acquisition(&locks[i], name, 10 + i * 5, LOCK_TYPE_QSPIN,
                                __FILE__, __LINE__);
        dag_lock_acquired(&locks[i], name, 10 + i * 5, LOCK_TYPE_QSPIN,
                         __FILE__, __LINE__);
    }

    TEST_EXPECT_NO_VIOLATION("No violations in deep chain");
    TEST_EXPECT(current_tracker.depth == 10, "10 locks acquired");
    TEST_EXPECT(current_tracker.highest_level == 10 + 9 * 5,
                "Highest level is correct");
    TEST_EXPECT(global_dag_stats.max_chain_length >= 10,
                "Global max chain length updated");

    // Release all
    for (int i = 9; i >= 0; i--) {
        dag_lock_released(&locks[i]);
    }

    TEST_EXPECT(current_tracker.depth == 0, "All locks released");
}

/**
 * Test 9: Statistics accuracy
 *
 * Verify that DAG statistics are tracked correctly.
 */
void test_statistics(void) {
    TEST_START("Statistics accuracy");

    dag_reset_stats();

    int lock1, lock2, lock3;

    // 3 acquisitions, 3 checks
    dag_validate_acquisition(&lock1, "lock1", 10, LOCK_TYPE_QSPIN, __FILE__, __LINE__);
    dag_lock_acquired(&lock1, "lock1", 10, LOCK_TYPE_QSPIN, __FILE__, __LINE__);

    dag_validate_acquisition(&lock2, "lock2", 20, LOCK_TYPE_QSPIN, __FILE__, __LINE__);
    dag_lock_acquired(&lock2, "lock2", 20, LOCK_TYPE_QSPIN, __FILE__, __LINE__);

    dag_validate_acquisition(&lock3, "lock3", 30, LOCK_TYPE_QSPIN, __FILE__, __LINE__);
    dag_lock_acquired(&lock3, "lock3", 30, LOCK_TYPE_QSPIN, __FILE__, __LINE__);

    TEST_EXPECT(global_dag_stats.total_acquisitions == 3,
                "Total acquisitions tracked");
    TEST_EXPECT(global_dag_stats.dag_checks == 3,
                "DAG checks tracked");

    // Trigger a violation
    violation_detected = 0;
    int lock4;
    dag_validate_acquisition(&lock4, "lock4", 15, LOCK_TYPE_QSPIN, __FILE__, __LINE__);

    TEST_EXPECT(global_dag_stats.violations_detected == 1,
                "Violations tracked");
    TEST_EXPECT(global_dag_stats.violations_by_level[15] == 1,
                "Violations by level tracked");

    // Clean up
    dag_lock_released(&lock3);
    dag_lock_released(&lock2);
    dag_lock_released(&lock1);
}

/**
 * Test 10: Concurrent validation stress test
 *
 * Multiple threads acquiring locks simultaneously.
 */
void *thread_worker(void *arg) {
    int thread_id = *(int *)arg;
    int locks[5];

    // Each thread acquires 5 locks
    for (int i = 0; i < 5; i++) {
        char name[32];
        snprintf(name, sizeof(name), "thread_%d_lock_%d", thread_id, i);
        dag_validate_acquisition(&locks[i], name, 10 + i * 10, LOCK_TYPE_QSPIN,
                                __FILE__, __LINE__);
        dag_lock_acquired(&locks[i], name, 10 + i * 10, LOCK_TYPE_QSPIN,
                         __FILE__, __LINE__);
    }

    // Release all
    for (int i = 4; i >= 0; i--) {
        dag_lock_released(&locks[i]);
    }

    return NULL;
}

void test_concurrent_validation(void) {
    TEST_START("Concurrent validation");

    dag_reset_stats();

    const int NUM_THREADS = 4;
    pthread_t threads[NUM_THREADS];
    int thread_ids[NUM_THREADS];

    // Create threads
    for (int i = 0; i < NUM_THREADS; i++) {
        thread_ids[i] = i;
        pthread_create(&threads[i], NULL, thread_worker, &thread_ids[i]);
    }

    // Wait for completion
    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_join(threads[i], NULL);
    }

    // Each thread did 5 acquisitions and 5 checks
    TEST_EXPECT(global_dag_stats.total_acquisitions == NUM_THREADS * 5,
                "All threads' acquisitions tracked");
    TEST_EXPECT(global_dag_stats.dag_checks == NUM_THREADS * 5,
                "All threads' checks tracked");

    printf("  Total acquisitions: %lu\n", global_dag_stats.total_acquisitions);
    printf("  DAG checks: %lu\n", global_dag_stats.dag_checks);
    printf("  Max chain length: %lu\n", global_dag_stats.max_chain_length);
}

/* ========================================================================
 * Main Test Runner
 * ======================================================================== */

int main(void) {
    printf("========================================\n");
    printf("DAG Lock Ordering Unit Tests\n");
    printf("========================================\n");

    // Run all tests
    test_proper_ordering();
    test_reverse_ordering();
    test_equal_level_violation();
    test_token_reacquisition();
    test_spinlock_reacquisition();
    test_lock_release();
    test_stack_overflow();
    test_deep_chain();
    test_statistics();
    test_concurrent_validation();

    // Summary
    printf("\n========================================\n");
    printf("Test Summary\n");
    printf("========================================\n");
    printf("Passed: %d\n", tests_passed);
    printf("Failed: %d\n", tests_failed);
    printf("Total:  %d\n", tests_passed + tests_failed);

    if (tests_failed == 0) {
        printf("\n✓ All tests passed!\n");
        return 0;
    } else {
        printf("\n✗ Some tests failed!\n");
        return 1;
    }
}
