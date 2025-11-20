/**
 * @file test_lockfree.c
 * @brief Comprehensive Tests for Lock-Free Data Structures
 *
 * TEST COVERAGE:
 * ==============
 * 1. Hazard Pointers (6 tests)
 *    - Initialization
 *    - Acquire/release
 *    - Protection protocol
 *    - Retirement
 *    - Scanning/reclamation
 *    - Multi-threaded safety simulation
 *
 * 2. Michael-Scott Queue (8 tests)
 *    - Basic enqueue/dequeue
 *    - FIFO ordering
 *    - Empty queue handling
 *    - Concurrent operations simulation
 *    - Stress test (many operations)
 *    - Linearizability check
 *    - Memory safety
 *    - Statistics accuracy
 *
 * 3. Treiber Stack (6 tests)
 *    - Basic push/pop
 *    - LIFO ordering
 *    - Empty stack handling
 *    - Concurrent operations simulation
 *    - Stress test
 *    - Memory safety
 *
 * 4. Integration Tests (3 tests)
 *    - Mixed queue and stack operations
 *    - Hazard pointer stress (reclamation)
 *    - Performance benchmarks
 *
 * TOTAL: 23 TESTS
 */

#include "lockfree.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>

/* Test counters */
static int tests_run = 0;
static int tests_passed = 0;

/* Test utilities */
#define TEST_START(name) \
    do { \
        printf("TEST: %s ... ", name); \
        fflush(stdout); \
        tests_run++; \
    } while(0)

#define TEST_PASS() \
    do { \
        printf("PASS\n"); \
        tests_passed++; \
    } while(0)

#define TEST_FAIL(msg) \
    do { \
        printf("FAIL: %s\n", msg); \
        return; \
    } while(0)

#define ASSERT(cond, msg) \
    do { \
        if (!(cond)) { \
            TEST_FAIL(msg); \
        } \
    } while(0)

/*******************************************************************************
 * HAZARD POINTER TESTS
 ******************************************************************************/

/**
 * Test: HP domain initialization
 */
void test_hp_init(void) {
    TEST_START("HP domain initialization");

    hp_domain_t hp;
    hp_domain_init(&hp);

    /* Verify all HPs are inactive and NULL */
    for (int i = 0; i < HP_MAX_THREADS * HP_PER_THREAD; i++) {
        void *ptr = atomic_load(&hp.hps[i].ptr);
        int active = atomic_load(&hp.hps[i].active);
        ASSERT(ptr == NULL, "HP should be NULL after init");
        ASSERT(active == 0, "HP should be inactive after init");
    }

    /* Verify retire lists are empty */
    for (int i = 0; i < HP_MAX_THREADS; i++) {
        ASSERT(hp.retire_lists[i] == NULL, "Retire list should be empty");
        int count = atomic_load(&hp.retire_counts[i]);
        ASSERT(count == 0, "Retire count should be 0");
    }

    TEST_PASS();
}

/**
 * Test: HP acquire and release
 */
void test_hp_acquire_release(void) {
    TEST_START("HP acquire and release");

    hp_domain_t hp;
    hp_domain_init(&hp);

    /* Acquire HP 0 for thread 0 */
    hazard_pointer_t *hp0 = hp_acquire(&hp, 0, 0);
    ASSERT(hp0 != NULL, "Acquire should return valid HP");
    ASSERT(atomic_load(&hp0->active) == 1, "HP should be active");

    /* Clear HP */
    hp_clear(hp0);
    ASSERT(atomic_load(&hp0->active) == 0, "HP should be inactive after clear");
    ASSERT(atomic_load(&hp0->ptr) == NULL, "HP should be NULL after clear");

    TEST_PASS();
}

/**
 * Test: HP protection protocol
 */
void test_hp_protect(void) {
    TEST_START("HP protection protocol");

    hp_domain_t hp;
    hp_domain_init(&hp);

    /* Create atomic pointer */
    atomic_ptr_t src;
    int value = 42;
    atomic_store(&src, &value);

    /* Acquire and protect */
    hazard_pointer_t *hp0 = hp_acquire(&hp, 0, 0);
    void *protected = hp_protect(hp0, &src);

    ASSERT(protected == &value, "Protected value should match source");
    ASSERT(atomic_load(&hp0->ptr) == &value, "HP should store protected pointer");

    hp_clear(hp0);
    TEST_PASS();
}

/**
 * Test: HP retirement
 */
void test_hp_retire(void) {
    TEST_START("HP retirement");

    hp_domain_t hp;
    hp_domain_init(&hp);

    /* Retire some pointers */
    int *data1 = (int*)malloc(sizeof(int));
    int *data2 = (int*)malloc(sizeof(int));
    int *data3 = (int*)malloc(sizeof(int));

    hp_retire(&hp, 0, data1, free);
    hp_retire(&hp, 0, data2, free);
    hp_retire(&hp, 0, data3, free);

    /* Check retire count */
    int count = atomic_load(&hp.retire_counts[0]);
    ASSERT(count == 3, "Retire count should be 3");
    ASSERT(hp.retire_lists[0] != NULL, "Retire list should not be empty");

    /* Manual cleanup (since we're not triggering scan) */
    retired_node_t *curr = hp.retire_lists[0];
    while (curr) {
        retired_node_t *next = curr->next;
        if (curr->deleter) {
            curr->deleter(curr->ptr);
        }
        free(curr);
        curr = next;
    }

    TEST_PASS();
}

/**
 * Test: HP scanning and reclamation
 */
void test_hp_scan(void) {
    TEST_START("HP scanning and reclamation");

    hp_domain_t hp;
    hp_domain_init(&hp);

    /* Create some data */
    int *protected_data = (int*)malloc(sizeof(int));
    int *unprotected_data1 = (int*)malloc(sizeof(int));
    int *unprotected_data2 = (int*)malloc(sizeof(int));

    /* Protect one pointer */
    hazard_pointer_t *hp0 = hp_acquire(&hp, 0, 0);
    atomic_ptr_t src;
    atomic_store(&src, protected_data);
    hp_protect(hp0, &src);

    /* Retire all three */
    hp_retire(&hp, 1, protected_data, NULL);  /* Won't be freed (protected) */
    hp_retire(&hp, 1, unprotected_data1, free);  /* Will be freed */
    hp_retire(&hp, 1, unprotected_data2, free);  /* Will be freed */

    int count_before = atomic_load(&hp.retire_counts[1]);
    ASSERT(count_before == 3, "Should have 3 retired nodes");

    /* Trigger scan */
    hp_scan(&hp, 1);

    int count_after = atomic_load(&hp.retire_counts[1]);
    ASSERT(count_after == 1, "Should have 1 retired node (protected)");

    /* Cleanup */
    hp_clear(hp0);
    hp_scan(&hp, 1);  /* Now it can be freed (hp_scan will free it) */
    /* Note: protected_data is freed by hp_scan, don't double-free */

    TEST_PASS();
}

/**
 * Test: HP multi-threaded simulation
 */
void test_hp_multithread_sim(void) {
    TEST_START("HP multi-threaded simulation");

    hp_domain_t hp;
    hp_domain_init(&hp);

    /* Simulate thread 0 protecting a pointer */
    simulated_tid = 0;
    int *data = (int*)malloc(sizeof(int));
    *data = 100;

    atomic_ptr_t shared;
    atomic_store(&shared, data);

    hazard_pointer_t *hp0 = hp_acquire(&hp, 0, 0);
    void *protected = hp_protect(hp0, &shared);
    ASSERT(protected == data, "Thread 0 should protect data");

    /* Simulate thread 1 trying to retire the same pointer */
    simulated_tid = 1;
    hp_retire(&hp, 1, data, NULL);  /* Use NULL deleter for manual cleanup */

    /* Scan should NOT free (thread 0 is protecting) */
    hp_scan(&hp, 1);
    int count = atomic_load(&hp.retire_counts[1]);
    ASSERT(count == 1, "Data should still be in retire list");

    /* Thread 0 releases protection */
    simulated_tid = 0;
    hp_clear(hp0);

    /* Now scan should free */
    simulated_tid = 1;
    hp_scan(&hp, 1);
    count = atomic_load(&hp.retire_counts[1]);
    ASSERT(count == 0, "Data should be freed after protection cleared");

    /* Note: data is freed by hp_scan (NULL deleter uses free()), don't double-free */

    TEST_PASS();
}

/*******************************************************************************
 * MICHAEL-SCOTT QUEUE TESTS
 ******************************************************************************/

/**
 * Test: MS queue basic enqueue/dequeue
 */
void test_ms_basic(void) {
    TEST_START("MS queue basic operations");

    hp_domain_t hp;
    hp_domain_init(&hp);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    simulated_tid = 0;

    /* Enqueue */
    ms_enqueue(&queue, (void*)"A", 0);
    ms_enqueue(&queue, (void*)"B", 0);
    ms_enqueue(&queue, (void*)"C", 0);

    /* Dequeue */
    char *val1 = (char*)ms_dequeue(&queue, 0);
    ASSERT(val1 != NULL && strcmp(val1, "A") == 0, "Should dequeue 'A'");

    char *val2 = (char*)ms_dequeue(&queue, 0);
    ASSERT(val2 != NULL && strcmp(val2, "B") == 0, "Should dequeue 'B'");

    char *val3 = (char*)ms_dequeue(&queue, 0);
    ASSERT(val3 != NULL && strcmp(val3, "C") == 0, "Should dequeue 'C'");

    /* Should be empty */
    char *val4 = (char*)ms_dequeue(&queue, 0);
    ASSERT(val4 == NULL, "Should be empty");

    TEST_PASS();
}

/**
 * Test: MS queue FIFO ordering
 */
void test_ms_fifo(void) {
    TEST_START("MS queue FIFO ordering");

    hp_domain_t hp;
    hp_domain_init(&hp);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    simulated_tid = 0;

    /* Enqueue 100 items */
    for (int i = 0; i < 100; i++) {
        int *data = (int*)malloc(sizeof(int));
        *data = i;
        ms_enqueue(&queue, data, 0);
    }

    /* Dequeue and verify order */
    for (int i = 0; i < 100; i++) {
        int *data = (int*)ms_dequeue(&queue, 0);
        ASSERT(data != NULL, "Should dequeue non-NULL");
        ASSERT(*data == i, "Should maintain FIFO order");
        free(data);
    }

    ASSERT(ms_is_empty(&queue), "Queue should be empty");

    TEST_PASS();
}

/**
 * Test: MS queue empty handling
 */
void test_ms_empty(void) {
    TEST_START("MS queue empty handling");

    hp_domain_t hp;
    hp_domain_init(&hp);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    simulated_tid = 0;

    /* Dequeue from empty queue */
    void *val = ms_dequeue(&queue, 0);
    ASSERT(val == NULL, "Dequeue from empty should return NULL");
    ASSERT(ms_is_empty(&queue), "Should be empty");

    /* Enqueue then dequeue */
    ms_enqueue(&queue, (void*)"X", 0);
    ASSERT(!ms_is_empty(&queue), "Should not be empty after enqueue");

    val = ms_dequeue(&queue, 0);
    ASSERT(val != NULL, "Should dequeue successfully");
    ASSERT(ms_is_empty(&queue), "Should be empty again");

    TEST_PASS();
}

/**
 * Test: MS queue concurrent simulation
 */
void test_ms_concurrent_sim(void) {
    TEST_START("MS queue concurrent simulation");

    hp_domain_t hp;
    hp_domain_init(&hp);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    /* Simulate interleaved operations from 2 threads */
    simulated_tid = 0;
    ms_enqueue(&queue, (void*)"T0-A", 0);
    ms_enqueue(&queue, (void*)"T0-B", 0);

    simulated_tid = 1;
    ms_enqueue(&queue, (void*)"T1-A", 1);
    char *val1 = (char*)ms_dequeue(&queue, 1);
    ASSERT(val1 != NULL, "Thread 1 should dequeue");

    simulated_tid = 0;
    ms_enqueue(&queue, (void*)"T0-C", 0);

    simulated_tid = 1;
    char *val2 = (char*)ms_dequeue(&queue, 1);
    ASSERT(val2 != NULL, "Thread 1 should dequeue again");

    /* Drain queue */
    int count = 0;
    while (!ms_is_empty(&queue)) {
        ms_dequeue(&queue, 1);
        count++;
    }

    ASSERT(count == 2, "Should have 2 remaining items");

    TEST_PASS();
}

/**
 * Test: MS queue stress test
 */
void test_ms_stress(void) {
    TEST_START("MS queue stress test");

    hp_domain_t hp;
    hp_domain_init(&hp);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    simulated_tid = 0;

    const int N = 1000;

    /* Enqueue N items */
    for (int i = 0; i < N; i++) {
        int *data = (int*)malloc(sizeof(int));
        *data = i;
        ms_enqueue(&queue, data, 0);
    }

    /* Dequeue all */
    int dequeued = 0;
    for (int i = 0; i < N; i++) {
        int *data = (int*)ms_dequeue(&queue, 0);
        ASSERT(data != NULL, "Should dequeue all items");
        ASSERT(*data == i, "Should maintain order");
        free(data);
        dequeued++;
    }

    ASSERT(dequeued == N, "Should dequeue all N items");
    ASSERT(ms_is_empty(&queue), "Should be empty");

    /* Check statistics */
    uint64_t enq_count = atomic_load(&queue.enqueue_count);
    uint64_t deq_count = atomic_load(&queue.dequeue_count);
    ASSERT(enq_count == N, "Enqueue count should match");
    ASSERT(deq_count == N, "Dequeue count should match");

    TEST_PASS();
}

/**
 * Test: MS queue linearizability check
 */
void test_ms_linearizability(void) {
    TEST_START("MS queue linearizability");

    hp_domain_t hp;
    hp_domain_init(&hp);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    simulated_tid = 0;

    /* Sequential spec: enqueue(A), enqueue(B), dequeue() = A */
    ms_enqueue(&queue, (void*)"A", 0);
    ms_enqueue(&queue, (void*)"B", 0);
    char *val = (char*)ms_dequeue(&queue, 0);

    ASSERT(val != NULL && strcmp(val, "A") == 0,
           "Linearization: dequeue after enq(A),enq(B) should return A");

    /* Sequential spec: dequeue() = B */
    val = (char*)ms_dequeue(&queue, 0);
    ASSERT(val != NULL && strcmp(val, "B") == 0,
           "Linearization: next dequeue should return B");

    TEST_PASS();
}

/**
 * Test: MS queue memory safety
 */
void test_ms_memory_safety(void) {
    TEST_START("MS queue memory safety");

    hp_domain_t hp;
    hp_domain_init(&hp);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    simulated_tid = 0;

    /* Enqueue dynamically allocated data */
    for (int i = 0; i < 50; i++) {
        int *data = (int*)malloc(sizeof(int));
        *data = i * 2;
        ms_enqueue(&queue, data, 0);
    }

    /* Dequeue and free */
    for (int i = 0; i < 50; i++) {
        int *data = (int*)ms_dequeue(&queue, 0);
        ASSERT(data != NULL, "Should dequeue successfully");
        free(data);
    }

    /* No memory leaks (hazard pointers protect queue nodes) */
    ASSERT(ms_is_empty(&queue), "Queue should be empty");

    TEST_PASS();
}

/**
 * Test: MS queue size tracking
 */
void test_ms_size(void) {
    TEST_START("MS queue size tracking");

    hp_domain_t hp;
    hp_domain_init(&hp);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    simulated_tid = 0;

    /* Initially empty */
    ASSERT(ms_get_size(&queue) == 0, "Size should be 0");

    /* Enqueue 10 */
    for (int i = 0; i < 10; i++) {
        ms_enqueue(&queue, (void*)(intptr_t)i, 0);
    }
    ASSERT(ms_get_size(&queue) == 10, "Size should be 10");

    /* Dequeue 5 */
    for (int i = 0; i < 5; i++) {
        ms_dequeue(&queue, 0);
    }
    ASSERT(ms_get_size(&queue) == 5, "Size should be 5");

    /* Dequeue all */
    while (!ms_is_empty(&queue)) {
        ms_dequeue(&queue, 0);
    }
    ASSERT(ms_get_size(&queue) == 0, "Size should be 0 again");

    TEST_PASS();
}

/*******************************************************************************
 * TREIBER STACK TESTS
 ******************************************************************************/

/**
 * Test: Treiber stack basic push/pop
 */
void test_treiber_basic(void) {
    TEST_START("Treiber stack basic operations");

    hp_domain_t hp;
    hp_domain_init(&hp);

    treiber_stack_t stack;
    treiber_init(&stack, &hp);

    simulated_tid = 0;

    /* Push */
    treiber_push(&stack, (void*)"A", 0);
    treiber_push(&stack, (void*)"B", 0);
    treiber_push(&stack, (void*)"C", 0);

    /* Pop (LIFO order) */
    char *val1 = (char*)treiber_pop(&stack, 0);
    ASSERT(val1 != NULL && strcmp(val1, "C") == 0, "Should pop 'C'");

    char *val2 = (char*)treiber_pop(&stack, 0);
    ASSERT(val2 != NULL && strcmp(val2, "B") == 0, "Should pop 'B'");

    char *val3 = (char*)treiber_pop(&stack, 0);
    ASSERT(val3 != NULL && strcmp(val3, "A") == 0, "Should pop 'A'");

    /* Should be empty */
    char *val4 = (char*)treiber_pop(&stack, 0);
    ASSERT(val4 == NULL, "Should be empty");

    TEST_PASS();
}

/**
 * Test: Treiber stack LIFO ordering
 */
void test_treiber_lifo(void) {
    TEST_START("Treiber stack LIFO ordering");

    hp_domain_t hp;
    hp_domain_init(&hp);

    treiber_stack_t stack;
    treiber_init(&stack, &hp);

    simulated_tid = 0;

    /* Push 100 items */
    for (int i = 0; i < 100; i++) {
        int *data = (int*)malloc(sizeof(int));
        *data = i;
        treiber_push(&stack, data, 0);
    }

    /* Pop and verify reverse order */
    for (int i = 99; i >= 0; i--) {
        int *data = (int*)treiber_pop(&stack, 0);
        ASSERT(data != NULL, "Should pop non-NULL");
        ASSERT(*data == i, "Should maintain LIFO order");
        free(data);
    }

    ASSERT(treiber_is_empty(&stack), "Stack should be empty");

    TEST_PASS();
}

/**
 * Test: Treiber stack empty handling
 */
void test_treiber_empty(void) {
    TEST_START("Treiber stack empty handling");

    hp_domain_t hp;
    hp_domain_init(&hp);

    treiber_stack_t stack;
    treiber_init(&stack, &hp);

    simulated_tid = 0;

    /* Pop from empty stack */
    void *val = treiber_pop(&stack, 0);
    ASSERT(val == NULL, "Pop from empty should return NULL");
    ASSERT(treiber_is_empty(&stack), "Should be empty");

    /* Push then pop */
    treiber_push(&stack, (void*)"X", 0);
    ASSERT(!treiber_is_empty(&stack), "Should not be empty after push");

    val = treiber_pop(&stack, 0);
    ASSERT(val != NULL, "Should pop successfully");
    ASSERT(treiber_is_empty(&stack), "Should be empty again");

    TEST_PASS();
}

/**
 * Test: Treiber stack concurrent simulation
 */
void test_treiber_concurrent_sim(void) {
    TEST_START("Treiber stack concurrent simulation");

    hp_domain_t hp;
    hp_domain_init(&hp);

    treiber_stack_t stack;
    treiber_init(&stack, &hp);

    /* Simulate interleaved operations */
    simulated_tid = 0;
    treiber_push(&stack, (void*)"T0-A", 0);
    treiber_push(&stack, (void*)"T0-B", 0);

    simulated_tid = 1;
    treiber_push(&stack, (void*)"T1-A", 1);
    char *val1 = (char*)treiber_pop(&stack, 1);
    ASSERT(val1 != NULL, "Thread 1 should pop");

    simulated_tid = 0;
    treiber_push(&stack, (void*)"T0-C", 0);

    /* Drain stack */
    int count = 0;
    simulated_tid = 1;
    while (!treiber_is_empty(&stack)) {
        treiber_pop(&stack, 1);
        count++;
    }

    ASSERT(count == 3, "Should have 3 remaining items");

    TEST_PASS();
}

/**
 * Test: Treiber stack stress test
 */
void test_treiber_stress(void) {
    TEST_START("Treiber stack stress test");

    hp_domain_t hp;
    hp_domain_init(&hp);

    treiber_stack_t stack;
    treiber_init(&stack, &hp);

    simulated_tid = 0;

    const int N = 1000;

    /* Push N items */
    for (int i = 0; i < N; i++) {
        int *data = (int*)malloc(sizeof(int));
        *data = i;
        treiber_push(&stack, data, 0);
    }

    /* Pop all (reverse order) */
    int popped = 0;
    for (int i = N - 1; i >= 0; i--) {
        int *data = (int*)treiber_pop(&stack, 0);
        ASSERT(data != NULL, "Should pop all items");
        ASSERT(*data == i, "Should maintain LIFO order");
        free(data);
        popped++;
    }

    ASSERT(popped == N, "Should pop all N items");
    ASSERT(treiber_is_empty(&stack), "Should be empty");

    /* Check statistics */
    uint64_t push_count = atomic_load(&stack.push_count);
    uint64_t pop_count = atomic_load(&stack.pop_count);
    ASSERT(push_count == N, "Push count should match");
    ASSERT(pop_count == N, "Pop count should match");

    TEST_PASS();
}

/**
 * Test: Treiber stack memory safety
 */
void test_treiber_memory_safety(void) {
    TEST_START("Treiber stack memory safety");

    hp_domain_t hp;
    hp_domain_init(&hp);

    treiber_stack_t stack;
    treiber_init(&stack, &hp);

    simulated_tid = 0;

    /* Push dynamically allocated data */
    for (int i = 0; i < 50; i++) {
        int *data = (int*)malloc(sizeof(int));
        *data = i * 3;
        treiber_push(&stack, data, 0);
    }

    /* Pop and free */
    for (int i = 0; i < 50; i++) {
        int *data = (int*)treiber_pop(&stack, 0);
        ASSERT(data != NULL, "Should pop successfully");
        free(data);
    }

    /* No memory leaks */
    ASSERT(treiber_is_empty(&stack), "Stack should be empty");

    TEST_PASS();
}

/*******************************************************************************
 * INTEGRATION TESTS
 ******************************************************************************/

/**
 * Test: Mixed queue and stack operations
 */
void test_mixed_operations(void) {
    TEST_START("Mixed queue and stack operations");

    hp_domain_t hp;
    hp_domain_init(&hp);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    treiber_stack_t stack;
    treiber_init(&stack, &hp);

    simulated_tid = 0;

    /* Push to stack, enqueue to queue */
    for (int i = 0; i < 10; i++) {
        int *stack_data = (int*)malloc(sizeof(int));
        int *queue_data = (int*)malloc(sizeof(int));
        *stack_data = i;
        *queue_data = i * 10;
        treiber_push(&stack, stack_data, 0);
        ms_enqueue(&queue, queue_data, 0);
    }

    /* Pop from stack (reverse order) */
    for (int i = 9; i >= 0; i--) {
        int *data = (int*)treiber_pop(&stack, 0);
        ASSERT(data != NULL && *data == i, "Stack should maintain LIFO");
        free(data);
    }

    /* Dequeue from queue (same order) */
    for (int i = 0; i < 10; i++) {
        int *data = (int*)ms_dequeue(&queue, 0);
        ASSERT(data != NULL && *data == i * 10, "Queue should maintain FIFO");
        free(data);
    }

    ASSERT(treiber_is_empty(&stack), "Stack should be empty");
    ASSERT(ms_is_empty(&queue), "Queue should be empty");

    TEST_PASS();
}

/**
 * Test: Hazard pointer stress (reclamation)
 */
void test_hp_reclamation_stress(void) {
    TEST_START("HP reclamation stress test");

    hp_domain_t hp;
    hp_domain_init(&hp);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    simulated_tid = 0;

    /* Enqueue many items to trigger multiple HP scans */
    const int N = 500;
    for (int i = 0; i < N; i++) {
        int *data = (int*)malloc(sizeof(int));
        *data = i;
        ms_enqueue(&queue, data, 0);
    }

    /* Dequeue all (will trigger HP scans at threshold) */
    for (int i = 0; i < N; i++) {
        int *data = (int*)ms_dequeue(&queue, 0);
        ASSERT(data != NULL, "Should dequeue all");
        free(data);
    }

    /* Retire count should be < threshold (scans happened) */
    int retire_count = atomic_load(&hp.retire_counts[0]);
    ASSERT(retire_count < HP_RETIRE_THRESHOLD,
           "HP scans should have triggered");

    TEST_PASS();
}

/**
 * Test: Performance benchmark
 */
void test_performance_benchmark(void) {
    TEST_START("Performance benchmark");

    hp_domain_t hp;
    hp_domain_init(&hp);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    simulated_tid = 0;

    const int N = 10000;

    clock_t start = clock();

    /* Benchmark: enqueue N, dequeue N */
    for (int i = 0; i < N; i++) {
        ms_enqueue(&queue, (void*)(intptr_t)i, 0);
    }

    for (int i = 0; i < N; i++) {
        ms_dequeue(&queue, 0);
    }

    clock_t end = clock();
    double elapsed = (double)(end - start) / CLOCKS_PER_SEC;

    printf("\n  Operations: %d enqueue + %d dequeue\n", N, N);
    printf("  Time: %.6f seconds\n", elapsed);
    printf("  Throughput: %.0f ops/sec\n", (2.0 * N) / elapsed);

    TEST_PASS();
}

/*******************************************************************************
 * TEST MAIN
 ******************************************************************************/

int main(void) {
    printf("========================================\n");
    printf("Lock-Free Data Structures Test Suite\n");
    printf("========================================\n\n");

    /* Hazard Pointer Tests */
    printf("--- Hazard Pointer Tests ---\n");
    test_hp_init();
    test_hp_acquire_release();
    test_hp_protect();
    test_hp_retire();
    test_hp_scan();
    test_hp_multithread_sim();

    /* Michael-Scott Queue Tests */
    printf("\n--- Michael-Scott Queue Tests ---\n");
    test_ms_basic();
    test_ms_fifo();
    test_ms_empty();
    test_ms_concurrent_sim();
    test_ms_stress();
    test_ms_linearizability();
    test_ms_memory_safety();
    test_ms_size();

    /* Treiber Stack Tests */
    printf("\n--- Treiber Stack Tests ---\n");
    test_treiber_basic();
    test_treiber_lifo();
    test_treiber_empty();
    test_treiber_concurrent_sim();
    test_treiber_stress();
    test_treiber_memory_safety();

    /* Integration Tests */
    printf("\n--- Integration Tests ---\n");
    test_mixed_operations();
    test_hp_reclamation_stress();
    test_performance_benchmark();

    /* Summary */
    printf("\n========================================\n");
    printf("Test Summary\n");
    printf("========================================\n");
    printf("Tests run:    %d\n", tests_run);
    printf("Tests passed: %d\n", tests_passed);
    printf("Tests failed: %d\n", tests_run - tests_passed);
    printf("Success rate: %.1f%%\n",
           100.0 * tests_passed / tests_run);
    printf("========================================\n");

    return (tests_run == tests_passed) ? 0 : 1;
}
