/**
 * @file test_optimized.c
 * @brief Test Suite for Optimized Operations (Phase A)
 *
 * Tests fast-path optimizations for capability and scheduler systems.
 * Validates correctness and measures performance improvements.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <assert.h>

#include "capability_lockfree.h"
#include "capability_optimized.h"
#include "scheduler_lockfree.h"
#include "scheduler_optimized.h"

/*******************************************************************************
 * TEST CONFIGURATION
 ******************************************************************************/

#define NUM_TEST_CAPS    100
#define NUM_TEST_TASKS   200
#define NUM_BATCH_OPS    50
#define NUM_CPUS         4

/*******************************************************************************
 * TIMING UTILITIES
 ******************************************************************************/

static uint64_t get_time_ns(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + ts.tv_nsec;
}

/*******************************************************************************
 * CAPABILITY OPTIMIZATION TESTS
 ******************************************************************************/

static void test_capability_check_fast(void)
{
    printf("TEST: capability_check_fast\n");

    capability_table_t table;
    assert(capability_table_init(&table, NUM_CPUS) == 0);

    /* Create test capability */
    cap_id_t id = 42;
    uint64_t perms = CAP_PERM_READ | CAP_PERM_WRITE;
    assert(capability_create(&table, id, perms, 1000) == 0);

    /* Lookup */
    capability_t *cap = capability_lookup(&table, id, 0);
    assert(cap != NULL);

    /* Test fast check - should succeed */
    assert(capability_check_fast(cap, CAP_PERM_READ) == true);
    assert(capability_check_fast(cap, CAP_PERM_WRITE) == true);
    assert(capability_check_fast(cap, CAP_PERM_EXECUTE) == false);

    /* Test combined permissions */
    assert(capability_check_fast(cap, CAP_PERM_READ | CAP_PERM_WRITE) == true);

    /* Test NULL handling */
    assert(capability_check_fast(NULL, CAP_PERM_READ) == false);

    capability_release(&table, cap, 0);
    capability_table_destroy(&table);

    printf("  PASS\n");
}

static void test_capability_check_batch(void)
{
    printf("TEST: capability_check_batch\n");

    capability_table_t table;
    assert(capability_table_init(&table, NUM_CPUS) == 0);

    /* Create multiple capabilities */
    capability_t *caps[NUM_BATCH_OPS];
    for (uint32_t i = 0; i < NUM_BATCH_OPS; i++) {
        cap_id_t id = 1000 + i;
        uint64_t perms = (i % 2) ? CAP_PERM_READ : CAP_PERM_READ | CAP_PERM_WRITE;
        assert(capability_create(&table, id, perms, 1000) == 0);
        caps[i] = capability_lookup(&table, id, 0);
        assert(caps[i] != NULL);
    }

    /* Batch check for READ permission */
    bool results[NUM_BATCH_OPS];
    capability_check_batch(caps, NUM_BATCH_OPS, CAP_PERM_READ, results);

    /* Verify all have READ */
    for (uint32_t i = 0; i < NUM_BATCH_OPS; i++) {
        assert(results[i] == true);
    }

    /* Batch check for WRITE permission */
    capability_check_batch(caps, NUM_BATCH_OPS, CAP_PERM_WRITE, results);

    /* Verify only even indices have WRITE */
    for (uint32_t i = 0; i < NUM_BATCH_OPS; i++) {
        bool expected = (i % 2) == 0;
        assert(results[i] == expected);
    }

    /* Cleanup */
    for (uint32_t i = 0; i < NUM_BATCH_OPS; i++) {
        capability_release(&table, caps[i], 0);
    }
    capability_table_destroy(&table);

    printf("  PASS\n");
}

static void test_capability_check_all_any(void)
{
    printf("TEST: capability_check_all/any\n");

    capability_table_t table;
    assert(capability_table_init(&table, NUM_CPUS) == 0);

    /* Create capabilities with different permissions */
    capability_t *caps[10];
    for (uint32_t i = 0; i < 10; i++) {
        cap_id_t id = 2000 + i;
        uint64_t perms = CAP_PERM_READ;
        if (i >= 5) perms |= CAP_PERM_WRITE;  /* Last 5 have WRITE */
        assert(capability_create(&table, id, perms, 1000) == 0);
        caps[i] = capability_lookup(&table, id, 0);
        assert(caps[i] != NULL);
    }

    /* Test check_all for READ - should pass */
    assert(capability_check_all(caps, 10, CAP_PERM_READ) == true);

    /* Test check_all for WRITE - should fail (first 5 don't have it) */
    assert(capability_check_all(caps, 10, CAP_PERM_WRITE) == false);

    /* Test check_any for WRITE - should pass (last 5 have it) */
    assert(capability_check_any(caps, 10, CAP_PERM_WRITE) == true);

    /* Test check_any for EXECUTE - should fail (none have it) */
    assert(capability_check_any(caps, 10, CAP_PERM_EXECUTE) == false);

    /* Test count */
    uint32_t count = capability_count_with_permission(caps, 10, CAP_PERM_WRITE);
    assert(count == 5);

    /* Cleanup */
    for (uint32_t i = 0; i < 10; i++) {
        capability_release(&table, caps[i], 0);
    }
    capability_table_destroy(&table);

    printf("  PASS\n");
}

/*******************************************************************************
 * SCHEDULER OPTIMIZATION TESTS
 ******************************************************************************/

static void test_task_is_state_fast(void)
{
    printf("TEST: task_is_state_fast\n");

    scheduler_lockfree_t sched;
    assert(scheduler_lockfree_init(&sched, NUM_CPUS) == 0);

    /* Create task */
    task_id_t id = 100;
    q16_t priority = q16_from_int(10);
    assert(scheduler_task_create(&sched, id, priority, NULL, NULL) == 0);

    /* Lookup task */
    task_t *task = scheduler_task_lookup(&sched, id);
    assert(task != NULL);

    /* Test state checks */
    assert(task_is_state_fast(task, TASK_STATE_NEW) == true);
    assert(task_is_ready_fast(task) == false);
    assert(task_is_running_fast(task) == false);

    /* Enqueue (NEW -> READY) */
    assert(scheduler_task_enqueue(&sched, id, 0) == 0);
    assert(task_is_ready_fast(task) == true);

    /* Dequeue (READY -> RUNNING) */
    task_t *dequeued = scheduler_task_dequeue(&sched, 0);
    assert(dequeued == task);
    assert(task_is_running_fast(task) == true);

    /* Complete */
    assert(scheduler_task_complete(&sched, task) == 0);

    scheduler_lockfree_destroy(&sched);

    printf("  PASS\n");
}

static void test_scheduler_queue_length_fast(void)
{
    printf("TEST: scheduler_queue_length_fast\n");

    scheduler_lockfree_t sched;
    assert(scheduler_lockfree_init(&sched, NUM_CPUS) == 0);

    /* Initially empty */
    assert(scheduler_queue_length_fast(&sched, 0) == 0);
    assert(scheduler_cpu_is_idle_fast(&sched, 0) == true);

    /* Create and enqueue tasks */
    for (uint32_t i = 0; i < 10; i++) {
        task_id_t id = 200 + i;
        q16_t priority = q16_from_int(10);
        assert(scheduler_task_create(&sched, id, priority, NULL, NULL) == 0);
        assert(scheduler_task_enqueue(&sched, id, 0) == 0);
    }

    /* Check queue length */
    uint32_t length = scheduler_queue_length_fast(&sched, 0);
    assert(length == 10);
    assert(scheduler_cpu_is_idle_fast(&sched, 0) == false);

    /* Check total */
    uint32_t total = scheduler_total_queue_length_fast(&sched);
    assert(total == 10);

    scheduler_lockfree_destroy(&sched);

    printf("  PASS\n");
}

static void test_scheduler_enqueue_batch(void)
{
    printf("TEST: scheduler_enqueue_batch\n");

    scheduler_lockfree_t sched;
    assert(scheduler_lockfree_init(&sched, NUM_CPUS) == 0);

    /* Create tasks */
    task_t *tasks[NUM_BATCH_OPS];
    for (uint32_t i = 0; i < NUM_BATCH_OPS; i++) {
        task_id_t id = 300 + i;
        q16_t priority = q16_from_int(10);
        assert(scheduler_task_create(&sched, id, priority, NULL, NULL) == 0);
        tasks[i] = scheduler_task_lookup(&sched, id);
        assert(tasks[i] != NULL);
    }

    /* Batch enqueue */
    uint32_t enqueued = scheduler_enqueue_batch(&sched, tasks, NUM_BATCH_OPS, 0);
    assert(enqueued == NUM_BATCH_OPS);

    /* Verify queue length */
    uint32_t length = scheduler_queue_length_fast(&sched, 0);
    assert(length == NUM_BATCH_OPS);

    scheduler_lockfree_destroy(&sched);

    printf("  PASS\n");
}

static void test_scheduler_dequeue_batch(void)
{
    printf("TEST: scheduler_dequeue_batch\n");

    scheduler_lockfree_t sched;
    assert(scheduler_lockfree_init(&sched, NUM_CPUS) == 0);

    /* Create and enqueue tasks */
    for (uint32_t i = 0; i < NUM_BATCH_OPS; i++) {
        task_id_t id = 400 + i;
        q16_t priority = q16_from_int(10);
        assert(scheduler_task_create(&sched, id, priority, NULL, NULL) == 0);
        assert(scheduler_task_enqueue(&sched, id, 0) == 0);
    }

    /* Batch dequeue */
    task_t *tasks[NUM_BATCH_OPS];
    uint32_t dequeued = scheduler_dequeue_batch(&sched, 0, tasks, NUM_BATCH_OPS);
    assert(dequeued == NUM_BATCH_OPS);

    /* Verify all tasks dequeued */
    for (uint32_t i = 0; i < dequeued; i++) {
        assert(tasks[i] != NULL);
        assert(task_is_running_fast(tasks[i]) == true);
    }

    /* Queue should be empty */
    assert(scheduler_queue_length_fast(&sched, 0) == 0);

    scheduler_lockfree_destroy(&sched);

    printf("  PASS\n");
}

static void test_scheduler_find_least_most_loaded(void)
{
    printf("TEST: scheduler_find_least/most_loaded_cpu_fast\n");

    scheduler_lockfree_t sched;
    assert(scheduler_lockfree_init(&sched, NUM_CPUS) == 0);

    /* Enqueue different numbers to each CPU */
    for (uint8_t cpu = 0; cpu < NUM_CPUS; cpu++) {
        uint32_t num_tasks = cpu * 5;  /* CPU 0: 0, CPU 1: 5, CPU 2: 10, CPU 3: 15 */
        for (uint32_t i = 0; i < num_tasks; i++) {
            task_id_t id = 500 + cpu * 100 + i;
            q16_t priority = q16_from_int(10);
            assert(scheduler_task_create(&sched, id, priority, NULL, NULL) == 0);
            assert(scheduler_task_enqueue(&sched, id, cpu) == 0);
        }
    }

    /* Find least loaded (should be CPU 0) */
    uint8_t least = scheduler_find_least_loaded_cpu_fast(&sched);
    assert(least == 0);

    /* Find most loaded (should be CPU 3) */
    uint8_t most = scheduler_find_most_loaded_cpu_fast(&sched);
    assert(most == NUM_CPUS - 1);

    /* Test balancing heuristic */
    bool needs_balancing = scheduler_needs_balancing_fast(&sched);
    assert(needs_balancing == true);  /* Imbalanced distribution */

    scheduler_lockfree_destroy(&sched);

    printf("  PASS\n");
}

/*******************************************************************************
 * PERFORMANCE BENCHMARKS
 ******************************************************************************/

static void benchmark_capability_fast_vs_normal(void)
{
    printf("BENCHMARK: capability_check_fast vs normal\n");

    capability_table_t table;
    capability_table_init(&table, NUM_CPUS);

    /* Create capability */
    cap_id_t id = 1;
    capability_create(&table, id, CAP_PERM_READ | CAP_PERM_WRITE, 1000);
    capability_t *cap = capability_lookup(&table, id, 0);

    const uint32_t iterations = 1000000;

    /* Benchmark fast path */
    uint64_t start = get_time_ns();
    for (uint32_t i = 0; i < iterations; i++) {
        capability_check_fast(cap, CAP_PERM_READ);
    }
    uint64_t fast_time = get_time_ns() - start;

    /* Benchmark normal path */
    start = get_time_ns();
    for (uint32_t i = 0; i < iterations; i++) {
        capability_has_permission(cap, CAP_PERM_READ);
    }
    uint64_t normal_time = get_time_ns() - start;

    double fast_avg_ns = (double)fast_time / iterations;
    double normal_avg_ns = (double)normal_time / iterations;
    double speedup = normal_avg_ns / fast_avg_ns;

    printf("  Fast path:   %.2f ns/op\n", fast_avg_ns);
    printf("  Normal path: %.2f ns/op\n", normal_avg_ns);
    printf("  Speedup:     %.2fx\n", speedup);

    capability_release(&table, cap, 0);
    capability_table_destroy(&table);
}

static void benchmark_scheduler_batch_enqueue(void)
{
    printf("BENCHMARK: scheduler_enqueue_batch vs individual\n");

    scheduler_lockfree_t sched;
    scheduler_lockfree_init(&sched, NUM_CPUS);

    const uint32_t num_tasks = 1000;
    const uint32_t iterations = 100;

    /* Create tasks */
    task_t *tasks[num_tasks];
    for (uint32_t i = 0; i < num_tasks; i++) {
        task_id_t id = i;
        q16_t priority = q16_from_int(10);
        scheduler_task_create(&sched, id, priority, NULL, NULL);
        tasks[i] = scheduler_task_lookup(&sched, id);
    }

    /* Benchmark batch enqueue */
    uint64_t start = get_time_ns();
    for (uint32_t iter = 0; iter < iterations; iter++) {
        scheduler_enqueue_batch(&sched, tasks, num_tasks, 0);
        /* Drain queue */
        for (uint32_t i = 0; i < num_tasks; i++) {
            scheduler_task_dequeue(&sched, 0);
        }
    }
    uint64_t batch_time = get_time_ns() - start;

    /* Benchmark individual enqueue */
    start = get_time_ns();
    for (uint32_t iter = 0; iter < iterations; iter++) {
        for (uint32_t i = 0; i < num_tasks; i++) {
            scheduler_task_enqueue(&sched, tasks[i]->id, 0);
        }
        /* Drain queue */
        for (uint32_t i = 0; i < num_tasks; i++) {
            scheduler_task_dequeue(&sched, 0);
        }
    }
    uint64_t individual_time = get_time_ns() - start;

    double batch_avg_us = (double)batch_time / (iterations * 1000);
    double individual_avg_us = (double)individual_time / (iterations * 1000);
    double speedup = (double)individual_time / batch_time;

    printf("  Batch:      %.2f us/batch (%d tasks)\n", batch_avg_us, num_tasks);
    printf("  Individual: %.2f us/batch (%d tasks)\n", individual_avg_us, num_tasks);
    printf("  Speedup:    %.2fx\n", speedup);

    scheduler_lockfree_destroy(&sched);
}

/*******************************************************************************
 * MAIN TEST RUNNER
 ******************************************************************************/

int main(void)
{
    printf("================================================================================\n");
    printf("OPTIMIZED OPERATIONS TEST SUITE (Phase A)\n");
    printf("================================================================================\n\n");

    printf("--- Capability Optimization Tests ---\n");
    test_capability_check_fast();
    test_capability_check_batch();
    test_capability_check_all_any();
    printf("\n");

    printf("--- Scheduler Optimization Tests ---\n");
    test_task_is_state_fast();
    test_scheduler_queue_length_fast();
    test_scheduler_enqueue_batch();
    test_scheduler_dequeue_batch();
    test_scheduler_find_least_most_loaded();
    printf("\n");

    printf("--- Performance Benchmarks ---\n");
    benchmark_capability_fast_vs_normal();
    benchmark_scheduler_batch_enqueue();
    printf("\n");

    printf("================================================================================\n");
    printf("ALL TESTS PASSED\n");
    printf("Phase A optimizations validated successfully.\n");
    printf("Expected improvements: 10-30%% on hot paths\n");
    printf("================================================================================\n");

    return 0;
}
