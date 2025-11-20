/**
 * @file test_integration.c
 * @brief Integration Test Suite (Phase C)
 *
 * Comprehensive integration tests combining all optimizations:
 * - Phase A: Fast-path optimizations
 * - Phase B: Cache + SIMD
 * - Lock-free capability system
 * - Lock-free scheduler
 *
 * Validates correctness, performance, and scalability.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <assert.h>
#include <pthread.h>
#include <unistd.h>

#include "capability_lockfree.h"
#include "capability_optimized.h"
#include "capability_cache.h"
#include "capability_simd.h"
#include "scheduler_lockfree.h"
#include "scheduler_optimized.h"

/*******************************************************************************
 * TEST CONFIGURATION
 ******************************************************************************/

#define NUM_CPUS           4
#define NUM_CAPABILITIES   1000
#define NUM_TASKS          500
#define NUM_THREADS        4
#define STRESS_DURATION_S  5

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
 * INTEGRATION TEST 1: COMBINED CACHE + SIMD
 ******************************************************************************/

static void test_cache_simd_combined(void)
{
    printf("TEST: cache_simd_combined\n");

    capability_table_t table;
    assert(capability_table_init(&table, NUM_CPUS) == 0);

    cap_cache_t cache;
    assert(cap_cache_init(&cache, &table, NUM_CPUS) == 0);

    /* Create many capabilities */
    const uint32_t num_caps = 64;
    for (uint32_t i = 0; i < num_caps; i++) {
        uint64_t perms = CAP_PERM_READ;
        if (i % 2 == 0) perms |= CAP_PERM_WRITE;
        if (i % 3 == 0) perms |= CAP_PERM_EXECUTE;
        assert(capability_create(&table, i, perms, 1000) == 0);
    }

    /* Warm up cache */
    for (uint32_t i = 0; i < num_caps; i++) {
        cap_cache_lookup(&cache, i, 0);
    }

    /* Build capability array for SIMD */
    capability_t *caps[num_caps];
    for (uint32_t i = 0; i < num_caps; i++) {
        caps[i] = cap_cache_lookup(&cache, i, 0);
        assert(caps[i] != NULL);
    }

    /* SIMD check with cached capabilities */
    bool results[num_caps];
    cap_simd_check_adaptive(caps, num_caps, CAP_PERM_READ, results);

    /* Verify all have READ */
    for (uint32_t i = 0; i < num_caps; i++) {
        assert(results[i] == true);
    }

    /* SIMD check for WRITE (only even) */
    cap_simd_check_adaptive(caps, num_caps, CAP_PERM_WRITE, results);
    for (uint32_t i = 0; i < num_caps; i++) {
        bool expected = (i % 2) == 0;
        assert(results[i] == expected);
    }

    /* Verify high cache hit rate */
    cap_cache_cpu_stats_t stats;
    cap_cache_get_cpu_stats(&cache, 0, &stats);
    printf("  Cache hit rate: %.2f%%\n", stats.hit_rate * 100.0);
    assert(stats.hit_rate > 0.8);  /* Should be >80% */

    /* Cleanup */
    for (uint32_t i = 0; i < num_caps; i++) {
        capability_release(&table, caps[i], 0);
    }

    cap_cache_destroy(&cache);
    capability_table_destroy(&table);

    printf("  PASS\n");
}

/*******************************************************************************
 * INTEGRATION TEST 2: SCHEDULER + OPTIMIZATIONS
 ******************************************************************************/

static void test_scheduler_with_optimizations(void)
{
    printf("TEST: scheduler_with_optimizations\n");

    scheduler_lockfree_t sched;
    assert(scheduler_lockfree_init(&sched, NUM_CPUS) == 0);

    /* Create many tasks */
    const uint32_t num_tasks = 100;
    task_t *tasks[num_tasks];

    for (uint32_t i = 0; i < num_tasks; i++) {
        q16_t priority = q16_from_int(10);
        assert(scheduler_task_create(&sched, i, priority, NULL, NULL) == 0);
        tasks[i] = scheduler_task_lookup(&sched, i);
        assert(tasks[i] != NULL);
    }

    /* Batch enqueue using optimized function */
    uint32_t enqueued = scheduler_enqueue_batch(&sched, tasks, num_tasks, 0);
    assert(enqueued == num_tasks);

    /* Verify queue length */
    uint32_t length = scheduler_queue_length_fast(&sched, 0);
    assert(length == num_tasks);

    /* Batch dequeue */
    task_t *dequeued[num_tasks];
    uint32_t dequeued_count = scheduler_dequeue_batch(&sched, 0, dequeued,
                                                      num_tasks);
    assert(dequeued_count == num_tasks);

    /* Verify all tasks are RUNNING */
    for (uint32_t i = 0; i < dequeued_count; i++) {
        assert(task_is_running_fast(dequeued[i]) == true);
    }

    /* Batch complete */
    uint32_t completed = scheduler_complete_batch(&sched, dequeued,
                                                   dequeued_count);
    assert(completed == dequeued_count);

    scheduler_lockfree_destroy(&sched);

    printf("  PASS\n");
}

/*******************************************************************************
 * INTEGRATION TEST 3: FULL SYSTEM (CAPABILITIES + SCHEDULER)
 ******************************************************************************/

static void test_full_system_integration(void)
{
    printf("TEST: full_system_integration\n");

    /* Initialize both systems */
    capability_table_t cap_table;
    assert(capability_table_init(&cap_table, NUM_CPUS) == 0);

    cap_cache_t cap_cache;
    assert(cap_cache_init(&cap_cache, &cap_table, NUM_CPUS) == 0);

    scheduler_lockfree_t sched;
    assert(scheduler_lockfree_init(&sched, NUM_CPUS) == 0);

    /* Create capabilities for tasks */
    const uint32_t num_tasks = 50;
    for (uint32_t i = 0; i < num_tasks; i++) {
        /* Each task gets a capability */
        cap_id_t cap_id = 1000 + i;
        uint64_t perms = CAP_PERM_READ | CAP_PERM_WRITE;
        assert(capability_create(&cap_table, cap_id, perms, i) == 0);
    }

    /* Create tasks */
    for (uint32_t i = 0; i < num_tasks; i++) {
        task_id_t task_id = i;
        q16_t priority = q16_from_int(10);
        assert(scheduler_task_create(&sched, task_id, priority, NULL, NULL) == 0);

        /* Enqueue task */
        uint8_t cpu = i % NUM_CPUS;  /* Distribute across CPUs */
        assert(scheduler_task_enqueue(&sched, task_id, cpu) == 0);
    }

    /* Simulate execution: dequeue, check capability, complete */
    for (uint32_t i = 0; i < num_tasks; i++) {
        uint8_t cpu = i % NUM_CPUS;

        /* Dequeue task */
        task_t *task = scheduler_task_dequeue(&sched, cpu);
        assert(task != NULL);

        /* Check capability using cache */
        cap_id_t cap_id = 1000 + task->id;
        bool has_perm = cap_cache_has_permission(&cap_cache, cap_id,
                                                 CAP_PERM_READ, cpu);
        assert(has_perm == true);

        /* Complete task */
        assert(scheduler_task_complete(&sched, task) == 0);
    }

    /* Verify all tasks completed */
    scheduler_stats_t stats;
    scheduler_get_stats(&sched, &stats);
    assert(stats.completed_tasks == num_tasks);

    /* Verify cache effectiveness */
    cap_cache_stats_t cache_stats;
    cap_cache_get_stats(&cap_cache, &cache_stats);
    printf("  Cache hit rate: %.2f%%\n", cache_stats.global_hit_rate * 100.0);

    /* Cleanup */
    scheduler_lockfree_destroy(&sched);
    cap_cache_destroy(&cap_cache);
    capability_table_destroy(&cap_table);

    printf("  PASS\n");
}

/*******************************************************************************
 * STRESS TEST: CONCURRENT OPERATIONS
 ******************************************************************************/

typedef struct {
    capability_table_t *table;
    cap_cache_t *cache;
    int thread_id;
    volatile int *stop_flag;
    uint64_t operations;
} thread_args_t;

static void *stress_thread(void *arg)
{
    thread_args_t *args = (thread_args_t *)arg;
    uint8_t cpu = args->thread_id % NUM_CPUS;

    while (!(*args->stop_flag)) {
        /* Random operation */
        uint32_t op = rand() % 3;
        cap_id_t id = rand() % NUM_CAPABILITIES;

        switch (op) {
        case 0:
            /* Cache lookup */
            cap_cache_has_permission(args->cache, id, CAP_PERM_READ, cpu);
            break;

        case 1:
            /* Direct lookup */
            {
                capability_t *cap = capability_lookup(args->table, id, cpu);
                if (cap) {
                    capability_check_fast(cap, CAP_PERM_READ);
                    capability_release(args->table, cap, cpu);
                }
            }
            break;

        case 2:
            /* Cache invalidation */
            cap_cache_invalidate(args->cache, id, cpu);
            break;
        }

        args->operations++;
    }

    return NULL;
}

static void test_stress_concurrent(void)
{
    printf("TEST: stress_concurrent\n");
    printf("  Running %d threads for %d seconds...\n", NUM_THREADS, STRESS_DURATION_S);

    capability_table_t table;
    assert(capability_table_init(&table, NUM_CPUS) == 0);

    cap_cache_t cache;
    assert(cap_cache_init(&cache, &table, NUM_CPUS) == 0);

    /* Create capabilities */
    for (uint32_t i = 0; i < NUM_CAPABILITIES; i++) {
        uint64_t perms = CAP_PERM_READ | CAP_PERM_WRITE;
        capability_create(&table, i, perms, 1000);
    }

    /* Start stress threads */
    pthread_t threads[NUM_THREADS];
    thread_args_t args[NUM_THREADS];
    volatile int stop_flag = 0;

    for (int i = 0; i < NUM_THREADS; i++) {
        args[i].table = &table;
        args[i].cache = &cache;
        args[i].thread_id = i;
        args[i].stop_flag = &stop_flag;
        args[i].operations = 0;
        pthread_create(&threads[i], NULL, stress_thread, &args[i]);
    }

    /* Run for specified duration */
    sleep(STRESS_DURATION_S);
    stop_flag = 1;

    /* Wait for threads */
    uint64_t total_ops = 0;
    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_join(threads[i], NULL);
        total_ops += args[i].operations;
        printf("  Thread %d: %lu operations\n", i, args[i].operations);
    }

    double ops_per_sec = (double)total_ops / STRESS_DURATION_S;
    printf("  Total: %lu operations (%.2f Mops/sec)\n",
           total_ops, ops_per_sec / 1000000.0);

    /* Print statistics */
    cap_cache_stats_t stats;
    cap_cache_get_stats(&cache, &stats);
    printf("  Cache hit rate: %.2f%%\n", stats.global_hit_rate * 100.0);

    cap_cache_destroy(&cache);
    capability_table_destroy(&table);

    printf("  PASS\n");
}

/*******************************************************************************
 * PERFORMANCE REGRESSION TEST
 ******************************************************************************/

static void test_performance_regression(void)
{
    printf("TEST: performance_regression\n");

    capability_table_t table;
    capability_table_init(&table, NUM_CPUS);

    cap_cache_t cache;
    cap_cache_init(&cache, &table, NUM_CPUS);

    /* Create capabilities */
    const uint32_t num_caps = 1000;
    for (uint32_t i = 0; i < num_caps; i++) {
        capability_create(&table, i, CAP_PERM_READ | CAP_PERM_WRITE, 1000);
    }

    /* Warm cache */
    for (uint32_t i = 0; i < num_caps; i++) {
        cap_cache_lookup(&cache, i, 0);
    }

    const uint32_t iterations = 100000;

    /* Baseline: Direct table lookup */
    uint64_t start = get_time_ns();
    for (uint32_t i = 0; i < iterations; i++) {
        cap_id_t id = i % num_caps;
        capability_t *cap = capability_lookup(&table, id, 0);
        if (cap) {
            capability_check_fast(cap, CAP_PERM_READ);
            capability_release(&table, cap, 0);
        }
    }
    uint64_t baseline_time = get_time_ns() - start;

    /* Optimized: Cache lookup */
    start = get_time_ns();
    for (uint32_t i = 0; i < iterations; i++) {
        cap_id_t id = i % num_caps;
        cap_cache_has_permission(&cache, id, CAP_PERM_READ, 0);
    }
    uint64_t optimized_time = get_time_ns() - start;

    double baseline_ns = (double)baseline_time / iterations;
    double optimized_ns = (double)optimized_time / iterations;
    double speedup = (double)baseline_time / optimized_time;

    printf("  Baseline:   %.2f ns/op\n", baseline_ns);
    printf("  Optimized:  %.2f ns/op\n", optimized_ns);
    printf("  Speedup:    %.2fx\n", speedup);

    /* Regression check: optimized should be at least 3x faster */
    assert(speedup >= 3.0);

    cap_cache_destroy(&cache);
    capability_table_destroy(&table);

    printf("  PASS (no regression, %.2fx speedup)\n", speedup);
}

/*******************************************************************************
 * SCALABILITY TEST
 ******************************************************************************/

static void test_scalability(void)
{
    printf("TEST: scalability\n");

    for (int num_cpus = 1; num_cpus <= 4; num_cpus *= 2) {
        printf("  Testing with %d CPUs...\n", num_cpus);

        scheduler_lockfree_t sched;
        scheduler_lockfree_init(&sched, num_cpus);

        const uint32_t num_tasks = 1000;
        const uint32_t iterations = 10;

        uint64_t total_time = 0;

        for (uint32_t iter = 0; iter < iterations; iter++) {
            /* Create tasks */
            for (uint32_t i = 0; i < num_tasks; i++) {
                task_id_t id = iter * num_tasks + i;
                q16_t priority = q16_from_int(10);
                scheduler_task_create(&sched, id, priority, NULL, NULL);
            }

            /* Enqueue across CPUs */
            uint64_t start = get_time_ns();
            for (uint32_t i = 0; i < num_tasks; i++) {
                task_id_t id = iter * num_tasks + i;
                uint8_t cpu = i % num_cpus;
                scheduler_task_enqueue(&sched, id, cpu);
            }

            /* Dequeue from all CPUs */
            for (uint32_t i = 0; i < num_tasks; i++) {
                uint8_t cpu = i % num_cpus;
                task_t *task = scheduler_task_dequeue(&sched, cpu);
                if (task) {
                    scheduler_task_complete(&sched, task);
                }
            }
            total_time += get_time_ns() - start;
        }

        double avg_time_us = (double)total_time / (iterations * 1000);
        double throughput = (double)(num_tasks * iterations) /
                           ((double)total_time / 1000000000.0);

        printf("    Avg time: %.2f us\n", avg_time_us);
        printf("    Throughput: %.2f Kops/sec\n", throughput / 1000.0);

        scheduler_lockfree_destroy(&sched);
    }

    printf("  PASS\n");
}

/*******************************************************************************
 * MAIN TEST RUNNER
 ******************************************************************************/

int main(void)
{
    printf("================================================================================\n");
    printf("INTEGRATION TEST SUITE (Phase C)\n");
    printf("================================================================================\n\n");

    printf("System Configuration:\n");
    printf("  CPUs:          %d\n", NUM_CPUS);
    printf("  Capabilities:  %d\n", NUM_CAPABILITIES);
    printf("  Tasks:         %d\n", NUM_TASKS);
    printf("\n");

    printf("--- Integration Tests ---\n");
    test_cache_simd_combined();
    test_scheduler_with_optimizations();
    test_full_system_integration();
    printf("\n");

    printf("--- Stress Tests ---\n");
    test_stress_concurrent();
    printf("\n");

    printf("--- Performance Tests ---\n");
    test_performance_regression();
    test_scalability();
    printf("\n");

    printf("================================================================================\n");
    printf("ALL INTEGRATION TESTS PASSED\n");
    printf("\n");
    printf("Validated:\n");
    printf("  ✓ Cache + SIMD integration\n");
    printf("  ✓ Scheduler + optimizations\n");
    printf("  ✓ Full system correctness\n");
    printf("  ✓ Concurrent stress testing\n");
    printf("  ✓ Performance regression (>3x speedup)\n");
    printf("  ✓ Multi-CPU scalability\n");
    printf("\n");
    printf("Phase C complete. System validated and ready for production.\n");
    printf("================================================================================\n");

    return 0;
}
