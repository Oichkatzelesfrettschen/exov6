/**
 * @file test_cache_simd.c
 * @brief Test Suite for Cache and SIMD Optimizations (Phase B)
 *
 * Tests cache and SIMD-accelerated operations.
 * Validates correctness and measures performance improvements.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <assert.h>

#include "capability_lockfree.h"
#include "capability_optimized.h"
#include "capability_cache.h"
#include "capability_simd.h"

/*******************************************************************************
 * TEST CONFIGURATION
 ******************************************************************************/

#define NUM_TEST_CAPS    100
#define NUM_CPUS         4
#define NUM_CACHE_OPS    10000

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
 * CACHE TESTS
 ******************************************************************************/

static void test_cache_init_destroy(void)
{
    printf("TEST: cache_init_destroy\n");

    capability_table_t table;
    assert(capability_table_init(&table, NUM_CPUS) == 0);

    cap_cache_t cache;
    assert(cap_cache_init(&cache, &table, NUM_CPUS) == 0);

    /* Verify cache is initialized */
    assert(cache.num_cpus == NUM_CPUS);
    assert(cache.table == &table);

    cap_cache_destroy(&cache);
    capability_table_destroy(&table);

    printf("  PASS\n");
}

static void test_cache_lookup_hit_miss(void)
{
    printf("TEST: cache_lookup_hit_miss\n");

    capability_table_t table;
    assert(capability_table_init(&table, NUM_CPUS) == 0);

    cap_cache_t cache;
    assert(cap_cache_init(&cache, &table, NUM_CPUS) == 0);

    /* Create capability */
    cap_id_t id = 42;
    uint64_t perms = CAP_PERM_READ | CAP_PERM_WRITE;
    assert(capability_create(&table, id, perms, 1000) == 0);

    uint8_t cpu = 0;

    /* First lookup - should be cache miss */
    uint64_t cached_perms;
    cap_state_t cached_state;
    assert(cap_cache_lookup_fast(&cache, id, cpu, &cached_perms, &cached_state) == false);

    /* Lookup via table and insert into cache */
    capability_t *cap = cap_cache_lookup(&cache, id, cpu);
    assert(cap != NULL);

    /* Second lookup - should be cache hit */
    assert(cap_cache_lookup_fast(&cache, id, cpu, &cached_perms, &cached_state) == true);
    assert(cached_perms == perms);
    assert(cached_state == CAP_STATE_ACTIVE);

    /* Verify statistics */
    cap_cache_cpu_stats_t stats;
    cap_cache_get_cpu_stats(&cache, cpu, &stats);
    assert(stats.hits == 1);
    assert(stats.misses == 1);

    capability_release(&table, cap, cpu);
    cap_cache_destroy(&cache);
    capability_table_destroy(&table);

    printf("  PASS\n");
}

static void test_cache_invalidation(void)
{
    printf("TEST: cache_invalidation\n");

    capability_table_t table;
    assert(capability_table_init(&table, NUM_CPUS) == 0);

    cap_cache_t cache;
    assert(cap_cache_init(&cache, &table, NUM_CPUS) == 0);

    /* Create and cache capability */
    cap_id_t id = 100;
    assert(capability_create(&table, id, CAP_PERM_READ, 1000) == 0);

    capability_t *cap = cap_cache_lookup(&cache, id, 0);
    assert(cap != NULL);
    capability_release(&table, cap, 0);

    /* Verify it's cached */
    uint64_t perms;
    cap_state_t state;
    assert(cap_cache_lookup_fast(&cache, id, 0, &perms, &state) == true);

    /* Invalidate */
    cap_cache_invalidate(&cache, id, 0);

    /* Should be cache miss now */
    assert(cap_cache_lookup_fast(&cache, id, 0, &perms, &state) == false);

    cap_cache_destroy(&cache);
    capability_table_destroy(&table);

    printf("  PASS\n");
}

static void test_cache_multiple_cpus(void)
{
    printf("TEST: cache_multiple_cpus\n");

    capability_table_t table;
    assert(capability_table_init(&table, NUM_CPUS) == 0);

    cap_cache_t cache;
    assert(cap_cache_init(&cache, &table, NUM_CPUS) == 0);

    /* Create capability */
    cap_id_t id = 200;
    assert(capability_create(&table, id, CAP_PERM_READ, 1000) == 0);

    /* Cache on multiple CPUs */
    for (uint8_t cpu = 0; cpu < NUM_CPUS; cpu++) {
        capability_t *cap = cap_cache_lookup(&cache, id, cpu);
        assert(cap != NULL);
        capability_release(&table, cap, cpu);

        /* Verify cached */
        uint64_t perms;
        cap_state_t state;
        assert(cap_cache_lookup_fast(&cache, id, cpu, &perms, &state) == true);
    }

    /* Invalidate all */
    cap_cache_invalidate_all(&cache, id);

    /* Verify all invalidated */
    for (uint8_t cpu = 0; cpu < NUM_CPUS; cpu++) {
        uint64_t perms;
        cap_state_t state;
        assert(cap_cache_lookup_fast(&cache, id, cpu, &perms, &state) == false);
    }

    cap_cache_destroy(&cache);
    capability_table_destroy(&table);

    printf("  PASS\n");
}

static void test_cache_permission_check(void)
{
    printf("TEST: cache_permission_check\n");

    capability_table_t table;
    assert(capability_table_init(&table, NUM_CPUS) == 0);

    cap_cache_t cache;
    assert(cap_cache_init(&cache, &table, NUM_CPUS) == 0);

    /* Create capability */
    cap_id_t id = 300;
    assert(capability_create(&table, id, CAP_PERM_READ | CAP_PERM_WRITE, 1000) == 0);

    /* Check permission (will cache) */
    assert(cap_cache_has_permission(&cache, id, CAP_PERM_READ, 0) == true);
    assert(cap_cache_has_permission(&cache, id, CAP_PERM_WRITE, 0) == true);
    assert(cap_cache_has_permission(&cache, id, CAP_PERM_EXECUTE, 0) == false);

    /* Second check should hit cache */
    assert(cap_cache_has_permission(&cache, id, CAP_PERM_READ, 0) == true);

    cap_cache_destroy(&cache);
    capability_table_destroy(&table);

    printf("  PASS\n");
}

/*******************************************************************************
 * SIMD TESTS
 ******************************************************************************/

static void test_simd_feature_detection(void)
{
    printf("TEST: simd_feature_detection\n");

    /* Print available features */
    printf("  ");
    cap_simd_print_info();

    int level = cap_simd_get_level();
    printf("  SIMD Level: %d\n", level);

    printf("  PASS\n");
}

static void test_simd_check_adaptive(void)
{
    printf("TEST: simd_check_adaptive\n");

    /* Create test capabilities */
    const uint32_t num_caps = 16;
    capability_t *caps[num_caps];
    bool results[num_caps];

    for (uint32_t i = 0; i < num_caps; i++) {
        caps[i] = (capability_t *)calloc(1, sizeof(capability_t));
        caps[i]->id = i;
        atomic_store(&caps[i]->permissions, (i % 2) ?
            CAP_PERM_READ : CAP_PERM_READ | CAP_PERM_WRITE);
        atomic_store(&caps[i]->state, CAP_STATE_ACTIVE);
    }

    /* Check for READ permission - all should have it */
    cap_simd_check_adaptive(caps, num_caps, CAP_PERM_READ, results);
    for (uint32_t i = 0; i < num_caps; i++) {
        assert(results[i] == true);
    }

    /* Check for WRITE permission - only even indices */
    cap_simd_check_adaptive(caps, num_caps, CAP_PERM_WRITE, results);
    for (uint32_t i = 0; i < num_caps; i++) {
        bool expected = (i % 2) == 0;
        assert(results[i] == expected);
    }

    /* Cleanup */
    for (uint32_t i = 0; i < num_caps; i++) {
        free(caps[i]);
    }

    printf("  PASS\n");
}

static void test_simd_state_check_adaptive(void)
{
    printf("TEST: simd_state_check_adaptive\n");

    const uint32_t num_caps = 16;
    capability_t *caps[num_caps];
    bool results[num_caps];

    for (uint32_t i = 0; i < num_caps; i++) {
        caps[i] = (capability_t *)calloc(1, sizeof(capability_t));
        caps[i]->id = i;
        /* Half active, half revoked */
        cap_state_t state = (i < num_caps / 2) ?
            CAP_STATE_ACTIVE : CAP_STATE_REVOKED;
        atomic_store(&caps[i]->state, state);
    }

    /* Check for ACTIVE state */
    cap_simd_check_state_adaptive(caps, num_caps, CAP_STATE_ACTIVE, results);
    for (uint32_t i = 0; i < num_caps; i++) {
        bool expected = (i < num_caps / 2);
        assert(results[i] == expected);
    }

    /* Check for REVOKED state */
    cap_simd_check_state_adaptive(caps, num_caps, CAP_STATE_REVOKED, results);
    for (uint32_t i = 0; i < num_caps; i++) {
        bool expected = (i >= num_caps / 2);
        assert(results[i] == expected);
    }

    /* Cleanup */
    for (uint32_t i = 0; i < num_caps; i++) {
        free(caps[i]);
    }

    printf("  PASS\n");
}

/*******************************************************************************
 * PERFORMANCE BENCHMARKS
 ******************************************************************************/

static void benchmark_cache_vs_table(void)
{
    printf("BENCHMARK: cache_vs_table_lookup\n");

    capability_table_t table;
    capability_table_init(&table, NUM_CPUS);

    cap_cache_t cache;
    cap_cache_init(&cache, &table, NUM_CPUS);

    /* Create capabilities */
    const uint32_t num_caps = 100;
    for (uint32_t i = 0; i < num_caps; i++) {
        capability_create(&table, i, CAP_PERM_READ, 1000);
    }

    const uint32_t iterations = 10000;
    uint8_t cpu = 0;

    /* Benchmark table lookup */
    uint64_t start = get_time_ns();
    for (uint32_t iter = 0; iter < iterations; iter++) {
        cap_id_t id = iter % num_caps;
        capability_t *cap = capability_lookup(&table, id, cpu);
        if (cap) {
            capability_check_fast(cap, CAP_PERM_READ);
            capability_release(&table, cap, cpu);
        }
    }
    uint64_t table_time = get_time_ns() - start;

    /* Pre-warm cache */
    for (uint32_t i = 0; i < num_caps; i++) {
        cap_cache_lookup(&cache, i, cpu);
    }

    /* Benchmark cache lookup */
    start = get_time_ns();
    for (uint32_t iter = 0; iter < iterations; iter++) {
        cap_id_t id = iter % num_caps;
        cap_cache_has_permission(&cache, id, CAP_PERM_READ, cpu);
    }
    uint64_t cache_time = get_time_ns() - start;

    double table_avg_ns = (double)table_time / iterations;
    double cache_avg_ns = (double)cache_time / iterations;
    double speedup = (double)table_time / cache_time;

    printf("  Table lookup: %.2f ns/op\n", table_avg_ns);
    printf("  Cache lookup: %.2f ns/op\n", cache_avg_ns);
    printf("  Speedup:      %.2fx\n", speedup);

    /* Print cache statistics */
    cap_cache_cpu_stats_t stats;
    cap_cache_get_cpu_stats(&cache, cpu, &stats);
    printf("  Cache hit rate: %.2f%%\n", stats.hit_rate * 100.0);

    cap_cache_destroy(&cache);
    capability_table_destroy(&table);
}

static void benchmark_simd_vs_scalar(void)
{
    printf("BENCHMARK: simd_vs_scalar\n");

    /* Use SIMD benchmark function */
    cap_simd_benchmark(10000);
}

/*******************************************************************************
 * MAIN TEST RUNNER
 ******************************************************************************/

int main(void)
{
    printf("================================================================================\n");
    printf("CACHE AND SIMD OPTIMIZATION TEST SUITE (Phase B)\n");
    printf("================================================================================\n\n");

    printf("--- Cache Tests ---\n");
    test_cache_init_destroy();
    test_cache_lookup_hit_miss();
    test_cache_invalidation();
    test_cache_multiple_cpus();
    test_cache_permission_check();
    printf("\n");

    printf("--- SIMD Tests ---\n");
    test_simd_feature_detection();
    test_simd_check_adaptive();
    test_simd_state_check_adaptive();
    printf("\n");

    printf("--- Performance Benchmarks ---\n");
    benchmark_cache_vs_table();
    printf("\n");
    benchmark_simd_vs_scalar();
    printf("\n");

    printf("--- SIMD Statistics ---\n");
    cap_simd_print_stats();
    printf("\n");

    printf("================================================================================\n");
    printf("ALL TESTS PASSED\n");
    printf("Phase B optimizations validated successfully.\n");
    printf("\n");
    printf("Expected Performance Improvements:\n");
    printf("  Cache:  5-10x faster lookups (1-5ns vs 10-50ns)\n");
    printf("  SIMD:   2-8x faster batch operations\n");
    printf("  Combined: 10-20x improvement on hot paths\n");
    printf("================================================================================\n");

    return 0;
}
