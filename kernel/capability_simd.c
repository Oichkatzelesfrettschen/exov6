/**
 * @file capability_simd.c
 * @brief SIMD-Accelerated Capability Operations Implementation (Phase B)
 *
 * Implementation of vectorized capability operations.
 */

#include "capability_simd.h"
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <cpuid.h>  /* For CPU feature detection */

/*******************************************************************************
 * SIMD STATISTICS
 ******************************************************************************/

static cap_simd_stats_t g_simd_stats = {0};

/*******************************************************************************
 * CPU FEATURE DETECTION
 ******************************************************************************/

bool cap_simd_has_avx2(void)
{
#ifdef __AVX2__
    /* Check CPUID for AVX2 support */
    unsigned int eax, ebx, ecx, edx;
    if (__get_cpuid(7, &eax, &ebx, &ecx, &edx)) {
        return (ebx & bit_AVX2) != 0;
    }
#endif
    return false;
}

bool cap_simd_has_avx512(void)
{
#ifdef __AVX512F__
    /* Check CPUID for AVX-512F support */
    unsigned int eax, ebx, ecx, edx;
    if (__get_cpuid(7, &eax, &ebx, &ecx, &edx)) {
        return (ebx & bit_AVX512F) != 0;
    }
#endif
    return false;
}

int cap_simd_get_level(void)
{
    if (cap_simd_has_avx512()) return 512;
    if (cap_simd_has_avx2()) return 2;
    return 0;  /* No SIMD */
}

void cap_simd_print_info(void)
{
    printf("SIMD Capabilities:\n");
    printf("  AVX2:     %s\n", cap_simd_has_avx2() ? "Available" : "Not Available");
    printf("  AVX-512:  %s\n", cap_simd_has_avx512() ? "Available" : "Not Available");
    printf("  Best:     ");

    int level = cap_simd_get_level();
    if (level == 512) {
        printf("AVX-512 (8-way parallelism, ~4-8x speedup)\n");
    } else if (level == 2) {
        printf("AVX2 (4-way parallelism, ~2-4x speedup)\n");
    } else {
        printf("Scalar (no SIMD acceleration)\n");
    }
}

/*******************************************************************************
 * ADAPTIVE SIMD OPERATIONS
 ******************************************************************************/

void cap_simd_check_adaptive(capability_t **caps, uint32_t count,
                             uint64_t perm, bool *results)
{
    if (!caps || !results || count == 0) return;

#ifdef __AVX512F__
    if (cap_simd_has_avx512()) {
        /* Use AVX-512 (8-way) */
        uint32_t i;
        for (i = 0; i + 7 < count; i += 8) {
            cap_simd_check_avx512(&caps[i], perm, &results[i]);
            g_simd_stats.avx512_operations++;
            g_simd_stats.total_capabilities_processed += 8;
        }

        /* Handle remainder */
        for (; i < count; i++) {
            results[i] = capability_check_fast(caps[i], perm);
            g_simd_stats.scalar_operations++;
            g_simd_stats.total_capabilities_processed++;
        }
        return;
    }
#endif

#ifdef __AVX2__
    if (cap_simd_has_avx2()) {
        /* Use AVX2 (4-way) */
        uint32_t i;
        for (i = 0; i + 3 < count; i += 4) {
            cap_simd_check_avx2(&caps[i], perm, &results[i]);
            g_simd_stats.avx2_operations++;
            g_simd_stats.total_capabilities_processed += 4;
        }

        /* Handle remainder */
        for (; i < count; i++) {
            results[i] = capability_check_fast(caps[i], perm);
            g_simd_stats.scalar_operations++;
            g_simd_stats.total_capabilities_processed++;
        }
        return;
    }
#endif

    /* Fallback: scalar */
    for (uint32_t i = 0; i < count; i++) {
        results[i] = capability_check_fast(caps[i], perm);
        g_simd_stats.scalar_operations++;
        g_simd_stats.total_capabilities_processed++;
    }
}

void cap_simd_check_state_adaptive(capability_t **caps, uint32_t count,
                                   cap_state_t expected_state, bool *results)
{
    if (!caps || !results || count == 0) return;

#ifdef __AVX512F__
    if (cap_simd_has_avx512()) {
        uint32_t i;
        for (i = 0; i + 7 < count; i += 8) {
            cap_simd_check_state_avx512(&caps[i], expected_state, &results[i]);
            g_simd_stats.avx512_operations++;
            g_simd_stats.total_capabilities_processed += 8;
        }
        for (; i < count; i++) {
            results[i] = task_is_state_fast((task_t *)caps[i], (task_state_t)expected_state);
            g_simd_stats.scalar_operations++;
            g_simd_stats.total_capabilities_processed++;
        }
        return;
    }
#endif

#ifdef __AVX2__
    if (cap_simd_has_avx2()) {
        uint32_t i;
        for (i = 0; i + 3 < count; i += 4) {
            cap_simd_check_state_avx2(&caps[i], expected_state, &results[i]);
            g_simd_stats.avx2_operations++;
            g_simd_stats.total_capabilities_processed += 4;
        }
        for (; i < count; i++) {
            results[i] = (caps[i] && atomic_load_explicit(&caps[i]->state,
                memory_order_relaxed) == expected_state);
            g_simd_stats.scalar_operations++;
            g_simd_stats.total_capabilities_processed++;
        }
        return;
    }
#endif

    /* Fallback: scalar */
    for (uint32_t i = 0; i < count; i++) {
        results[i] = (caps[i] && atomic_load_explicit(&caps[i]->state,
            memory_order_relaxed) == expected_state);
        g_simd_stats.scalar_operations++;
        g_simd_stats.total_capabilities_processed++;
    }
}

void cap_simd_batch_check(capability_t **caps, uint32_t count,
                         uint64_t perm, bool *results)
{
    /* Just call adaptive version */
    cap_simd_check_adaptive(caps, count, perm, results);
}

/*******************************************************************************
 * STATISTICS
 ******************************************************************************/

void cap_simd_get_stats(cap_simd_stats_t *stats)
{
    if (!stats) return;
    *stats = g_simd_stats;

    /* Calculate average speedup */
    uint64_t total_ops = stats->avx512_operations + stats->avx2_operations +
                         stats->scalar_operations;
    if (total_ops > 0) {
        /* Rough estimate: AVX-512 = 6x, AVX2 = 3x, Scalar = 1x */
        double weighted = (stats->avx512_operations * 6.0) +
                         (stats->avx2_operations * 3.0) +
                         (stats->scalar_operations * 1.0);
        stats->avg_speedup = weighted / total_ops;
    } else {
        stats->avg_speedup = 1.0;
    }
}

void cap_simd_print_stats(void)
{
    cap_simd_stats_t stats;
    cap_simd_get_stats(&stats);

    printf("================================================================================\n");
    printf("SIMD STATISTICS\n");
    printf("================================================================================\n");
    printf("Operations:\n");
    printf("  AVX-512:    %lu (8-way)\n", stats.avx512_operations);
    printf("  AVX2:       %lu (4-way)\n", stats.avx2_operations);
    printf("  Scalar:     %lu (1-way)\n", stats.scalar_operations);
    printf("\n");
    printf("Capabilities Processed:\n");
    printf("  Total:      %lu\n", stats.total_capabilities_processed);
    printf("\n");
    printf("Performance:\n");
    printf("  Avg Speedup: %.2fx\n", stats.avg_speedup);
    printf("================================================================================\n");
}

/*******************************************************************************
 * BENCHMARKING
 ******************************************************************************/

static uint64_t get_time_ns(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + ts.tv_nsec;
}

void cap_simd_benchmark(uint32_t num_iterations)
{
    printf("================================================================================\n");
    printf("SIMD PERFORMANCE BENCHMARK\n");
    printf("================================================================================\n");
    printf("Iterations: %u\n", num_iterations);
    printf("Testing with 32 capabilities per iteration\n\n");

    /* Create test capabilities */
    const uint32_t num_caps = 32;
    capability_t *caps[num_caps];
    bool results[num_caps];

    for (uint32_t i = 0; i < num_caps; i++) {
        caps[i] = (capability_t *)malloc(sizeof(capability_t));
        caps[i]->id = i;
        atomic_store(&caps[i]->permissions, CAP_PERM_READ | CAP_PERM_WRITE);
        atomic_store(&caps[i]->state, CAP_STATE_ACTIVE);
        caps[i]->owner_pid = 1000;
    }

    uint64_t perm = CAP_PERM_READ;

    /* Benchmark scalar */
    uint64_t start = get_time_ns();
    for (uint32_t iter = 0; iter < num_iterations; iter++) {
        for (uint32_t i = 0; i < num_caps; i++) {
            results[i] = capability_check_fast(caps[i], perm);
        }
    }
    uint64_t scalar_time = get_time_ns() - start;

    /* Benchmark SIMD adaptive */
    start = get_time_ns();
    for (uint32_t iter = 0; iter < num_iterations; iter++) {
        cap_simd_check_adaptive(caps, num_caps, perm, results);
    }
    uint64_t simd_time = get_time_ns() - start;

    /* Calculate metrics */
    double scalar_ns_per_op = (double)scalar_time / (num_iterations * num_caps);
    double simd_ns_per_op = (double)simd_time / (num_iterations * num_caps);
    double speedup = (double)scalar_time / simd_time;

    /* Print results */
    printf("Results:\n");
    printf("  Scalar:      %.2f ns/op (%lu ns total)\n",
           scalar_ns_per_op, scalar_time);
    printf("  SIMD:        %.2f ns/op (%lu ns total)\n",
           simd_ns_per_op, simd_time);
    printf("  Speedup:     %.2fx\n", speedup);
    printf("\n");

    printf("SIMD Level:    ");
    int level = cap_simd_get_level();
    if (level == 512) {
        printf("AVX-512 (8-way)\n");
    } else if (level == 2) {
        printf("AVX2 (4-way)\n");
    } else {
        printf("None (scalar fallback)\n");
    }

    printf("\n");
    printf("Expected Performance:\n");
    printf("  AVX-512: 4-8x speedup for batch operations\n");
    printf("  AVX2:    2-4x speedup for batch operations\n");
    printf("  Scalar:  1x baseline\n");

    printf("================================================================================\n");

    /* Cleanup */
    for (uint32_t i = 0; i < num_caps; i++) {
        free(caps[i]);
    }
}
