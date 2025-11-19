/**
 * @file capability_simd_adaptive.c
 * @brief Adaptive SIMD Implementation (Task 5.5.4 - Phase 2)
 */

#include "capability_simd_adaptive.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>

/*******************************************************************************
 * HELPER FUNCTIONS
 ******************************************************************************/

static uint64_t get_time_ns(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + ts.tv_nsec;
}

/*******************************************************************************
 * INITIALIZATION
 ******************************************************************************/

int simd_adaptive_init(simd_adaptive_t *simd)
{
    if (!simd) return -1;

    memset(simd, 0, sizeof(*simd));

    /* Detect available SIMD level */
    simd->simd_level = cap_simd_get_level();

    /* Initialize statistics */
    for (int i = 0; i < 7; i++) {
        atomic_store(&simd->stats.batch_sizes[i], 0);
    }
    atomic_store(&simd->stats.scalar_chosen, 0);
    atomic_store(&simd->stats.avx2_chosen, 0);
    atomic_store(&simd->stats.avx512_chosen, 0);
    atomic_store(&simd->stats.total_operations, 0);

    /* Enable adaptation by default */
    atomic_store(&simd->adaptation_enabled, true);

    /* Run calibration */
    return simd_adaptive_calibrate(simd);
}

void simd_adaptive_destroy(simd_adaptive_t *simd)
{
    if (!simd) return;

    atomic_store(&simd->adaptation_enabled, false);
}

void simd_adaptive_set_enabled(simd_adaptive_t *simd, bool enable)
{
    if (!simd) return;
    atomic_store(&simd->adaptation_enabled, enable);
}

/*******************************************************************************
 * CALIBRATION
 ******************************************************************************/

int simd_adaptive_calibrate(simd_adaptive_t *simd)
{
    if (!simd) return -1;

    printf("Calibrating adaptive SIMD thresholds...\n");

    uint64_t start_time = get_time_ns();

    /* Create test capabilities */
    const uint32_t max_batch = SIMD_BENCHMARK_MAX_BATCH;
    capability_t *caps[max_batch];
    bool results[max_batch];

    for (uint32_t i = 0; i < max_batch; i++) {
        caps[i] = (capability_t *)calloc(1, sizeof(capability_t));
        caps[i]->id = i;
        atomic_store(&caps[i]->permissions, CAP_PERM_READ | CAP_PERM_WRITE);
        atomic_store(&caps[i]->state, CAP_STATE_ACTIVE);
    }

    /* Default thresholds (conservative) */
    simd->thresholds.avx2_threshold = 8;
    simd->thresholds.avx512_threshold = 16;
    simd->thresholds.avx2_speedup = 1.0;
    simd->thresholds.avx512_speedup = 1.0;

    /* Benchmark different batch sizes */
    const uint32_t iterations = SIMD_BENCHMARK_ITERATIONS;
    const uint32_t batch_sizes[] = {4, 8, 16, 32, 64};
    const int num_sizes = 5;

    for (int i = 0; i < num_sizes; i++) {
        uint32_t batch = batch_sizes[i];

        /* Benchmark scalar */
        uint64_t scalar_start = get_time_ns();
        for (uint32_t iter = 0; iter < iterations; iter++) {
            for (uint32_t j = 0; j < batch; j++) {
                results[j] = capability_check_fast(caps[j], CAP_PERM_READ);
            }
        }
        uint64_t scalar_time = get_time_ns() - scalar_start;

        /* Benchmark SIMD (adaptive) */
        uint64_t simd_start = get_time_ns();
        for (uint32_t iter = 0; iter < iterations; iter++) {
            cap_simd_check_adaptive(caps, batch, CAP_PERM_READ, results);
        }
        uint64_t simd_time = get_time_ns() - simd_start;

        double speedup = (double)scalar_time / simd_time;

        printf("  Batch %2d: Scalar=%6luns, SIMD=%6luns, Speedup=%.2fx\n",
               batch,
               scalar_time / iterations,
               simd_time / iterations,
               speedup);

        /* Update thresholds based on speedup */
        if (simd->simd_level >= 2 && speedup >= SIMD_SPEEDUP_THRESHOLD) {
            /* AVX2 is beneficial at this size */
            if (batch < simd->thresholds.avx2_threshold) {
                simd->thresholds.avx2_threshold = batch;
                simd->thresholds.avx2_speedup = speedup;
            }
        }

        if (simd->simd_level == 512 && speedup >= SIMD_SPEEDUP_THRESHOLD * 1.5) {
            /* AVX-512 is beneficial at this size */
            if (batch < simd->thresholds.avx512_threshold) {
                simd->thresholds.avx512_threshold = batch;
                simd->thresholds.avx512_speedup = speedup;
            }
        }
    }

    /* Cleanup */
    for (uint32_t i = 0; i < max_batch; i++) {
        free(caps[i]);
    }

    simd->thresholds.calibrated = true;
    simd->thresholds.calibration_time_ns = get_time_ns() - start_time;

    printf("Calibration complete:\n");
    printf("  AVX2 threshold:    %u (%.2fx speedup)\n",
           simd->thresholds.avx2_threshold,
           simd->thresholds.avx2_speedup);
    printf("  AVX-512 threshold: %u (%.2fx speedup)\n",
           simd->thresholds.avx512_threshold,
           simd->thresholds.avx512_speedup);
    printf("  Calibration time:  %.2f ms\n",
           simd->thresholds.calibration_time_ns / 1000000.0);

    return 0;
}

void simd_adaptive_get_thresholds(const simd_adaptive_t *simd,
                                  simd_thresholds_t *thresholds)
{
    if (!simd || !thresholds) return;
    *thresholds = simd->thresholds;
}

void simd_adaptive_set_thresholds(simd_adaptive_t *simd,
                                  const simd_thresholds_t *thresholds)
{
    if (!simd || !thresholds) return;
    simd->thresholds = *thresholds;
}

/*******************************************************************************
 * ADAPTIVE OPERATIONS
 ******************************************************************************/

void simd_adaptive_check(simd_adaptive_t *simd, capability_t **caps,
                         uint32_t count, uint64_t perm, bool *results)
{
    if (!simd || !caps || !results || count == 0) return;

    /* Update histogram */
    simd_adaptive_update_histogram(simd, count);

    /* Select method */
    int method = simd_adaptive_select_method(simd, count);

    /* Execute based on selection */
    switch (method) {
        case 512:
            /* AVX-512 */
#ifdef __AVX512F__
            if (cap_simd_has_avx512()) {
                cap_simd_check_adaptive(caps, count, perm, results);
                atomic_fetch_add(&simd->stats.avx512_chosen, 1);
                return;
            }
#endif
            /* Fallthrough to AVX2 */

        case 2:
            /* AVX2 */
#ifdef __AVX2__
            if (cap_simd_has_avx2()) {
                cap_simd_check_adaptive(caps, count, perm, results);
                atomic_fetch_add(&simd->stats.avx2_chosen, 1);
                return;
            }
#endif
            /* Fallthrough to scalar */

        case 0:
        default:
            /* Scalar */
            for (uint32_t i = 0; i < count; i++) {
                results[i] = capability_check_fast(caps[i], perm);
            }
            atomic_fetch_add(&simd->stats.scalar_chosen, 1);
            break;
    }
}

void simd_adaptive_check_state(simd_adaptive_t *simd, capability_t **caps,
                               uint32_t count, cap_state_t state, bool *results)
{
    if (!simd || !caps || !results || count == 0) return;

    /* Update histogram */
    simd_adaptive_update_histogram(simd, count);

    /* Select method */
    int method = simd_adaptive_select_method(simd, count);

    /* Execute based on selection */
    switch (method) {
        case 512:
#ifdef __AVX512F__
            if (cap_simd_has_avx512()) {
                cap_simd_check_state_adaptive(caps, count, state, results);
                atomic_fetch_add(&simd->stats.avx512_chosen, 1);
                return;
            }
#endif
            /* Fallthrough */

        case 2:
#ifdef __AVX2__
            if (cap_simd_has_avx2()) {
                cap_simd_check_state_adaptive(caps, count, state, results);
                atomic_fetch_add(&simd->stats.avx2_chosen, 1);
                return;
            }
#endif
            /* Fallthrough */

        case 0:
        default:
            /* Scalar */
            for (uint32_t i = 0; i < count; i++) {
                results[i] = (caps[i] &&
                             atomic_load_explicit(&caps[i]->state,
                                                 memory_order_relaxed) == state);
            }
            atomic_fetch_add(&simd->stats.scalar_chosen, 1);
            break;
    }
}

/*******************************************************************************
 * STATISTICS
 ******************************************************************************/

void simd_adaptive_get_stats(const simd_adaptive_t *simd,
                             simd_adaptive_stats_full_t *stats)
{
    if (!simd || !stats) return;

    memset(stats, 0, sizeof(*stats));

    /* Thresholds */
    stats->thresholds = simd->thresholds;

    /* Batch distribution */
    stats->batch_distribution.count_1 = atomic_load(&simd->stats.batch_sizes[0]);
    stats->batch_distribution.count_2_3 = atomic_load(&simd->stats.batch_sizes[1]);
    stats->batch_distribution.count_4_7 = atomic_load(&simd->stats.batch_sizes[2]);
    stats->batch_distribution.count_8_15 = atomic_load(&simd->stats.batch_sizes[3]);
    stats->batch_distribution.count_16_31 = atomic_load(&simd->stats.batch_sizes[4]);
    stats->batch_distribution.count_32_63 = atomic_load(&simd->stats.batch_sizes[5]);
    stats->batch_distribution.count_64_plus = atomic_load(&simd->stats.batch_sizes[6]);

    /* Method selection */
    stats->scalar_chosen = atomic_load(&simd->stats.scalar_chosen);
    stats->avx2_chosen = atomic_load(&simd->stats.avx2_chosen);
    stats->avx512_chosen = atomic_load(&simd->stats.avx512_chosen);

    /* Totals */
    stats->total_operations = atomic_load(&simd->stats.total_operations);

    /* Configuration */
    stats->adaptation_enabled = atomic_load(&simd->adaptation_enabled);
    stats->calibrated = simd->thresholds.calibrated;
}

void simd_adaptive_print_stats(const simd_adaptive_t *simd)
{
    if (!simd) return;

    printf("================================================================================\n");
    printf("ADAPTIVE SIMD STATISTICS\n");
    printf("================================================================================\n\n");

    simd_adaptive_stats_full_t stats;
    simd_adaptive_get_stats(simd, &stats);

    printf("Configuration:\n");
    printf("  Adaptation Enabled: %s\n", stats.adaptation_enabled ? "Yes" : "No");
    printf("  Calibrated:         %s\n", stats.calibrated ? "Yes" : "No");
    printf("  SIMD Level:         %d\n", simd->simd_level);
    printf("\n");

    if (stats.calibrated) {
        printf("Thresholds:\n");
        printf("  AVX2 Threshold:     %u (%.2fx speedup)\n",
               stats.thresholds.avx2_threshold,
               stats.thresholds.avx2_speedup);
        printf("  AVX-512 Threshold:  %u (%.2fx speedup)\n",
               stats.thresholds.avx512_threshold,
               stats.thresholds.avx512_speedup);
        printf("  Calibration Time:   %.2f ms\n",
               stats.thresholds.calibration_time_ns / 1000000.0);
        printf("\n");
    }

    printf("Batch Size Distribution:\n");
    printf("  1:       %lu\n", stats.batch_distribution.count_1);
    printf("  2-3:     %lu\n", stats.batch_distribution.count_2_3);
    printf("  4-7:     %lu\n", stats.batch_distribution.count_4_7);
    printf("  8-15:    %lu\n", stats.batch_distribution.count_8_15);
    printf("  16-31:   %lu\n", stats.batch_distribution.count_16_31);
    printf("  32-63:   %lu\n", stats.batch_distribution.count_32_63);
    printf("  64+:     %lu\n", stats.batch_distribution.count_64_plus);
    printf("\n");

    printf("Method Selection:\n");
    printf("  Scalar:  %lu (%.1f%%)\n",
           stats.scalar_chosen,
           stats.total_operations > 0 ?
               (double)stats.scalar_chosen / stats.total_operations * 100 : 0.0);
    printf("  AVX2:    %lu (%.1f%%)\n",
           stats.avx2_chosen,
           stats.total_operations > 0 ?
               (double)stats.avx2_chosen / stats.total_operations * 100 : 0.0);
    printf("  AVX-512: %lu (%.1f%%)\n",
           stats.avx512_chosen,
           stats.total_operations > 0 ?
               (double)stats.avx512_chosen / stats.total_operations * 100 : 0.0);
    printf("\n");

    printf("Total Operations: %lu\n", stats.total_operations);

    printf("\n");
    printf("Expected Performance:\n");
    printf("  Overhead:     <0.5%%\n");
    printf("  Improvement:  5-10%% for mixed batches\n");
    printf("================================================================================\n");
}

void simd_adaptive_benchmark(simd_adaptive_t *simd, uint32_t iterations)
{
    if (!simd) return;

    printf("================================================================================\n");
    printf("ADAPTIVE SIMD BENCHMARK\n");
    printf("================================================================================\n");
    printf("Iterations: %u\n", iterations);
    printf("Testing with varied batch sizes\n\n");

    /* Create test capabilities */
    const uint32_t max_caps = 64;
    capability_t *caps[max_caps];
    bool results[max_caps];

    for (uint32_t i = 0; i < max_caps; i++) {
        caps[i] = (capability_t *)calloc(1, sizeof(capability_t));
        caps[i]->id = i;
        atomic_store(&caps[i]->permissions, CAP_PERM_READ | CAP_PERM_WRITE);
        atomic_store(&caps[i]->state, CAP_STATE_ACTIVE);
    }

    /* Benchmark with varied batch sizes */
    const uint32_t batch_sizes[] = {4, 8, 16, 32, 64};
    for (int b = 0; b < 5; b++) {
        uint32_t batch = batch_sizes[b];

        /* Benchmark static SIMD */
        uint64_t start = get_time_ns();
        for (uint32_t iter = 0; iter < iterations; iter++) {
            cap_simd_check_adaptive(caps, batch, CAP_PERM_READ, results);
        }
        uint64_t static_time = get_time_ns() - start;

        /* Benchmark adaptive SIMD */
        start = get_time_ns();
        for (uint32_t iter = 0; iter < iterations; iter++) {
            simd_adaptive_check(simd, caps, batch, CAP_PERM_READ, results);
        }
        uint64_t adaptive_time = get_time_ns() - start;

        double static_ns = (double)static_time / iterations;
        double adaptive_ns = (double)adaptive_time / iterations;
        double overhead = ((double)adaptive_time / static_time - 1.0) * 100;

        printf("Batch %2d:\n", batch);
        printf("  Static:   %.2f ns\n", static_ns);
        printf("  Adaptive: %.2f ns\n", adaptive_ns);
        printf("  Overhead: %+.2f%%\n\n", overhead);
    }

    /* Cleanup */
    for (uint32_t i = 0; i < max_caps; i++) {
        free(caps[i]);
    }

    printf("Target: Overhead < 0.5%%\n");
    printf("================================================================================\n");
}
