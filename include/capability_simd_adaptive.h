/**
 * @file capability_simd_adaptive.h
 * @brief Adaptive SIMD Threshold Selection (Task 5.5.4 - Phase 2)
 *
 * Dynamic SIMD threshold that adapts to actual performance:
 * - Startup benchmarking to find crossover points
 * - Runtime batch size tracking
 * - Automatic scalar/SIMD selection
 * - Per-workload optimization
 *
 * Expected Performance:
 * - 5-10% improvement for mixed batch sizes
 * - Overhead: <0.5%
 * - Optimal SIMD usage across varied workloads
 */

#pragma once

#include "capability_simd.h"
#include <stdint.h>
#include <stdbool.h>
#include <stdatomic.h>

#ifdef __cplusplus
extern "C" {
#endif

/*******************************************************************************
 * CONFIGURATION
 ******************************************************************************/

/** Benchmark configuration */
#define SIMD_BENCHMARK_ITERATIONS  10000  /**< Iterations per batch size */
#define SIMD_BENCHMARK_MAX_BATCH   64     /**< Max batch size to test */

/** Adaptation configuration */
#define SIMD_ADAPT_WINDOW_SIZE     1000   /**< Samples before re-evaluation */
#define SIMD_SPEEDUP_THRESHOLD     1.2    /**< Min speedup to use SIMD */

/*******************************************************************************
 * ADAPTIVE SIMD STATE
 ******************************************************************************/

/**
 * @brief SIMD crossover thresholds
 *
 * Batch sizes below threshold use scalar, above use SIMD.
 */
typedef struct {
    /* Measured thresholds */
    uint32_t avx512_threshold;  /**< Minimum batch for AVX-512 */
    uint32_t avx2_threshold;    /**< Minimum batch for AVX2 */

    /* Measured speedups */
    double avx512_speedup;      /**< Measured speedup for AVX-512 */
    double avx2_speedup;        /**< Measured speedup for AVX2 */

    /* Calibration state */
    bool calibrated;            /**< Has been calibrated */
    uint64_t calibration_time_ns; /**< Time taken to calibrate */
} simd_thresholds_t;

/**
 * @brief Runtime batch statistics
 */
typedef struct {
    /* Batch size histogram */
    _Atomic uint64_t batch_sizes[9];  /**< Buckets: 1, 2-3, 4-7, 8-15, 16-31, 32-63, 64+ */

    /* Decision statistics */
    _Atomic uint64_t scalar_chosen;
    _Atomic uint64_t avx2_chosen;
    _Atomic uint64_t avx512_chosen;

    /* Adaptation */
    _Atomic uint64_t total_operations;
    uint64_t last_adapt_count;
} simd_runtime_stats_t;

/**
 * @brief Adaptive SIMD system
 */
typedef struct {
    /* Thresholds */
    simd_thresholds_t thresholds;

    /* Runtime statistics */
    simd_runtime_stats_t stats;

    /* Adaptation control */
    _Atomic bool adaptation_enabled;

    /* Available SIMD levels */
    int simd_level;  /**< 0=none, 2=AVX2, 512=AVX-512 */
} simd_adaptive_t;

/*******************************************************************************
 * INITIALIZATION
 ******************************************************************************/

/**
 * @brief Initialize adaptive SIMD system
 *
 * Runs startup benchmarks to determine optimal thresholds.
 *
 * @param simd  Adaptive SIMD system
 * @return 0 on success, negative on error
 */
int simd_adaptive_init(simd_adaptive_t *simd);

/**
 * @brief Destroy adaptive SIMD system
 *
 * @param simd  Adaptive SIMD system
 */
void simd_adaptive_destroy(simd_adaptive_t *simd);

/**
 * @brief Enable/disable adaptation
 *
 * @param simd   Adaptive SIMD system
 * @param enable true to enable, false to disable
 */
void simd_adaptive_set_enabled(simd_adaptive_t *simd, bool enable);

/*******************************************************************************
 * ADAPTIVE SIMD OPERATIONS
 ******************************************************************************/

/**
 * @brief Adaptive SIMD permission check
 *
 * Automatically selects scalar/AVX2/AVX-512 based on batch size and thresholds.
 *
 * @param simd    Adaptive SIMD system
 * @param caps    Array of capabilities
 * @param count   Number of capabilities
 * @param perm    Permission to check
 * @param results Output array
 */
void simd_adaptive_check(simd_adaptive_t *simd, capability_t **caps,
                         uint32_t count, uint64_t perm, bool *results);

/**
 * @brief Adaptive SIMD state check
 *
 * @param simd    Adaptive SIMD system
 * @param caps    Array of capabilities
 * @param count   Number of capabilities
 * @param state   Expected state
 * @param results Output array
 */
void simd_adaptive_check_state(simd_adaptive_t *simd, capability_t **caps,
                               uint32_t count, cap_state_t state, bool *results);

/*******************************************************************************
 * CALIBRATION
 ******************************************************************************/

/**
 * @brief Run startup calibration
 *
 * Benchmarks scalar vs SIMD to determine optimal thresholds.
 *
 * @param simd  Adaptive SIMD system
 * @return 0 on success, negative on error
 */
int simd_adaptive_calibrate(simd_adaptive_t *simd);

/**
 * @brief Get current thresholds
 *
 * @param simd        Adaptive SIMD system
 * @param thresholds  Output thresholds
 */
void simd_adaptive_get_thresholds(const simd_adaptive_t *simd,
                                  simd_thresholds_t *thresholds);

/**
 * @brief Manually set thresholds
 *
 * Overrides calibration.
 *
 * @param simd        Adaptive SIMD system
 * @param thresholds  Desired thresholds
 */
void simd_adaptive_set_thresholds(simd_adaptive_t *simd,
                                  const simd_thresholds_t *thresholds);

/*******************************************************************************
 * DECISION LOGIC
 ******************************************************************************/

/**
 * @brief Select best SIMD method for batch
 *
 * @param simd   Adaptive SIMD system
 * @param count  Batch size
 * @return 0 (scalar), 2 (AVX2), or 512 (AVX-512)
 */
static inline int simd_adaptive_select_method(const simd_adaptive_t *simd,
                                              uint32_t count)
{
    if (!simd || !atomic_load(&simd->adaptation_enabled)) {
        /* Fallback to static selection */
        return cap_simd_get_level();
    }

    const simd_thresholds_t *t = &simd->thresholds;

    if (!t->calibrated) {
        /* Not calibrated - use default */
        return cap_simd_get_level();
    }

    /* Check AVX-512 threshold */
    if (simd->simd_level == 512 && count >= t->avx512_threshold) {
        return 512;
    }

    /* Check AVX2 threshold */
    if (simd->simd_level >= 2 && count >= t->avx2_threshold) {
        return 2;
    }

    /* Use scalar */
    return 0;
}

/**
 * @brief Update batch size histogram
 *
 * @param simd   Adaptive SIMD system
 * @param count  Batch size
 */
static inline void simd_adaptive_update_histogram(simd_adaptive_t *simd,
                                                  uint32_t count)
{
    int bucket;
    if (count == 1) bucket = 0;
    else if (count <= 3) bucket = 1;
    else if (count <= 7) bucket = 2;
    else if (count <= 15) bucket = 3;
    else if (count <= 31) bucket = 4;
    else if (count <= 63) bucket = 5;
    else bucket = 6;

    atomic_fetch_add(&simd->stats.batch_sizes[bucket], 1);
    atomic_fetch_add(&simd->stats.total_operations, 1);
}

/*******************************************************************************
 * STATISTICS
 ******************************************************************************/

/**
 * @brief Adaptive SIMD statistics
 */
typedef struct {
    /* Thresholds */
    simd_thresholds_t thresholds;

    /* Batch size distribution */
    struct {
        uint64_t count_1;
        uint64_t count_2_3;
        uint64_t count_4_7;
        uint64_t count_8_15;
        uint64_t count_16_31;
        uint64_t count_32_63;
        uint64_t count_64_plus;
    } batch_distribution;

    /* Method selection */
    uint64_t scalar_chosen;
    uint64_t avx2_chosen;
    uint64_t avx512_chosen;

    /* Totals */
    uint64_t total_operations;

    /* Configuration */
    bool adaptation_enabled;
    bool calibrated;
} simd_adaptive_stats_full_t;

/**
 * @brief Get adaptive SIMD statistics
 *
 * @param simd   Adaptive SIMD system
 * @param stats  Output statistics
 */
void simd_adaptive_get_stats(const simd_adaptive_t *simd,
                             simd_adaptive_stats_full_t *stats);

/**
 * @brief Print adaptive SIMD statistics
 *
 * @param simd  Adaptive SIMD system
 */
void simd_adaptive_print_stats(const simd_adaptive_t *simd);

/**
 * @brief Run adaptive SIMD benchmark
 *
 * Compares adaptive vs static SIMD selection.
 *
 * @param simd       Adaptive SIMD system
 * @param iterations Number of iterations
 */
void simd_adaptive_benchmark(simd_adaptive_t *simd, uint32_t iterations);

#ifdef __cplusplus
}
#endif
