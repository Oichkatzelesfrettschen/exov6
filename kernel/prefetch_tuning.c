/**
 * @file prefetch_tuning.c
 * @brief Adaptive Prefetch Tuning Implementation (Task 5.5.4 - Phase 3)
 */

#include "prefetch_tuning.h"
#include <stdio.h>
#include <string.h>

/*******************************************************************************
 * INITIALIZATION
 ******************************************************************************/

int prefetch_tuning_init(prefetch_config_t *config)
{
    if (!config) return -1;

    memset(config, 0, sizeof(*config));

    /* Start with medium distance */
    atomic_store(&config->distance, PREFETCH_DIST_MEDIUM);
    atomic_store(&config->enabled, true);

    /* Initialize tracker */
    config->tracker.detected_pattern = PATTERN_UNKNOWN;

    return 0;
}

void prefetch_tuning_destroy(prefetch_config_t *config)
{
    if (!config) return;
    atomic_store(&config->enabled, false);
}

void prefetch_tuning_set_enabled(prefetch_config_t *config, bool enable)
{
    if (!config) return;
    atomic_store(&config->enabled, enable);
}

/*******************************************************************************
 * TUNING
 ******************************************************************************/

void prefetch_tune(prefetch_config_t *config)
{
    if (!config) return;

    /* Check if enough samples collected */
    if (config->samples_since_tune < PREFETCH_TUNE_SAMPLES) {
        return;
    }

    /* Compute recommended distance */
    uint32_t current = atomic_load(&config->distance);
    uint32_t recommended = prefetch_compute_distance(config);

    /* Check for oscillation */
    if (recommended != current) {
        config->consecutive_adjustments++;

        /* Prevent thrashing */
        if (config->consecutive_adjustments > 3) {
            /* Too many rapid changes - stabilize */
            recommended = current;
            config->consecutive_adjustments = 0;
        } else {
            /* Apply change */
            atomic_store(&config->distance, recommended);
        }
    } else {
        config->consecutive_adjustments = 0;
    }

    /* Reset counters */
    config->samples_since_tune = 0;
}

/*******************************************************************************
 * STATISTICS
 ******************************************************************************/

void prefetch_get_stats(const prefetch_config_t *config, prefetch_stats_t *stats)
{
    if (!config || !stats) return;

    memset(stats, 0, sizeof(*stats));

    stats->current_distance = atomic_load(&config->distance);
    stats->enabled = atomic_load(&config->enabled);
    stats->detected_pattern = config->tracker.detected_pattern;
    stats->cache_hits = atomic_load(&config->cache_hits);
    stats->cache_misses = atomic_load(&config->cache_misses);
    stats->prefetches_issued = atomic_load(&config->prefetches_issued);
    stats->total_accesses = config->tracker.total_count;

    uint64_t total = stats->cache_hits + stats->cache_misses;
    stats->miss_rate = (total > 0) ? (double)stats->cache_misses / total : 0.0;
}

void prefetch_print_stats(const prefetch_config_t *config)
{
    if (!config) return;

    printf("================================================================================\n");
    printf("PREFETCH TUNING STATISTICS\n");
    printf("================================================================================\n\n");

    prefetch_stats_t stats;
    prefetch_get_stats(config, &stats);

    printf("Configuration:\n");
    printf("  Enabled:           %s\n", stats.enabled ? "Yes" : "No");
    printf("  Distance:          %u cache lines\n", stats.current_distance);
    printf("\n");

    const char *pattern_str;
    switch (stats.detected_pattern) {
        case PATTERN_SEQUENTIAL: pattern_str = "Sequential"; break;
        case PATTERN_STRIDED:    pattern_str = "Strided"; break;
        case PATTERN_RANDOM:     pattern_str = "Random"; break;
        default:                 pattern_str = "Unknown"; break;
    }

    printf("Access Pattern:\n");
    printf("  Detected:          %s\n", pattern_str);
    printf("  Total Accesses:    %u\n", stats.total_accesses);
    printf("\n");

    printf("Performance:\n");
    printf("  Cache Hits:        %lu\n", stats.cache_hits);
    printf("  Cache Misses:      %lu\n", stats.cache_misses);
    printf("  Miss Rate:         %.2f%%\n", stats.miss_rate * 100.0);
    printf("  Prefetches Issued: %lu\n", stats.prefetches_issued);
    printf("\n");

    printf("Expected Performance:\n");
    printf("  Sequential access: 3-8%% improvement\n");
    printf("  Random access:     Reduced pollution\n");
    printf("  Overhead:          <0.5%%\n");

    printf("================================================================================\n");
}
