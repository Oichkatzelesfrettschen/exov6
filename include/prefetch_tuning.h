/**
 * @file prefetch_tuning.h
 * @brief Adaptive Prefetch Distance Tuning (Task 5.5.4 - Phase 3)
 *
 * Auto-tuning prefetch distance based on:
 * - Access patterns (sequential vs random)
 * - Cache miss rates
 * - Memory latency
 *
 * Expected Performance:
 * - 3-8% improvement for sequential access
 * - Reduced cache pollution for random access
 * - Overhead: <0.5%
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <stdatomic.h>

#ifdef __cplusplus
extern "C" {
#endif

/*******************************************************************************
 * CONFIGURATION
 ******************************************************************************/

/** Prefetch distance options */
#define PREFETCH_DIST_NONE      0   /**< No prefetching */
#define PREFETCH_DIST_SMALL     2   /**< 2 cache lines ahead */
#define PREFETCH_DIST_MEDIUM    4   /**< 4 cache lines ahead */
#define PREFETCH_DIST_LARGE     8   /**< 8 cache lines ahead */
#define PREFETCH_DIST_AGGRESSIVE 16 /**< 16 cache lines ahead */

/** Tuning parameters */
#define PREFETCH_TUNE_SAMPLES   1000  /**< Samples before tuning */
#define PREFETCH_SEQ_THRESHOLD  0.8   /**< Sequential detection threshold */
#define PREFETCH_MISS_HIGH      0.1   /**< High miss rate threshold */
#define PREFETCH_MISS_LOW       0.02  /**< Low miss rate threshold */

/*******************************************************************************
 * ACCESS PATTERN DETECTION
 ******************************************************************************/

/**
 * @brief Access pattern type
 */
typedef enum {
    PATTERN_UNKNOWN,
    PATTERN_SEQUENTIAL,    /**< Sequential access (stride 1) */
    PATTERN_STRIDED,       /**< Regular stride access */
    PATTERN_RANDOM         /**< Random access */
} access_pattern_t;

/**
 * @brief Access tracker
 */
typedef struct {
    uint64_t last_addresses[16];  /**< Last 16 addresses */
    uint32_t index;               /**< Current index in ring buffer */
    uint32_t sequential_count;    /**< Count of sequential accesses */
    uint32_t total_count;         /**< Total accesses */
    access_pattern_t detected_pattern;
} access_tracker_t;

/*******************************************************************************
 * PREFETCH CONFIGURATION
 ******************************************************************************/

/**
 * @brief Prefetch configuration
 */
typedef struct {
    /* Current settings */
    _Atomic uint32_t distance;        /**< Current prefetch distance */
    _Atomic bool enabled;             /**< Prefetching enabled */

    /* Access pattern tracking */
    access_tracker_t tracker;

    /* Performance counters */
    _Atomic uint64_t cache_hits;
    _Atomic uint64_t cache_misses;
    _Atomic uint64_t prefetches_issued;

    /* Tuning state */
    uint64_t samples_since_tune;
    uint32_t consecutive_adjustments;
} prefetch_config_t;

/*******************************************************************************
 * INITIALIZATION
 ******************************************************************************/

/**
 * @brief Initialize prefetch tuning
 *
 * @param config  Prefetch configuration
 * @return 0 on success, negative on error
 */
int prefetch_tuning_init(prefetch_config_t *config);

/**
 * @brief Destroy prefetch tuning
 *
 * @param config  Prefetch configuration
 */
void prefetch_tuning_destroy(prefetch_config_t *config);

/**
 * @brief Enable/disable prefetching
 *
 * @param config  Prefetch configuration
 * @param enable  true to enable, false to disable
 */
void prefetch_tuning_set_enabled(prefetch_config_t *config, bool enable);

/*******************************************************************************
 * ACCESS PATTERN DETECTION
 ******************************************************************************/

/**
 * @brief Track memory access
 *
 * Updates access pattern detection.
 *
 * @param tracker  Access tracker
 * @param address  Memory address accessed
 */
static inline void prefetch_track_access(access_tracker_t *tracker, uint64_t address)
{
    if (!tracker) return;

    /* Store in ring buffer */
    tracker->last_addresses[tracker->index] = address;
    tracker->index = (tracker->index + 1) % 16;
    tracker->total_count++;

    /* Check if sequential (stride 64 bytes = cache line) */
    if (tracker->total_count > 1) {
        uint32_t prev_idx = (tracker->index + 15) % 16;
        uint64_t prev_addr = tracker->last_addresses[prev_idx];
        int64_t diff = (int64_t)address - (int64_t)prev_addr;

        /* Sequential if difference is one cache line */
        if (diff == 64 || diff == -64) {
            tracker->sequential_count++;
        }
    }

    /* Update pattern every 16 accesses */
    if (tracker->total_count % 16 == 0 && tracker->total_count >= 16) {
        double seq_ratio = (double)tracker->sequential_count / 16;

        if (seq_ratio >= PREFETCH_SEQ_THRESHOLD) {
            tracker->detected_pattern = PATTERN_SEQUENTIAL;
        } else if (seq_ratio >= 0.5) {
            tracker->detected_pattern = PATTERN_STRIDED;
        } else {
            tracker->detected_pattern = PATTERN_RANDOM;
        }

        /* Reset for next window */
        tracker->sequential_count = 0;
    }
}

/**
 * @brief Get detected access pattern
 *
 * @param tracker  Access tracker
 * @return Detected pattern
 */
static inline access_pattern_t prefetch_get_pattern(const access_tracker_t *tracker)
{
    return tracker ? tracker->detected_pattern : PATTERN_UNKNOWN;
}

/*******************************************************************************
 * ADAPTIVE PREFETCHING
 ******************************************************************************/

/**
 * @brief Issue prefetch with adaptive distance
 *
 * @param config   Prefetch configuration
 * @param address  Base address
 */
static inline void prefetch_adaptive(prefetch_config_t *config, void *address)
{
    if (!config || !atomic_load(&config->enabled)) {
        return;
    }

    uint32_t distance = atomic_load(&config->distance);
    if (distance == 0) return;

    /* Prefetch ahead by distance cache lines */
    char *ptr = (char *)address;
    for (uint32_t i = 1; i <= distance; i++) {
        __builtin_prefetch(ptr + i * 64, 0, 3);  /* Read, high temporal locality */
    }

    atomic_fetch_add(&config->prefetches_issued, 1);
}

/**
 * @brief Record cache hit
 *
 * @param config  Prefetch configuration
 */
static inline void prefetch_record_hit(prefetch_config_t *config)
{
    if (!config) return;
    atomic_fetch_add(&config->cache_hits, 1);
}

/**
 * @brief Record cache miss
 *
 * @param config  Prefetch configuration
 */
static inline void prefetch_record_miss(prefetch_config_t *config)
{
    if (!config) return;
    atomic_fetch_add(&config->cache_misses, 1);
}

/*******************************************************************************
 * TUNING
 ******************************************************************************/

/**
 * @brief Tune prefetch distance
 *
 * Adjusts prefetch distance based on access pattern and miss rate.
 *
 * @param config  Prefetch configuration
 */
void prefetch_tune(prefetch_config_t *config);

/**
 * @brief Compute recommended prefetch distance
 *
 * @param config  Prefetch configuration
 * @return Recommended distance
 */
static inline uint32_t prefetch_compute_distance(const prefetch_config_t *config)
{
    if (!config) return PREFETCH_DIST_MEDIUM;

    /* Get access pattern */
    access_pattern_t pattern = prefetch_get_pattern(&config->tracker);

    /* Calculate miss rate */
    uint64_t hits = atomic_load(&config->cache_hits);
    uint64_t misses = atomic_load(&config->cache_misses);
    uint64_t total = hits + misses;

    double miss_rate = (total > 0) ? (double)misses / total : 0.0;

    uint32_t current = atomic_load(&config->distance);

    /* Decision logic based on pattern and miss rate */
    switch (pattern) {
        case PATTERN_SEQUENTIAL:
            /* Sequential access - aggressive prefetching helps */
            if (miss_rate > PREFETCH_MISS_HIGH) {
                return PREFETCH_DIST_AGGRESSIVE;  /* 16 cache lines */
            } else if (miss_rate > PREFETCH_MISS_LOW) {
                return PREFETCH_DIST_LARGE;       /* 8 cache lines */
            } else {
                return PREFETCH_DIST_MEDIUM;      /* 4 cache lines */
            }

        case PATTERN_STRIDED:
            /* Regular stride - moderate prefetching */
            if (miss_rate > PREFETCH_MISS_HIGH) {
                return PREFETCH_DIST_LARGE;
            } else {
                return PREFETCH_DIST_MEDIUM;
            }

        case PATTERN_RANDOM:
            /* Random access - minimal prefetching (reduces pollution) */
            if (miss_rate > PREFETCH_MISS_HIGH) {
                return PREFETCH_DIST_SMALL;       /* 2 cache lines */
            } else {
                return PREFETCH_DIST_NONE;        /* Disable */
            }

        default:
            /* Unknown - use conservative default */
            return PREFETCH_DIST_MEDIUM;
    }
}

/*******************************************************************************
 * STATISTICS
 ******************************************************************************/

/**
 * @brief Prefetch statistics
 */
typedef struct {
    uint32_t current_distance;
    bool enabled;
    access_pattern_t detected_pattern;
    uint64_t cache_hits;
    uint64_t cache_misses;
    double miss_rate;
    uint64_t prefetches_issued;
    uint32_t total_accesses;
} prefetch_stats_t;

/**
 * @brief Get prefetch statistics
 *
 * @param config  Prefetch configuration
 * @param stats   Output statistics
 */
void prefetch_get_stats(const prefetch_config_t *config, prefetch_stats_t *stats);

/**
 * @brief Print prefetch statistics
 *
 * @param config  Prefetch configuration
 */
void prefetch_print_stats(const prefetch_config_t *config);

#ifdef __cplusplus
}
#endif
