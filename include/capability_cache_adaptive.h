/**
 * @file capability_cache_adaptive.h
 * @brief Adaptive Capability Cache (Task 5.5.4 - Phase 1)
 *
 * Dynamic cache sizing that adapts to workload characteristics:
 * - Automatic size adjustment (32, 64, 128, 256 entries)
 * - Hit rate monitoring and optimization
 * - Working set size detection
 * - Memory pressure awareness
 * - Zero-configuration adaptation
 *
 * Expected Performance:
 * - 5-10% improvement for varied workloads
 * - Adaptation overhead: <1%
 * - Maintains 80-95% hit rate across workloads
 */

#pragma once

#include "capability_cache.h"
#include <stdint.h>
#include <stdbool.h>
#include <stdatomic.h>

#ifdef __cplusplus
extern "C" {
#endif

/*******************************************************************************
 * CONFIGURATION
 ******************************************************************************/

/** Supported cache sizes (powers of 2 for fast modulo) */
#define CAP_CACHE_SIZE_MIN    32
#define CAP_CACHE_SIZE_SMALL  64
#define CAP_CACHE_SIZE_MEDIUM 128
#define CAP_CACHE_SIZE_LARGE  256

/** Tuning parameters */
#define CAP_CACHE_HIT_RATE_TARGET_LOW   0.80  /**< Increase size if below */
#define CAP_CACHE_HIT_RATE_TARGET_HIGH  0.95  /**< Decrease size if above */
#define CAP_CACHE_WORKING_SET_THRESHOLD 0.90  /**< Utilization threshold */

/** Adaptation frequency */
#define CAP_CACHE_TUNE_INTERVAL_MS  1000  /**< Tune every 1 second */
#define CAP_CACHE_TUNE_MIN_SAMPLES  100   /**< Minimum samples before tuning */

/*******************************************************************************
 * ADAPTIVE CACHE STRUCTURES
 ******************************************************************************/

/**
 * @brief Cache size level
 */
typedef enum {
    CACHE_SIZE_32   = 0,
    CACHE_SIZE_64   = 1,
    CACHE_SIZE_128  = 2,
    CACHE_SIZE_256  = 3,
    CACHE_SIZE_MAX  = 4
} cache_size_level_t;

/**
 * @brief Per-CPU adaptive statistics
 */
typedef struct {
    /* Current metrics */
    _Atomic uint64_t hits_since_tune;
    _Atomic uint64_t misses_since_tune;
    _Atomic uint64_t accesses_since_tune;

    /* Working set tracking */
    _Atomic uint32_t unique_ids_seen;
    uint8_t id_bloom_filter[256];  /**< Simple bloom filter for unique IDs */

    /* Historical metrics */
    double hit_rate_history[4];     /**< Last 4 measurements */
    uint32_t history_index;

    /* Current size level */
    _Atomic cache_size_level_t current_level;

    /* Tuning state */
    uint64_t last_tune_time_ms;
    uint32_t consecutive_resizes;   /**< Prevent oscillation */
} cap_cache_adaptive_stats_t;

/**
 * @brief Adaptive cache (extends base cache)
 */
typedef struct {
    /* Base cache */
    cap_cache_t base;

    /* Adaptive stats per CPU */
    cap_cache_adaptive_stats_t cpu_stats[MAX_CPUS];

    /* Global tuning control */
    _Atomic bool tuning_enabled;
    _Atomic uint64_t global_tune_count;

    /* Memory pressure awareness */
    _Atomic uint64_t total_memory_used;
    uint64_t memory_limit;
} cap_cache_adaptive_t;

/*******************************************************************************
 * INITIALIZATION
 ******************************************************************************/

/**
 * @brief Initialize adaptive cache
 *
 * @param cache    Adaptive cache
 * @param table    Capability table
 * @param num_cpus Number of CPUs
 * @return 0 on success, negative on error
 */
int cap_cache_adaptive_init(cap_cache_adaptive_t *cache,
                            capability_table_t *table,
                            uint8_t num_cpus);

/**
 * @brief Destroy adaptive cache
 *
 * @param cache  Adaptive cache
 */
void cap_cache_adaptive_destroy(cap_cache_adaptive_t *cache);

/**
 * @brief Enable/disable automatic tuning
 *
 * @param cache  Adaptive cache
 * @param enable true to enable, false to disable
 */
void cap_cache_adaptive_set_tuning(cap_cache_adaptive_t *cache, bool enable);

/*******************************************************************************
 * ADAPTIVE OPERATIONS
 ******************************************************************************/

/**
 * @brief Lookup with adaptive caching
 *
 * Same as cap_cache_lookup but updates adaptive statistics.
 *
 * @param cache  Adaptive cache
 * @param id     Capability ID
 * @param cpu    CPU ID
 * @return Capability pointer or NULL
 */
capability_t *cap_cache_adaptive_lookup(cap_cache_adaptive_t *cache,
                                       cap_id_t id, uint8_t cpu);

/**
 * @brief Permission check with adaptive caching
 *
 * @param cache  Adaptive cache
 * @param id     Capability ID
 * @param perm   Permission to check
 * @param cpu    CPU ID
 * @return true if has permission
 */
bool cap_cache_adaptive_has_permission(cap_cache_adaptive_t *cache,
                                       cap_id_t id, uint64_t perm, uint8_t cpu);

/**
 * @brief Invalidate with adaptive tracking
 *
 * @param cache  Adaptive cache
 * @param id     Capability ID
 * @param cpu    CPU ID
 */
void cap_cache_adaptive_invalidate(cap_cache_adaptive_t *cache,
                                   cap_id_t id, uint8_t cpu);

/*******************************************************************************
 * TUNING OPERATIONS
 ******************************************************************************/

/**
 * @brief Manually trigger cache tuning
 *
 * Normally called automatically, but can be called manually.
 *
 * @param cache  Adaptive cache
 * @param cpu    CPU to tune (or ALL_CPUS for all)
 */
void cap_cache_adaptive_tune(cap_cache_adaptive_t *cache, uint8_t cpu);

/**
 * @brief Get current cache size for CPU
 *
 * @param cache  Adaptive cache
 * @param cpu    CPU ID
 * @return Current cache size (32, 64, 128, or 256)
 */
uint32_t cap_cache_adaptive_get_size(const cap_cache_adaptive_t *cache,
                                     uint8_t cpu);

/**
 * @brief Manually set cache size level
 *
 * Overrides automatic tuning.
 *
 * @param cache  Adaptive cache
 * @param cpu    CPU ID
 * @param level  Desired size level
 * @return 0 on success, negative on error
 */
int cap_cache_adaptive_set_size(cap_cache_adaptive_t *cache, uint8_t cpu,
                                cache_size_level_t level);

/*******************************************************************************
 * TUNING ALGORITHMS
 ******************************************************************************/

/**
 * @brief Compute recommended cache size
 *
 * Based on hit rate, working set size, and memory pressure.
 *
 * @param cache  Adaptive cache
 * @param cpu    CPU ID
 * @return Recommended size level
 */
static inline cache_size_level_t cap_cache_compute_recommended_size(
    const cap_cache_adaptive_t *cache, uint8_t cpu)
{
    if (!cache || cpu >= cache->base.num_cpus) {
        return CACHE_SIZE_64;  /* Default */
    }

    const cap_cache_adaptive_stats_t *stats = &cache->cpu_stats[cpu];
    cache_size_level_t current = atomic_load(&stats->current_level);

    /* Compute current hit rate */
    uint64_t hits = atomic_load(&stats->hits_since_tune);
    uint64_t misses = atomic_load(&stats->misses_since_tune);
    uint64_t total = hits + misses;

    if (total < CAP_CACHE_TUNE_MIN_SAMPLES) {
        return current;  /* Not enough data */
    }

    double hit_rate = (double)hits / total;

    /* Check working set utilization */
    uint32_t unique_ids = atomic_load(&stats->unique_ids_seen);
    uint32_t current_size = cap_cache_adaptive_get_size(cache, cpu);
    double utilization = (double)unique_ids / current_size;

    /* Decision logic */

    /* 1. Hit rate too low - increase size */
    if (hit_rate < CAP_CACHE_HIT_RATE_TARGET_LOW) {
        if (current < CACHE_SIZE_256) {
            return current + 1;  /* Increase one level */
        }
        return CACHE_SIZE_256;  /* Already at max */
    }

    /* 2. Working set larger than cache - increase size */
    if (utilization > CAP_CACHE_WORKING_SET_THRESHOLD) {
        if (current < CACHE_SIZE_256) {
            return current + 1;
        }
        return CACHE_SIZE_256;
    }

    /* 3. Hit rate excellent and memory pressure - decrease size */
    if (hit_rate > CAP_CACHE_HIT_RATE_TARGET_HIGH) {
        uint64_t mem_used = atomic_load(&cache->total_memory_used);
        if (mem_used > cache->memory_limit * 0.8) {
            if (current > CACHE_SIZE_32) {
                return current - 1;  /* Decrease one level */
            }
        }
    }

    /* 4. Default: keep current size */
    return current;
}

/**
 * @brief Check if tuning should run
 *
 * @param cache  Adaptive cache
 * @param cpu    CPU ID
 * @return true if tuning should run
 */
static inline bool cap_cache_should_tune(const cap_cache_adaptive_t *cache,
                                        uint8_t cpu)
{
    if (!atomic_load(&cache->tuning_enabled)) {
        return false;
    }

    if (cpu >= cache->base.num_cpus) {
        return false;
    }

    /* Check if enough samples collected */
    const cap_cache_adaptive_stats_t *stats = &cache->cpu_stats[cpu];
    uint64_t accesses = atomic_load(&stats->accesses_since_tune);

    return accesses >= CAP_CACHE_TUNE_MIN_SAMPLES;
}

/**
 * @brief Update bloom filter for unique ID tracking
 *
 * @param stats  Adaptive stats
 * @param id     Capability ID
 */
static inline void cap_cache_update_bloom_filter(cap_cache_adaptive_stats_t *stats,
                                                 cap_id_t id)
{
    /* Simple bloom filter: use two hash functions */
    uint8_t hash1 = (id ^ (id >> 8)) & 0xFF;
    uint8_t hash2 = ((id >> 16) ^ (id >> 24)) & 0xFF;

    bool was_set1 = stats->id_bloom_filter[hash1] != 0;
    bool was_set2 = stats->id_bloom_filter[hash2] != 0;

    stats->id_bloom_filter[hash1] = 1;
    stats->id_bloom_filter[hash2] = 1;

    /* If either was unset, likely a new unique ID */
    if (!was_set1 || !was_set2) {
        atomic_fetch_add(&stats->unique_ids_seen, 1);
    }
}

/*******************************************************************************
 * STATISTICS
 ******************************************************************************/

/**
 * @brief Adaptive cache statistics
 */
typedef struct {
    /* Per-CPU stats */
    struct {
        cache_size_level_t current_level;
        uint32_t current_size;
        double current_hit_rate;
        uint32_t unique_ids;
        uint32_t total_resizes;
    } cpus[MAX_CPUS];

    /* Global stats */
    uint64_t total_tune_count;
    uint64_t total_memory_used;
    bool tuning_enabled;
} cap_cache_adaptive_stats_full_t;

/**
 * @brief Get adaptive cache statistics
 *
 * @param cache  Adaptive cache
 * @param stats  Output statistics
 */
void cap_cache_adaptive_get_stats(const cap_cache_adaptive_t *cache,
                                  cap_cache_adaptive_stats_full_t *stats);

/**
 * @brief Print adaptive cache statistics
 *
 * @param cache  Adaptive cache
 */
void cap_cache_adaptive_print_stats(const cap_cache_adaptive_t *cache);

#ifdef __cplusplus
}
#endif
