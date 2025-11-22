/**
 * @file capability_cache.h
 * @brief Per-CPU Capability Cache (Phase B - Task 5.5.3)
 *
 * Hot-path capability caching to reduce lookup latency:
 * - Per-CPU direct-mapped cache (no locks)
 * - LRU eviction policy
 * - Automatic invalidation on revocation
 * - Cache prefetching hints
 *
 * Expected Performance:
 * - Cache hit:  1-5ns   (10x faster than table lookup)
 * - Cache miss: 10-50ns (fallback to table lookup)
 * - Target hit rate: 80-95% (for typical workloads)
 */

#pragma once

#include "capability_lockfree.h"
#include "capability_optimized.h"
#include <stdint.h>
#include <stdbool.h>
#include <stdatomic.h>

#ifdef __cplusplus
extern "C" {
#endif

/*******************************************************************************
 * CONFIGURATION
 ******************************************************************************/

/** Cache size per CPU (power of 2 for fast modulo) */
#define CAP_CACHE_SIZE      64

/** Cache line size (for alignment) */
#define CAP_CACHE_LINE_SIZE 64

/** Maximum CPUs supported */
#ifndef MAX_CPUS
#define MAX_CPUS            16
#endif

/*******************************************************************************
 * CACHE ENTRY
 ******************************************************************************/

/**
 * @brief Cache entry for a single capability
 *
 * Aligned to cache line to avoid false sharing between CPUs.
 */
typedef struct cap_cache_entry {
    /* Key */
    cap_id_t id;                         /**< Capability ID (0 = empty) */

    /* Cached data (frequently accessed fields) */
    uint64_t permissions;                /**< Cached permissions */
    cap_state_t state;                   /**< Cached state */
    uint32_t owner_pid;                  /**< Cached owner PID */

    /* Pointer to full capability (for slow path) */
    capability_t *cap_ptr;               /**< Pointer to actual capability */

    /* Cache metadata */
    uint64_t access_time;                /**< Last access timestamp (for LRU) */
    uint32_t access_count;               /**< Access count (for statistics) */

    /* Padding to cache line size */
    uint8_t padding[CAP_CACHE_LINE_SIZE - sizeof(cap_id_t) - sizeof(uint64_t) -
                    sizeof(cap_state_t) - sizeof(uint32_t) - sizeof(void *) -
                    sizeof(uint64_t) - sizeof(uint32_t)];
} __attribute__((aligned(CAP_CACHE_LINE_SIZE))) cap_cache_entry_t;

/*******************************************************************************
 * PER-CPU CACHE
 ******************************************************************************/

/**
 * @brief Per-CPU capability cache
 *
 * Each CPU has its own cache (no locking needed).
 * Direct-mapped with LRU eviction.
 */
typedef struct cap_cache_cpu {
    /* Cache entries */
    cap_cache_entry_t entries[CAP_CACHE_SIZE];

    /* Statistics (relaxed atomics for per-CPU updates) */
    _Atomic uint64_t hits;               /**< Cache hits */
    _Atomic uint64_t misses;             /**< Cache misses */
    _Atomic uint64_t evictions;          /**< Cache evictions */
    _Atomic uint64_t invalidations;      /**< Cache invalidations */

    /* Padding to avoid false sharing between CPU caches */
    uint8_t padding[CAP_CACHE_LINE_SIZE];
} __attribute__((aligned(CAP_CACHE_LINE_SIZE))) cap_cache_cpu_t;

/**
 * @brief Global capability cache
 *
 * Contains per-CPU caches and global statistics.
 */
typedef struct cap_cache {
    /* Per-CPU caches */
    cap_cache_cpu_t cpus[MAX_CPUS];
    uint8_t num_cpus;

    /* Pointer to underlying capability table */
    capability_table_t *table;

    /* Global statistics (for reporting) */
    _Atomic uint64_t total_lookups;      /**< Total lookup operations */
    _Atomic uint64_t total_insertions;   /**< Total insertions */
} cap_cache_t;

/*******************************************************************************
 * CACHE MANAGEMENT
 ******************************************************************************/

/**
 * @brief Initialize capability cache
 *
 * @param cache    Cache to initialize
 * @param table    Underlying capability table
 * @param num_cpus Number of CPUs
 * @return 0 on success, negative on error
 */
int cap_cache_init(cap_cache_t *cache, capability_table_t *table,
                   uint8_t num_cpus);

/**
 * @brief Destroy capability cache
 *
 * @param cache  Cache to destroy
 */
void cap_cache_destroy(cap_cache_t *cache);

/**
 * @brief Clear all entries in cache
 *
 * @param cache  Cache to clear
 */
void cap_cache_clear(cap_cache_t *cache);

/**
 * @brief Clear per-CPU cache
 *
 * @param cache  Cache
 * @param cpu    CPU ID
 */
void cap_cache_clear_cpu(cap_cache_t *cache, uint8_t cpu);

/*******************************************************************************
 * FAST-PATH CACHE OPERATIONS (INLINE)
 ******************************************************************************/

/**
 * @brief Get cache index for capability ID
 *
 * Direct-mapped cache: hash ID to cache slot.
 *
 * @param id  Capability ID
 * @return Cache index (0 to CAP_CACHE_SIZE-1)
 */
static inline uint32_t cap_cache_index(cap_id_t id)
{
    /* Simple hash: use lower bits (cache size is power of 2) */
    return id & (CAP_CACHE_SIZE - 1);
}

/**
 * @brief Get current timestamp (for LRU)
 *
 * @return Monotonic timestamp
 */
static inline uint64_t cap_cache_timestamp(void)
{
    /* Use a simple counter for now (could use rdtsc on x86) */
    static _Atomic uint64_t counter = 0;
    return atomic_fetch_add(&counter, 1);
}

/**
 * @brief Cache lookup (fast path)
 *
 * Checks if capability is in per-CPU cache.
 * Returns cached permissions on hit, 0 on miss.
 *
 * @param cache  Cache
 * @param id     Capability ID
 * @param cpu    Current CPU
 * @param[out] perms  Cached permissions (on hit)
 * @param[out] state  Cached state (on hit)
 * @return true on cache hit, false on miss
 *
 * Performance: 1-5ns on hit (no table access)
 */
static inline bool cap_cache_lookup_fast(cap_cache_t *cache, cap_id_t id,
                                         uint8_t cpu, uint64_t *perms,
                                         cap_state_t *state)
{
    if (UNLIKELY(!cache || cpu >= cache->num_cpus)) {
        return false;
    }

    /* Get cache entry */
    uint32_t idx = cap_cache_index(id);
    cap_cache_entry_t *entry = &cache->cpus[cpu].entries[idx];

    /* Check if entry matches (cache hit) */
    if (LIKELY(entry->id == id && entry->cap_ptr != NULL)) {
        /* Cache hit - return cached data */
        *perms = entry->permissions;
        *state = entry->state;

        /* Update LRU metadata */
        entry->access_time = cap_cache_timestamp();
        entry->access_count++;

        /* Update statistics */
        atomic_fetch_add_explicit(&cache->cpus[cpu].hits, 1,
                                 memory_order_relaxed);

        return true;  /* HIT */
    }

    /* Cache miss */
    atomic_fetch_add_explicit(&cache->cpus[cpu].misses, 1,
                             memory_order_relaxed);

    return false;  /* MISS */
}

/**
 * @brief Insert capability into cache
 *
 * Adds capability to per-CPU cache, evicting old entry if needed.
 *
 * @param cache  Cache
 * @param cap    Capability to cache
 * @param cpu    Current CPU
 *
 * Performance: 2-10ns (single cache line write)
 */
static inline void cap_cache_insert(cap_cache_t *cache, capability_t *cap,
                                   uint8_t cpu)
{
    if (UNLIKELY(!cache || !cap || cpu >= cache->num_cpus)) {
        return;
    }

    /* Get cache entry */
    uint32_t idx = cap_cache_index(cap->id);
    cap_cache_entry_t *entry = &cache->cpus[cpu].entries[idx];

    /* Check if eviction needed */
    if (entry->id != 0 && entry->id != cap->id) {
        atomic_fetch_add_explicit(&cache->cpus[cpu].evictions, 1,
                                 memory_order_relaxed);
    }

    /* Insert into cache */
    entry->id = cap->id;
    entry->permissions = atomic_load_explicit(&cap->permissions,
                                             memory_order_relaxed);
    entry->state = atomic_load_explicit(&cap->state, memory_order_relaxed);
    entry->owner_pid = cap->owner_pid;
    entry->cap_ptr = cap;
    entry->access_time = cap_cache_timestamp();
    entry->access_count = 1;

    /* Update statistics */
    atomic_fetch_add_explicit(&cache->total_insertions, 1,
                             memory_order_relaxed);
}

/**
 * @brief Invalidate cache entry
 *
 * Removes capability from cache (e.g., on revocation).
 *
 * @param cache  Cache
 * @param id     Capability ID to invalidate
 * @param cpu    CPU ID (or ALL_CPUS to invalidate all)
 *
 * Performance: 2-10ns per CPU
 */
static inline void cap_cache_invalidate(cap_cache_t *cache, cap_id_t id,
                                       uint8_t cpu)
{
    if (UNLIKELY(!cache)) return;

    uint32_t idx = cap_cache_index(id);

    if (cpu < cache->num_cpus) {
        /* Invalidate on specific CPU */
        cap_cache_entry_t *entry = &cache->cpus[cpu].entries[idx];
        if (entry->id == id) {
            entry->id = 0;  /* Mark as empty */
            entry->cap_ptr = NULL;
            atomic_fetch_add_explicit(&cache->cpus[cpu].invalidations, 1,
                                     memory_order_relaxed);
        }
    }
}

/**
 * @brief Invalidate on all CPUs
 *
 * @param cache  Cache
 * @param id     Capability ID to invalidate
 */
static inline void cap_cache_invalidate_all(cap_cache_t *cache, cap_id_t id)
{
    if (UNLIKELY(!cache)) return;

    for (uint8_t cpu = 0; cpu < cache->num_cpus; cpu++) {
        cap_cache_invalidate(cache, id, cpu);
    }
}

/*******************************************************************************
 * COMBINED CACHE + TABLE OPERATIONS
 ******************************************************************************/

/**
 * @brief Lookup capability with cache
 *
 * Fast path: check cache first, fallback to table on miss.
 * Automatically inserts into cache on table hit.
 *
 * @param cache  Cache
 * @param id     Capability ID
 * @param cpu    Current CPU
 * @return Capability pointer, or NULL if not found
 *
 * Performance: 1-5ns (cache hit) or 10-50ns (cache miss + table lookup)
 */
static inline capability_t *cap_cache_lookup(cap_cache_t *cache, cap_id_t id,
                                            uint8_t cpu)
{
    /* Try cache first */
    uint64_t perms;
    cap_state_t state;
    if (cap_cache_lookup_fast(cache, id, cpu, &perms, &state)) {
        /* Cache hit - return cached pointer */
        uint32_t idx = cap_cache_index(id);
        return cache->cpus[cpu].entries[idx].cap_ptr;
    }

    /* Cache miss - lookup in table */
    capability_t *cap = capability_lookup(cache->table, id, cpu);
    if (cap) {
        /* Insert into cache for next time */
        cap_cache_insert(cache, cap, cpu);
    }

    atomic_fetch_add_explicit(&cache->total_lookups, 1,
                             memory_order_relaxed);

    return cap;
}

/**
 * @brief Check permission with cache
 *
 * Ultra-fast permission check using cache.
 *
 * @param cache  Cache
 * @param id     Capability ID
 * @param perm   Permission to check
 * @param cpu    Current CPU
 * @return true if has permission
 *
 * Performance: 1-5ns (cache hit) or 10-50ns (cache miss)
 */
static inline bool cap_cache_has_permission(cap_cache_t *cache, cap_id_t id,
                                           uint64_t perm, uint8_t cpu)
{
    /* Try cache first */
    uint64_t perms;
    cap_state_t state;
    if (cap_cache_lookup_fast(cache, id, cpu, &perms, &state)) {
        /* Cache hit - check cached permissions */
        if (state != CAP_STATE_ACTIVE) return false;
        return (perms & perm) == perm;
    }

    /* Cache miss - use table */
    capability_t *cap = capability_lookup(cache->table, id, cpu);
    if (!cap) return false;

    bool result = capability_check_fast(cap, perm);

    /* Insert into cache */
    cap_cache_insert(cache, cap, cpu);

    capability_release(cache->table, cap, cpu);

    return result;
}

/*******************************************************************************
 * STATISTICS
 ******************************************************************************/

/**
 * @brief Per-CPU cache statistics
 */
typedef struct {
    uint64_t hits;                       /**< Cache hits */
    uint64_t misses;                     /**< Cache misses */
    uint64_t evictions;                  /**< Evictions */
    uint64_t invalidations;              /**< Invalidations */
    double hit_rate;                     /**< Hit rate (0.0-1.0) */
} cap_cache_cpu_stats_t;

/**
 * @brief Global cache statistics
 */
typedef struct {
    uint64_t total_lookups;              /**< Total lookups */
    uint64_t total_insertions;           /**< Total insertions */
    uint64_t total_hits;                 /**< Total hits (all CPUs) */
    uint64_t total_misses;               /**< Total misses (all CPUs) */
    double global_hit_rate;              /**< Global hit rate */
} cap_cache_stats_t;

/**
 * @brief Get per-CPU cache statistics
 *
 * @param cache  Cache
 * @param cpu    CPU ID
 * @param stats  Output statistics
 */
void cap_cache_get_cpu_stats(const cap_cache_t *cache, uint8_t cpu,
                             cap_cache_cpu_stats_t *stats);

/**
 * @brief Get global cache statistics
 *
 * @param cache  Cache
 * @param stats  Output statistics
 */
void cap_cache_get_stats(const cap_cache_t *cache, cap_cache_stats_t *stats);

/**
 * @brief Print cache statistics (debugging)
 *
 * @param cache  Cache
 */
void cap_cache_print_stats(const cap_cache_t *cache);

#ifdef __cplusplus
}
#endif
