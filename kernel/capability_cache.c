/**
 * @file capability_cache.c
 * @brief Per-CPU Capability Cache Implementation (Phase B)
 *
 * Implementation of hot-path capability caching.
 */

#include "capability_cache.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

/*******************************************************************************
 * INITIALIZATION AND DESTRUCTION
 ******************************************************************************/

int cap_cache_init(cap_cache_t *cache, capability_table_t *table,
                   uint8_t num_cpus)
{
    if (!cache || !table || num_cpus == 0 || num_cpus > MAX_CPUS) {
        return -1;
    }

    /* Initialize cache */
    memset(cache, 0, sizeof(cap_cache_t));
    cache->table = table;
    cache->num_cpus = num_cpus;

    /* Initialize per-CPU caches */
    for (uint8_t cpu = 0; cpu < num_cpus; cpu++) {
        /* Clear entries */
        for (uint32_t i = 0; i < CAP_CACHE_SIZE; i++) {
            cache->cpus[cpu].entries[i].id = 0;  /* Mark as empty */
            cache->cpus[cpu].entries[i].cap_ptr = NULL;
        }

        /* Reset statistics */
        atomic_store(&cache->cpus[cpu].hits, 0);
        atomic_store(&cache->cpus[cpu].misses, 0);
        atomic_store(&cache->cpus[cpu].evictions, 0);
        atomic_store(&cache->cpus[cpu].invalidations, 0);
    }

    /* Reset global statistics */
    atomic_store(&cache->total_lookups, 0);
    atomic_store(&cache->total_insertions, 0);

    return 0;
}

void cap_cache_destroy(cap_cache_t *cache)
{
    if (!cache) return;

    /* Clear all caches */
    cap_cache_clear(cache);

    /* Reset pointers */
    cache->table = NULL;
    cache->num_cpus = 0;
}

/*******************************************************************************
 * CACHE CLEARING
 ******************************************************************************/

void cap_cache_clear(cap_cache_t *cache)
{
    if (!cache) return;

    /* Clear all per-CPU caches */
    for (uint8_t cpu = 0; cpu < cache->num_cpus; cpu++) {
        cap_cache_clear_cpu(cache, cpu);
    }
}

void cap_cache_clear_cpu(cap_cache_t *cache, uint8_t cpu)
{
    if (!cache || cpu >= cache->num_cpus) return;

    /* Clear all entries */
    for (uint32_t i = 0; i < CAP_CACHE_SIZE; i++) {
        cache->cpus[cpu].entries[i].id = 0;
        cache->cpus[cpu].entries[i].cap_ptr = NULL;
        cache->cpus[cpu].entries[i].access_time = 0;
        cache->cpus[cpu].entries[i].access_count = 0;
    }
}

/*******************************************************************************
 * STATISTICS
 ******************************************************************************/

void cap_cache_get_cpu_stats(const cap_cache_t *cache, uint8_t cpu,
                             cap_cache_cpu_stats_t *stats)
{
    if (!cache || !stats || cpu >= cache->num_cpus) {
        return;
    }

    /* Read atomic statistics with relaxed ordering */
    stats->hits = atomic_load_explicit(&cache->cpus[cpu].hits,
                                      memory_order_relaxed);
    stats->misses = atomic_load_explicit(&cache->cpus[cpu].misses,
                                        memory_order_relaxed);
    stats->evictions = atomic_load_explicit(&cache->cpus[cpu].evictions,
                                           memory_order_relaxed);
    stats->invalidations = atomic_load_explicit(&cache->cpus[cpu].invalidations,
                                               memory_order_relaxed);

    /* Calculate hit rate */
    uint64_t total = stats->hits + stats->misses;
    if (total > 0) {
        stats->hit_rate = (double)stats->hits / (double)total;
    } else {
        stats->hit_rate = 0.0;
    }
}

void cap_cache_get_stats(const cap_cache_t *cache, cap_cache_stats_t *stats)
{
    if (!cache || !stats) {
        return;
    }

    /* Read global statistics */
    stats->total_lookups = atomic_load_explicit(&cache->total_lookups,
                                               memory_order_relaxed);
    stats->total_insertions = atomic_load_explicit(&cache->total_insertions,
                                                  memory_order_relaxed);

    /* Aggregate per-CPU statistics */
    stats->total_hits = 0;
    stats->total_misses = 0;

    for (uint8_t cpu = 0; cpu < cache->num_cpus; cpu++) {
        stats->total_hits += atomic_load_explicit(&cache->cpus[cpu].hits,
                                                 memory_order_relaxed);
        stats->total_misses += atomic_load_explicit(&cache->cpus[cpu].misses,
                                                   memory_order_relaxed);
    }

    /* Calculate global hit rate */
    uint64_t total = stats->total_hits + stats->total_misses;
    if (total > 0) {
        stats->global_hit_rate = (double)stats->total_hits / (double)total;
    } else {
        stats->global_hit_rate = 0.0;
    }
}

void cap_cache_print_stats(const cap_cache_t *cache)
{
    if (!cache) return;

    printf("================================================================================\n");
    printf("CAPABILITY CACHE STATISTICS\n");
    printf("================================================================================\n\n");

    /* Global statistics */
    cap_cache_stats_t global;
    cap_cache_get_stats(cache, &global);

    printf("Global Statistics:\n");
    printf("  Total Lookups:     %lu\n", global.total_lookups);
    printf("  Total Insertions:  %lu\n", global.total_insertions);
    printf("  Total Hits:        %lu\n", global.total_hits);
    printf("  Total Misses:      %lu\n", global.total_misses);
    printf("  Global Hit Rate:   %.2f%%\n", global.global_hit_rate * 100.0);
    printf("\n");

    /* Per-CPU statistics */
    printf("Per-CPU Statistics:\n");
    printf("  CPU | Hits      | Misses    | Evictions | Invalidations | Hit Rate\n");
    printf("  ----+-----------+-----------+-----------+---------------+---------\n");

    for (uint8_t cpu = 0; cpu < cache->num_cpus; cpu++) {
        cap_cache_cpu_stats_t cpu_stats;
        cap_cache_get_cpu_stats(cache, cpu, &cpu_stats);

        printf("  %3d | %9lu | %9lu | %9lu | %13lu | %6.2f%%\n",
               cpu,
               cpu_stats.hits,
               cpu_stats.misses,
               cpu_stats.evictions,
               cpu_stats.invalidations,
               cpu_stats.hit_rate * 100.0);
    }

    printf("\n");

    /* Cache occupancy */
    printf("Cache Occupancy:\n");
    printf("  CPU | Occupied | Empty | Occupancy\n");
    printf("  ----+----------+-------+----------\n");

    for (uint8_t cpu = 0; cpu < cache->num_cpus; cpu++) {
        uint32_t occupied = 0;
        for (uint32_t i = 0; i < CAP_CACHE_SIZE; i++) {
            if (cache->cpus[cpu].entries[i].id != 0) {
                occupied++;
            }
        }
        uint32_t empty = CAP_CACHE_SIZE - occupied;
        double occupancy = (double)occupied / CAP_CACHE_SIZE;

        printf("  %3d | %8d | %5d | %6.2f%%\n",
               cpu, occupied, empty, occupancy * 100.0);
    }

    printf("\n");

    /* Top accessed capabilities (CPU 0 for example) */
    if (cache->num_cpus > 0) {
        printf("Most Accessed Capabilities (CPU 0):\n");
        printf("  Cap ID   | Access Count | Last Access\n");
        printf("  ---------+--------------+------------\n");

        /* Find top 10 by access count */
        #define TOP_N 10
        cap_cache_entry_t *top[TOP_N] = {NULL};

        for (uint32_t i = 0; i < CAP_CACHE_SIZE; i++) {
            cap_cache_entry_t *entry = &cache->cpus[0].entries[i];
            if (entry->id == 0) continue;

            /* Insert into top list */
            for (int j = 0; j < TOP_N; j++) {
                if (!top[j] || entry->access_count > top[j]->access_count) {
                    /* Shift down */
                    for (int k = TOP_N - 1; k > j; k--) {
                        top[k] = top[k - 1];
                    }
                    top[j] = entry;
                    break;
                }
            }
        }

        /* Print top entries */
        for (int i = 0; i < TOP_N && top[i]; i++) {
            printf("  %8d | %12u | %10lu\n",
                   top[i]->id,
                   top[i]->access_count,
                   top[i]->access_time);
        }
    }

    printf("\n");
    printf("Cache Configuration:\n");
    printf("  Cache Size per CPU: %d entries\n", CAP_CACHE_SIZE);
    printf("  Total CPUs:         %d\n", cache->num_cpus);
    printf("  Total Cache Size:   %d entries\n", CAP_CACHE_SIZE * cache->num_cpus);
    printf("  Memory per CPU:     %zu bytes\n", sizeof(cap_cache_cpu_t));
    printf("  Total Memory:       %zu bytes\n", sizeof(cap_cache_t));
    printf("\n");

    printf("Expected Performance:\n");
    printf("  Cache Hit:  1-5ns   (10x faster than table lookup)\n");
    printf("  Cache Miss: 10-50ns (fallback to table lookup)\n");
    printf("  Target Hit Rate: 80-95%%\n");

    printf("================================================================================\n");
}
