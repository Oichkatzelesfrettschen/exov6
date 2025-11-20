/**
 * @file vfs_dcache.c
 * @brief VFS Dentry Cache Implementation
 */

#include "vfs_dcache.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>

/*******************************************************************************
 * GLOBAL STATE
 ******************************************************************************/

static vfs_dcache_t g_dcache;
static bool g_dcache_initialized = false;

/*******************************************************************************
 * INITIALIZATION
 ******************************************************************************/

int vfs_dcache_init(vfs_dcache_t *cache)
{
    if (!cache) return -1;

    memset(cache, 0, sizeof(*cache));

    atomic_store(&cache->enabled, true);
    atomic_store(&cache->negative_caching, true);
    atomic_store(&cache->lru_count, 0);

    printf("VFS: Dentry cache initialized (%u buckets, max %u entries)\n",
           DCACHE_SIZE, DCACHE_MAX_ENTRIES);

    return 0;
}

void vfs_dcache_destroy(vfs_dcache_t *cache)
{
    if (!cache) return;

    atomic_store(&cache->enabled, false);
    vfs_dcache_clear(cache);
}

void vfs_dcache_set_enabled(vfs_dcache_t *cache, bool enable)
{
    if (!cache) return;
    atomic_store(&cache->enabled, enable);
}

void vfs_dcache_set_negative_caching(vfs_dcache_t *cache, bool enable)
{
    if (!cache) return;
    atomic_store(&cache->negative_caching, enable);
}

vfs_dcache_t* vfs_get_dcache(void)
{
    if (!g_dcache_initialized) {
        vfs_dcache_init(&g_dcache);
        g_dcache_initialized = true;
    }
    return &g_dcache;
}

/*******************************************************************************
 * LRU MANAGEMENT
 ******************************************************************************/

/**
 * @brief Move entry to head of LRU list (most recently used)
 *
 * @param cache  Dentry cache
 * @param entry  Entry to move
 */
static void dcache_lru_touch(vfs_dcache_t *cache, dcache_entry_t *entry)
{
    if (!cache || !entry) return;

    /* Update access timestamp */
    atomic_store(&entry->last_access, (uint64_t)time(NULL));

    /* If already at head, nothing to do */
    if (entry == cache->lru_head) {
        return;
    }

    /* Remove from current position */
    if (entry->lru_prev) {
        entry->lru_prev->lru_next = entry->lru_next;
    }
    if (entry->lru_next) {
        entry->lru_next->lru_prev = entry->lru_prev;
    }
    if (entry == cache->lru_tail) {
        cache->lru_tail = entry->lru_prev;
    }

    /* Insert at head */
    entry->lru_prev = NULL;
    entry->lru_next = cache->lru_head;

    if (cache->lru_head) {
        cache->lru_head->lru_prev = entry;
    }

    cache->lru_head = entry;

    if (!cache->lru_tail) {
        cache->lru_tail = entry;
    }
}

/**
 * @brief Remove entry from LRU list
 *
 * @param cache  Dentry cache
 * @param entry  Entry to remove
 */
static void dcache_lru_remove(vfs_dcache_t *cache, dcache_entry_t *entry)
{
    if (!cache || !entry) return;

    if (entry->lru_prev) {
        entry->lru_prev->lru_next = entry->lru_next;
    }
    if (entry->lru_next) {
        entry->lru_next->lru_prev = entry->lru_prev;
    }

    if (entry == cache->lru_head) {
        cache->lru_head = entry->lru_next;
    }
    if (entry == cache->lru_tail) {
        cache->lru_tail = entry->lru_prev;
    }

    entry->lru_prev = NULL;
    entry->lru_next = NULL;

    atomic_fetch_sub(&cache->lru_count, 1);
}

/*******************************************************************************
 * CACHE OPERATIONS
 ******************************************************************************/

int vfs_dcache_lookup(vfs_dcache_t *cache, uint64_t parent_inum,
                      const char *name, uint32_t len, uint64_t *inum_out)
{
    if (!cache || !name || len == 0 || !inum_out) {
        atomic_fetch_add(&cache->misses, 1);
        return -1;
    }

    if (!atomic_load(&cache->enabled)) {
        atomic_fetch_add(&cache->misses, 1);
        return -1;
    }

    /* Compute hash and bucket */
    uint32_t name_hash = vfs_dcache_hash_name(name, len);
    uint64_t key = vfs_dcache_key(parent_inum, name_hash);
    uint32_t bucket = vfs_dcache_bucket(key);

    /* Search hash chain */
    dcache_entry_t *entry = cache->buckets[bucket];
    while (entry) {
        if (entry->parent_inum == parent_inum &&
            entry->hash == name_hash &&
            entry->name_len == len &&
            memcmp(entry->name, name, len) == 0) {

            /* Found - update LRU */
            dcache_lru_touch(cache, entry);

            if (entry->negative) {
                /* Negative entry */
                atomic_fetch_add(&cache->negative_hits, 1);
                atomic_fetch_add(&cache->hits, 1);
                return 0;
            } else {
                /* Positive entry */
                *inum_out = entry->inum;
                atomic_fetch_add(&cache->hits, 1);
                return 1;
            }
        }
        entry = entry->next;
    }

    /* Not found */
    atomic_fetch_add(&cache->misses, 1);
    return -1;
}

int vfs_dcache_insert(vfs_dcache_t *cache, uint64_t parent_inum,
                      const char *name, uint32_t len, uint64_t inum)
{
    if (!cache || !name || len == 0 || len >= DCACHE_MAX_PATH) {
        return -1;
    }

    if (!atomic_load(&cache->enabled)) {
        return -1;
    }

    /* Check negative caching */
    if (inum == 0 && !atomic_load(&cache->negative_caching)) {
        return -1;
    }

    /* Compute hash and bucket */
    uint32_t name_hash = vfs_dcache_hash_name(name, len);
    uint64_t key = vfs_dcache_key(parent_inum, name_hash);
    uint32_t bucket = vfs_dcache_bucket(key);

    /* Check if already cached */
    dcache_entry_t *entry = cache->buckets[bucket];
    while (entry) {
        if (entry->parent_inum == parent_inum &&
            entry->hash == name_hash &&
            entry->name_len == len &&
            memcmp(entry->name, name, len) == 0) {

            /* Already cached - update */
            entry->inum = inum;
            entry->negative = (inum == 0);
            dcache_lru_touch(cache, entry);
            return 0;
        }
        entry = entry->next;
    }

    /* Check if cache is full */
    uint64_t total = atomic_load(&cache->total_entries);
    if (total >= DCACHE_MAX_ENTRIES) {
        /* Evict LRU entry */
        vfs_dcache_evict_lru(cache);
    }

    /* Allocate new entry */
    entry = malloc(sizeof(dcache_entry_t));
    if (!entry) {
        return -1;
    }

    memset(entry, 0, sizeof(*entry));

    /* Initialize entry */
    memcpy(entry->name, name, len);
    entry->name[len] = '\0';
    entry->name_len = len;
    entry->parent_inum = parent_inum;
    entry->inum = inum;
    entry->hash = name_hash;
    entry->negative = (inum == 0);
    atomic_store(&entry->refcount, 1);
    atomic_store(&entry->last_access, (uint64_t)time(NULL));

    /* Insert into hash chain */
    entry->next = cache->buckets[bucket];
    cache->buckets[bucket] = entry;

    /* Add to LRU list */
    entry->lru_prev = NULL;
    entry->lru_next = cache->lru_head;

    if (cache->lru_head) {
        cache->lru_head->lru_prev = entry;
    }

    cache->lru_head = entry;

    if (!cache->lru_tail) {
        cache->lru_tail = entry;
    }

    atomic_fetch_add(&cache->lru_count, 1);
    atomic_fetch_add(&cache->total_entries, 1);

    return 0;
}

int vfs_dcache_remove(vfs_dcache_t *cache, uint64_t parent_inum,
                      const char *name, uint32_t len)
{
    if (!cache || !name || len == 0) {
        return -1;
    }

    /* Compute hash and bucket */
    uint32_t name_hash = vfs_dcache_hash_name(name, len);
    uint64_t key = vfs_dcache_key(parent_inum, name_hash);
    uint32_t bucket = vfs_dcache_bucket(key);

    /* Search hash chain */
    dcache_entry_t **prev = &cache->buckets[bucket];
    dcache_entry_t *entry = cache->buckets[bucket];

    while (entry) {
        if (entry->parent_inum == parent_inum &&
            entry->hash == name_hash &&
            entry->name_len == len &&
            memcmp(entry->name, name, len) == 0) {

            /* Found - remove from hash chain */
            *prev = entry->next;

            /* Remove from LRU list */
            dcache_lru_remove(cache, entry);

            /* Free entry */
            free(entry);

            atomic_fetch_sub(&cache->total_entries, 1);
            return 0;
        }

        prev = &entry->next;
        entry = entry->next;
    }

    return -1;  /* Not found */
}

int vfs_dcache_invalidate_dir(vfs_dcache_t *cache, uint64_t parent_inum)
{
    if (!cache) return -1;

    int count = 0;

    /* Walk all buckets */
    for (uint32_t i = 0; i < DCACHE_SIZE; i++) {
        dcache_entry_t **prev = &cache->buckets[i];
        dcache_entry_t *entry = cache->buckets[i];

        while (entry) {
            dcache_entry_t *next = entry->next;

            if (entry->parent_inum == parent_inum) {
                /* Remove from hash chain */
                *prev = entry->next;

                /* Remove from LRU list */
                dcache_lru_remove(cache, entry);

                /* Free entry */
                free(entry);

                atomic_fetch_sub(&cache->total_entries, 1);
                count++;
            } else {
                prev = &entry->next;
            }

            entry = next;
        }
    }

    return count;
}

int vfs_dcache_evict_lru(vfs_dcache_t *cache)
{
    if (!cache || !cache->lru_tail) {
        return -1;
    }

    dcache_entry_t *victim = cache->lru_tail;

    /* Remove from cache */
    uint64_t key = vfs_dcache_key(victim->parent_inum, victim->hash);
    uint32_t bucket = vfs_dcache_bucket(key);

    dcache_entry_t **prev = &cache->buckets[bucket];
    dcache_entry_t *entry = cache->buckets[bucket];

    while (entry) {
        if (entry == victim) {
            *prev = entry->next;
            break;
        }
        prev = &entry->next;
        entry = entry->next;
    }

    /* Remove from LRU list */
    dcache_lru_remove(cache, victim);

    /* Free entry */
    free(victim);

    atomic_fetch_sub(&cache->total_entries, 1);
    atomic_fetch_add(&cache->evictions, 1);

    return 0;
}

void vfs_dcache_clear(vfs_dcache_t *cache)
{
    if (!cache) return;

    /* Walk all buckets and free entries */
    for (uint32_t i = 0; i < DCACHE_SIZE; i++) {
        dcache_entry_t *entry = cache->buckets[i];

        while (entry) {
            dcache_entry_t *next = entry->next;
            free(entry);
            entry = next;
        }

        cache->buckets[i] = NULL;
    }

    /* Clear LRU list */
    cache->lru_head = NULL;
    cache->lru_tail = NULL;
    atomic_store(&cache->lru_count, 0);
    atomic_store(&cache->total_entries, 0);
}

/*******************************************************************************
 * STATISTICS
 ******************************************************************************/

void vfs_dcache_get_stats(const vfs_dcache_t *cache, dcache_stats_t *stats)
{
    if (!cache || !stats) return;

    memset(stats, 0, sizeof(*stats));

    stats->enabled = atomic_load(&cache->enabled);
    stats->negative_caching = atomic_load(&cache->negative_caching);
    stats->total_entries = atomic_load(&cache->total_entries);
    stats->lru_count = atomic_load(&cache->lru_count);
    stats->hits = atomic_load(&cache->hits);
    stats->misses = atomic_load(&cache->misses);
    stats->negative_hits = atomic_load(&cache->negative_hits);
    stats->evictions = atomic_load(&cache->evictions);

    uint64_t total = stats->hits + stats->misses;
    stats->hit_rate = (total > 0) ? (double)stats->hits / total : 0.0;
    stats->negative_hit_rate = (stats->hits > 0) ?
        (double)stats->negative_hits / stats->hits : 0.0;
}

void vfs_dcache_print_stats(const vfs_dcache_t *cache)
{
    if (!cache) return;

    printf("================================================================================\n");
    printf("VFS DENTRY CACHE STATISTICS\n");
    printf("================================================================================\n\n");

    dcache_stats_t stats;
    vfs_dcache_get_stats(cache, &stats);

    printf("Configuration:\n");
    printf("  Enabled:           %s\n", stats.enabled ? "Yes" : "No");
    printf("  Negative Caching:  %s\n", stats.negative_caching ? "Yes" : "No");
    printf("  Buckets:           %u\n", DCACHE_SIZE);
    printf("  Max Entries:       %u\n", DCACHE_MAX_ENTRIES);
    printf("\n");

    printf("Current State:\n");
    printf("  Cached Entries:    %u\n", stats.total_entries);
    printf("  LRU Count:         %u\n", stats.lru_count);
    printf("  Utilization:       %.1f%%\n",
           100.0 * stats.total_entries / DCACHE_MAX_ENTRIES);
    printf("\n");

    printf("Performance:\n");
    printf("  Cache Hits:        %lu\n", stats.hits);
    printf("  Cache Misses:      %lu\n", stats.misses);
    printf("  Hit Rate:          %.1f%%\n", stats.hit_rate * 100.0);
    printf("  Negative Hits:     %lu (%.1f%% of hits)\n",
           stats.negative_hits, stats.negative_hit_rate * 100.0);
    printf("  Evictions:         %lu\n", stats.evictions);
    printf("\n");

    printf("Expected Performance:\n");
    printf("  Hit Rate:          >95%% for typical workloads\n");
    printf("  Lookup Time:       O(1) average\n");
    printf("  Memory Overhead:   ~%zu bytes per entry\n", sizeof(dcache_entry_t));

    printf("================================================================================\n");
}
