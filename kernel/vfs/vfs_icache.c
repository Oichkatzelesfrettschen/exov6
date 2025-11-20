/**
 * @file vfs_icache.c
 * @brief VFS Inode Cache Implementation
 */

#include "vfs_icache.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>

/*******************************************************************************
 * GLOBAL STATE
 ******************************************************************************/

static vfs_icache_t g_icache;
static bool g_icache_initialized = false;

/*******************************************************************************
 * INITIALIZATION
 ******************************************************************************/

int vfs_icache_init(vfs_icache_t *cache)
{
    if (!cache) return -1;

    memset(cache, 0, sizeof(*cache));

    atomic_store(&cache->enabled, true);
    atomic_store(&cache->lru_count, 0);

    printf("VFS: Inode cache initialized (%u buckets, max %u entries)\n",
           ICACHE_SIZE, ICACHE_MAX_ENTRIES);

    return 0;
}

void vfs_icache_destroy(vfs_icache_t *cache)
{
    if (!cache) return;

    atomic_store(&cache->enabled, false);
    vfs_icache_clear(cache);
}

void vfs_icache_set_enabled(vfs_icache_t *cache, bool enable)
{
    if (!cache) return;
    atomic_store(&cache->enabled, enable);
}

vfs_icache_t* vfs_get_icache(void)
{
    if (!g_icache_initialized) {
        vfs_icache_init(&g_icache);
        g_icache_initialized = true;
    }
    return &g_icache;
}

/*******************************************************************************
 * LRU MANAGEMENT
 ******************************************************************************/

/**
 * @brief Move entry to head of LRU list (most recently used)
 *
 * @param cache  Inode cache
 * @param entry  Entry to move
 */
static void icache_lru_touch(vfs_icache_t *cache, icache_entry_t *entry)
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
 * @param cache  Inode cache
 * @param entry  Entry to remove
 */
static void icache_lru_remove(vfs_icache_t *cache, icache_entry_t *entry)
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

    uint32_t old = atomic_fetch_sub(&cache->lru_count, 1);
    (void)old;  /* Unused */
}

/*******************************************************************************
 * CACHE OPERATIONS
 ******************************************************************************/

struct vfs_inode* vfs_icache_lookup(vfs_icache_t *cache, uint32_t dev, uint64_t inum)
{
    if (!cache || !atomic_load(&cache->enabled)) {
        atomic_fetch_add(&cache->misses, 1);
        return NULL;
    }

    uint64_t key = vfs_icache_key(dev, inum);
    uint32_t bucket = vfs_icache_hash(key);

    /* Search hash chain */
    icache_entry_t *entry = cache->buckets[bucket];
    while (entry) {
        if (entry->key == key) {
            /* Found - update LRU and return */
            icache_lru_touch(cache, entry);
            vfs_inode_get(entry->inode);
            atomic_fetch_add(&cache->hits, 1);
            return entry->inode;
        }
        entry = entry->next;
    }

    /* Not found */
    atomic_fetch_add(&cache->misses, 1);
    return NULL;
}

int vfs_icache_insert(vfs_icache_t *cache, uint32_t dev, struct vfs_inode *inode)
{
    if (!cache || !inode) return -1;
    if (!atomic_load(&cache->enabled)) return -1;

    uint64_t key = vfs_icache_key(dev, inode->inum);
    uint32_t bucket = vfs_icache_hash(key);

    /* Check if already cached */
    icache_entry_t *entry = cache->buckets[bucket];
    while (entry) {
        if (entry->key == key) {
            /* Already cached - just update LRU */
            icache_lru_touch(cache, entry);
            return 0;
        }
        entry = entry->next;
    }

    /* Check if cache is full */
    uint64_t total = atomic_load(&cache->total_entries);
    if (total >= ICACHE_MAX_ENTRIES) {
        /* Evict LRU entry */
        vfs_icache_evict_lru(cache);
    }

    /* Allocate new entry */
    entry = malloc(sizeof(icache_entry_t));
    if (!entry) {
        return -1;
    }

    memset(entry, 0, sizeof(*entry));

    /* Initialize entry */
    entry->inode = inode;
    entry->key = key;
    atomic_store(&entry->refcount, 1);
    atomic_store(&entry->last_access, (uint64_t)time(NULL));

    /* Add reference to inode */
    vfs_inode_get(inode);

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

int vfs_icache_remove(vfs_icache_t *cache, uint32_t dev, uint64_t inum)
{
    if (!cache) return -1;

    uint64_t key = vfs_icache_key(dev, inum);
    uint32_t bucket = vfs_icache_hash(key);

    /* Search hash chain */
    icache_entry_t **prev = &cache->buckets[bucket];
    icache_entry_t *entry = cache->buckets[bucket];

    while (entry) {
        if (entry->key == key) {
            /* Found - remove from hash chain */
            *prev = entry->next;

            /* Remove from LRU list */
            icache_lru_remove(cache, entry);

            /* Release inode reference */
            vfs_inode_put(entry->inode);

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

int vfs_icache_evict_lru(vfs_icache_t *cache)
{
    if (!cache || !cache->lru_tail) {
        return -1;
    }

    icache_entry_t *victim = cache->lru_tail;

    /* Check if inode is in use (refcount > 1 means external refs) */
    if (atomic_load(&victim->inode->refcount) > 1) {
        /* Can't evict - in use */
        return -1;
    }

    /* Write back if dirty */
    if (atomic_load(&victim->inode->state) & VFS_INODE_DIRTY) {
        if (victim->inode->sb && victim->inode->sb->s_op &&
            victim->inode->sb->s_op->write_inode) {
            victim->inode->sb->s_op->write_inode(victim->inode);
        }
    }

    /* Remove from cache */
    uint32_t bucket = vfs_icache_hash(victim->key);
    icache_entry_t **prev = &cache->buckets[bucket];
    icache_entry_t *entry = cache->buckets[bucket];

    while (entry) {
        if (entry == victim) {
            *prev = entry->next;
            break;
        }
        prev = &entry->next;
        entry = entry->next;
    }

    /* Remove from LRU list */
    icache_lru_remove(cache, victim);

    /* Release inode reference */
    vfs_inode_put(victim->inode);

    /* Free entry */
    free(victim);

    atomic_fetch_sub(&cache->total_entries, 1);
    atomic_fetch_add(&cache->evictions, 1);

    return 0;
}

int vfs_icache_flush(vfs_icache_t *cache)
{
    if (!cache) return -1;

    int errors = 0;

    /* Walk all buckets */
    for (uint32_t i = 0; i < ICACHE_SIZE; i++) {
        icache_entry_t *entry = cache->buckets[i];

        while (entry) {
            /* Check if dirty */
            if (atomic_load(&entry->inode->state) & VFS_INODE_DIRTY) {
                /* Write back */
                if (entry->inode->sb && entry->inode->sb->s_op &&
                    entry->inode->sb->s_op->write_inode) {

                    if (entry->inode->sb->s_op->write_inode(entry->inode) < 0) {
                        errors++;
                    } else {
                        /* Clear dirty flag */
                        atomic_fetch_and(&entry->inode->state, ~VFS_INODE_DIRTY);
                    }
                }
            }

            entry = entry->next;
        }
    }

    return (errors == 0) ? 0 : -1;
}

void vfs_icache_clear(vfs_icache_t *cache)
{
    if (!cache) return;

    /* Flush before clearing */
    vfs_icache_flush(cache);

    /* Walk all buckets and free entries */
    for (uint32_t i = 0; i < ICACHE_SIZE; i++) {
        icache_entry_t *entry = cache->buckets[i];

        while (entry) {
            icache_entry_t *next = entry->next;

            /* Release inode reference */
            vfs_inode_put(entry->inode);

            /* Free entry */
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

void vfs_icache_get_stats(const vfs_icache_t *cache, icache_stats_t *stats)
{
    if (!cache || !stats) return;

    memset(stats, 0, sizeof(*stats));

    stats->enabled = atomic_load(&cache->enabled);
    stats->total_entries = atomic_load(&cache->total_entries);
    stats->lru_count = atomic_load(&cache->lru_count);
    stats->hits = atomic_load(&cache->hits);
    stats->misses = atomic_load(&cache->misses);
    stats->evictions = atomic_load(&cache->evictions);

    uint64_t total = stats->hits + stats->misses;
    stats->hit_rate = (total > 0) ? (double)stats->hits / total : 0.0;
}

void vfs_icache_print_stats(const vfs_icache_t *cache)
{
    if (!cache) return;

    printf("================================================================================\n");
    printf("VFS INODE CACHE STATISTICS\n");
    printf("================================================================================\n\n");

    icache_stats_t stats;
    vfs_icache_get_stats(cache, &stats);

    printf("Configuration:\n");
    printf("  Enabled:           %s\n", stats.enabled ? "Yes" : "No");
    printf("  Buckets:           %u\n", ICACHE_SIZE);
    printf("  Max Entries:       %u\n", ICACHE_MAX_ENTRIES);
    printf("\n");

    printf("Current State:\n");
    printf("  Cached Entries:    %u\n", stats.total_entries);
    printf("  LRU Count:         %u\n", stats.lru_count);
    printf("  Utilization:       %.1f%%\n",
           100.0 * stats.total_entries / ICACHE_MAX_ENTRIES);
    printf("\n");

    printf("Performance:\n");
    printf("  Cache Hits:        %lu\n", stats.hits);
    printf("  Cache Misses:      %lu\n", stats.misses);
    printf("  Hit Rate:          %.1f%%\n", stats.hit_rate * 100.0);
    printf("  Evictions:         %lu\n", stats.evictions);
    printf("\n");

    printf("Expected Performance:\n");
    printf("  Hit Rate:          >90%% for typical workloads\n");
    printf("  Lookup Time:       O(1) average\n");
    printf("  Memory Overhead:   ~%zu bytes per entry\n", sizeof(icache_entry_t));

    printf("================================================================================\n");
}
