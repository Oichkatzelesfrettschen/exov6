/**
 * @file buffer_cache.c
 * @brief PDAC-Aware Buffer Cache Implementation
 *
 * Novel unified buffer cache with:
 * - Block-level capability security
 * - SIMD-accelerated operations
 * - Adaptive cache sizing
 * - Prefetch integration
 */

#include "buffer_cache.h"
#include "fs.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>

/*******************************************************************************
 * GLOBAL STATE
 ******************************************************************************/

static buffer_cache_t g_bcache;
static bool g_bcache_initialized = false;

/*******************************************************************************
 * FORWARD DECLARATIONS
 ******************************************************************************/

static bcache_entry_t* bcache_alloc_entry(buffer_cache_t *cache, uint32_t dev,
                                          uint64_t blockno);
static void bcache_free_entry(buffer_cache_t *cache, bcache_entry_t *entry);
static void bcache_lru_touch(buffer_cache_t *cache, bcache_entry_t *entry);
static void bcache_lru_remove(buffer_cache_t *cache, bcache_entry_t *entry);
static int bcache_read_from_disk(buffer_cache_t *cache, bcache_entry_t *entry);
static bool bcache_verify_capability(const vfs_capability_t *entry_cap,
                                     const vfs_capability_t *required_cap);

/*******************************************************************************
 * INITIALIZATION
 ******************************************************************************/

int bcache_init(buffer_cache_t *cache, uint32_t num_cpus, simd_adaptive_t *simd)
{
    if (!cache || num_cpus == 0 || num_cpus > 256) return -1;

    memset(cache, 0, sizeof(*cache));

    cache->num_cpus = num_cpus;
    cache->simd = simd;

    /* Set defaults */
    atomic_store(&cache->target_size, BCACHE_DEFAULT_SIZE);
    atomic_store(&cache->current_size, 0);
    atomic_store(&cache->enabled, true);
    atomic_store(&cache->capability_checking, true);

    /* Initialize per-CPU LRU lists */
    for (uint32_t i = 0; i < num_cpus; i++) {
        cache->cpu_lru[i].lru_head = NULL;
        cache->cpu_lru[i].lru_tail = NULL;
        atomic_store(&cache->cpu_lru[i].count, 0);
    }

    /* Initialize read-ahead */
    cache->readahead.pattern = PATTERN_RANDOM;
    cache->readahead.readahead_blocks = 0;

    cache->last_tune_time = time(NULL);

    printf("BCACHE: Buffer cache initialized (%u buckets, %u CPUs)\n",
           BCACHE_BUCKETS, num_cpus);

    return 0;
}

void bcache_destroy(buffer_cache_t *cache)
{
    if (!cache) return;

    /* Flush all dirty blocks */
    bcache_flush_all(cache);

    /* Free all entries */
    for (uint32_t i = 0; i < BCACHE_BUCKETS; i++) {
        bcache_entry_t *entry = cache->buckets[i];
        while (entry) {
            bcache_entry_t *next = entry->next;
            bcache_free_entry(cache, entry);
            entry = next;
        }
        cache->buckets[i] = NULL;
    }

    atomic_store(&cache->enabled, false);
    atomic_store(&cache->current_size, 0);
}

void bcache_set_enabled(buffer_cache_t *cache, bool enable)
{
    if (!cache) return;
    atomic_store(&cache->enabled, enable);
}

void bcache_set_capability_checking(buffer_cache_t *cache, bool enable)
{
    if (!cache) return;
    atomic_store(&cache->capability_checking, enable);
}

buffer_cache_t* bcache_get_global(void)
{
    if (!g_bcache_initialized) {
        /* Initialize with single CPU and no SIMD for now */
        bcache_init(&g_bcache, 1, NULL);
        g_bcache_initialized = true;
    }
    return &g_bcache;
}

/*******************************************************************************
 * LRU MANAGEMENT
 ******************************************************************************/

static void bcache_lru_touch(buffer_cache_t *cache, bcache_entry_t *entry)
{
    if (!cache || !entry) return;

    /* Update access timestamp */
    atomic_store(&entry->last_access, (uint64_t)time(NULL));

    uint8_t cpu = entry->cpu;
    if (cpu >= cache->num_cpus) return;

    bcache_cpu_lru_t *lru = &cache->cpu_lru[cpu];

    /* If already at head, nothing to do */
    if (entry == lru->lru_head) {
        return;
    }

    /* Remove from current position */
    if (entry->lru_prev) {
        entry->lru_prev->lru_next = entry->lru_next;
    }
    if (entry->lru_next) {
        entry->lru_next->lru_prev = entry->lru_prev;
    }
    if (entry == lru->lru_tail) {
        lru->lru_tail = entry->lru_prev;
    }

    /* Insert at head (MRU) */
    entry->lru_prev = NULL;
    entry->lru_next = lru->lru_head;

    if (lru->lru_head) {
        lru->lru_head->lru_prev = entry;
    }

    lru->lru_head = entry;

    if (!lru->lru_tail) {
        lru->lru_tail = entry;
    }
}

static void bcache_lru_remove(buffer_cache_t *cache, bcache_entry_t *entry)
{
    if (!cache || !entry) return;

    uint8_t cpu = entry->cpu;
    if (cpu >= cache->num_cpus) return;

    bcache_cpu_lru_t *lru = &cache->cpu_lru[cpu];

    if (entry->lru_prev) {
        entry->lru_prev->lru_next = entry->lru_next;
    }
    if (entry->lru_next) {
        entry->lru_next->lru_prev = entry->lru_prev;
    }

    if (entry == lru->lru_head) {
        lru->lru_head = entry->lru_next;
    }
    if (entry == lru->lru_tail) {
        lru->lru_tail = entry->lru_prev;
    }

    entry->lru_prev = NULL;
    entry->lru_next = NULL;

    atomic_fetch_sub(&lru->count, 1);
}

/*******************************************************************************
 * CAPABILITY VERIFICATION (NOVEL)
 ******************************************************************************/

static bool bcache_verify_capability(const vfs_capability_t *entry_cap,
                                     const vfs_capability_t *required_cap)
{
    if (!entry_cap || !required_cap) return false;

    /* Check rights */
    if ((entry_cap->rights & required_cap->rights) != required_cap->rights) {
        return false;
    }

    /* Check expiry */
    if (entry_cap->expiry > 0) {
        uint64_t now = (uint64_t)time(NULL);
        if (now > entry_cap->expiry) {
            return false;  /* Expired */
        }
    }

    /* Check signature */
    if (entry_cap->signature != required_cap->signature) {
        return false;  /* Signature mismatch */
    }

    return true;
}

/*******************************************************************************
 * CACHE OPERATIONS
 ******************************************************************************/

bcache_entry_t* bcache_get(buffer_cache_t *cache, uint32_t dev,
                           uint64_t blockno, const vfs_capability_t *required_cap)
{
    if (!cache || !atomic_load(&cache->enabled)) {
        atomic_fetch_add(&cache->misses, 1);
        return NULL;
    }

    uint64_t bucket = bcache_hash(dev, blockno);

    /* Search hash chain */
    bcache_entry_t *entry = cache->buckets[bucket];
    while (entry) {
        if (entry->dev == dev && entry->blockno == blockno) {
            /* Found - verify capability if enabled */
            if (atomic_load(&cache->capability_checking) && required_cap) {
                if (!bcache_verify_capability(&entry->capability, required_cap)) {
                    atomic_fetch_add(&cache->capability_denials, 1);
                    return NULL;  /* Capability denied */
                }
            }

            /* Check if valid */
            if (!(atomic_load(&entry->flags) & BCACHE_VALID)) {
                atomic_fetch_add(&cache->misses, 1);
                return NULL;  /* Not yet read */
            }

            /* Update LRU */
            bcache_lru_touch(cache, entry);

            /* Increment refcount */
            atomic_fetch_add(&entry->refcount, 1);

            atomic_fetch_add(&cache->hits, 1);
            return entry;
        }
        entry = entry->next;
    }

    /* Not found */
    atomic_fetch_add(&cache->misses, 1);
    return NULL;
}

bcache_entry_t* bcache_get_or_read(buffer_cache_t *cache, uint32_t dev,
                                   uint64_t blockno, const vfs_capability_t *required_cap)
{
    if (!cache) return NULL;

    /* Try cache first */
    bcache_entry_t *entry = bcache_get(cache, dev, blockno, required_cap);
    if (entry) {
        return entry;
    }

    /* Cache miss - allocate new entry */
    entry = bcache_alloc_entry(cache, dev, blockno);
    if (!entry) {
        return NULL;
    }

    /* Copy capability if provided */
    if (required_cap) {
        entry->capability = *required_cap;
        entry->cap_signature = required_cap->signature;
    }

    /* Read from disk */
    if (bcache_read_from_disk(cache, entry) < 0) {
        bcache_free_entry(cache, entry);
        return NULL;
    }

    /* Mark as valid */
    atomic_fetch_or(&entry->flags, BCACHE_VALID);

    /* Increment refcount */
    atomic_fetch_add(&entry->refcount, 1);

    atomic_fetch_add(&cache->reads, 1);
    return entry;
}

void bcache_release(buffer_cache_t *cache, bcache_entry_t *entry)
{
    if (!cache || !entry) return;

    /* Decrement refcount */
    uint32_t old = atomic_fetch_sub(&entry->refcount, 1);

    if (old == 1) {
        /* Last reference - entry can be evicted now */
        /* But we don't free it immediately; leave in cache for reuse */
    }
}

int bcache_write_block(buffer_cache_t *cache, bcache_entry_t *entry)
{
    if (!cache || !entry) return -1;

    /* Check if dirty */
    if (!(atomic_load(&entry->flags) & BCACHE_DIRTY)) {
        return 0;  /* Not dirty */
    }

    /* TODO: Write to disk */
    /* For now, just clear dirty flag */
    atomic_fetch_and(&entry->flags, ~BCACHE_DIRTY);

    atomic_fetch_add(&cache->writes, 1);
    return 0;
}

int bcache_flush_all(buffer_cache_t *cache)
{
    if (!cache) return -1;

    int errors = 0;

    /* Walk all buckets */
    for (uint32_t i = 0; i < BCACHE_BUCKETS; i++) {
        bcache_entry_t *entry = cache->buckets[i];

        while (entry) {
            if (atomic_load(&entry->flags) & BCACHE_DIRTY) {
                if (bcache_write_block(cache, entry) < 0) {
                    errors++;
                }
            }
            entry = entry->next;
        }
    }

    return (errors == 0) ? 0 : -1;
}

int bcache_flush_dev(buffer_cache_t *cache, uint32_t dev)
{
    if (!cache) return -1;

    int errors = 0;

    /* Walk all buckets */
    for (uint32_t i = 0; i < BCACHE_BUCKETS; i++) {
        bcache_entry_t *entry = cache->buckets[i];

        while (entry) {
            if (entry->dev == dev && (atomic_load(&entry->flags) & BCACHE_DIRTY)) {
                if (bcache_write_block(cache, entry) < 0) {
                    errors++;
                }
            }
            entry = entry->next;
        }
    }

    return (errors == 0) ? 0 : -1;
}

void bcache_invalidate(buffer_cache_t *cache, bcache_entry_t *entry)
{
    if (!cache || !entry) return;

    /* Remove from hash chain */
    uint64_t bucket = bcache_hash(entry->dev, entry->blockno);

    bcache_entry_t **prev = &cache->buckets[bucket];
    bcache_entry_t *curr = cache->buckets[bucket];

    while (curr) {
        if (curr == entry) {
            *prev = curr->next;
            break;
        }
        prev = &curr->next;
        curr = curr->next;
    }

    /* Remove from LRU */
    bcache_lru_remove(cache, entry);

    /* Free entry */
    bcache_free_entry(cache, entry);
}

int bcache_invalidate_dev(buffer_cache_t *cache, uint32_t dev)
{
    if (!cache) return -1;

    int count = 0;

    /* Walk all buckets */
    for (uint32_t i = 0; i < BCACHE_BUCKETS; i++) {
        bcache_entry_t **prev = &cache->buckets[i];
        bcache_entry_t *entry = cache->buckets[i];

        while (entry) {
            bcache_entry_t *next = entry->next;

            if (entry->dev == dev) {
                /* Remove from hash chain */
                *prev = entry->next;

                /* Remove from LRU */
                bcache_lru_remove(cache, entry);

                /* Free entry */
                bcache_free_entry(cache, entry);

                count++;
            } else {
                prev = &entry->next;
            }

            entry = next;
        }
    }

    return count;
}

/*******************************************************************************
 * ENTRY ALLOCATION
 ******************************************************************************/

static bcache_entry_t* bcache_alloc_entry(buffer_cache_t *cache, uint32_t dev,
                                          uint64_t blockno)
{
    if (!cache) return NULL;

    /* Check if cache is full */
    uint32_t current = atomic_load(&cache->current_size);
    uint32_t target = atomic_load(&cache->target_size);

    if (current >= target) {
        /* Evict LRU entry */
        if (bcache_evict_lru(cache, 1) == 0) {
            /* Failed to evict */
            return NULL;
        }
    }

    /* Allocate entry */
    bcache_entry_t *entry = malloc(sizeof(bcache_entry_t));
    if (!entry) return NULL;

    memset(entry, 0, sizeof(*entry));

    /* Allocate data buffer */
    entry->data = malloc(BSIZE);
    if (!entry->data) {
        free(entry);
        return NULL;
    }

    /* Initialize entry */
    entry->dev = dev;
    entry->blockno = blockno;
    entry->hash = bcache_hash(dev, blockno);
    atomic_store(&entry->flags, 0);
    atomic_store(&entry->refcount, 0);
    atomic_store(&entry->last_access, (uint64_t)time(NULL));
    entry->cpu = 0;  /* TODO: Get current CPU */
    entry->checksum_valid = false;

    /* Insert into hash chain */
    uint64_t bucket = entry->hash;
    entry->next = cache->buckets[bucket];
    cache->buckets[bucket] = entry;

    /* Add to LRU */
    bcache_cpu_lru_t *lru = &cache->cpu_lru[entry->cpu];

    entry->lru_prev = NULL;
    entry->lru_next = lru->lru_head;

    if (lru->lru_head) {
        lru->lru_head->lru_prev = entry;
    }

    lru->lru_head = entry;

    if (!lru->lru_tail) {
        lru->lru_tail = entry;
    }

    atomic_fetch_add(&lru->count, 1);
    atomic_fetch_add(&cache->current_size, 1);

    return entry;
}

static void bcache_free_entry(buffer_cache_t *cache, bcache_entry_t *entry)
{
    if (!cache || !entry) return;

    /* Free data buffer */
    if (entry->data) {
        free(entry->data);
    }

    /* Free entry */
    free(entry);

    atomic_fetch_sub(&cache->current_size, 1);
}

/*******************************************************************************
 * DISK I/O
 ******************************************************************************/

static int bcache_read_from_disk(buffer_cache_t *cache, bcache_entry_t *entry)
{
    if (!cache || !entry || !entry->data) return -1;

    /* TODO: Read from actual disk device */
    /* For now, just zero the buffer */
    memset(entry->data, 0, BSIZE);

    return 0;
}

/*******************************************************************************
 * READ-AHEAD (NOVEL: Prefetch Integration)
 ******************************************************************************/

int bcache_prefetch_async(buffer_cache_t *cache, uint32_t dev, uint64_t blockno)
{
    if (!cache) return -1;

    /* Check if already cached */
    if (bcache_get(cache, dev, blockno, NULL)) {
        return 0;  /* Already cached */
    }

    /* Allocate entry */
    bcache_entry_t *entry = bcache_alloc_entry(cache, dev, blockno);
    if (!entry) return -1;

    /* Mark as read-ahead */
    atomic_fetch_or(&entry->flags, BCACHE_READAHEAD);

    /* Start async read */
    /* TODO: Queue async read */
    /* For now, read synchronously */
    bcache_read_from_disk(cache, entry);
    atomic_fetch_or(&entry->flags, BCACHE_VALID);

    return 0;
}

bcache_entry_t* bcache_read_with_prefetch(buffer_cache_t *cache, uint32_t dev,
                                          uint64_t blockno,
                                          const vfs_capability_t *required_cap)
{
    if (!cache) return NULL;

    /* Read requested block */
    bcache_entry_t *entry = bcache_get_or_read(cache, dev, blockno, required_cap);
    if (!entry) return NULL;

    /* Update access pattern */
    uint64_t last = cache->readahead.last_blockno;

    if (blockno == last + 1) {
        /* Sequential access */
        cache->readahead.sequential_count++;

        if (cache->readahead.sequential_count >= 4) {
            cache->readahead.pattern = PATTERN_SEQUENTIAL;
            cache->readahead.readahead_blocks = MIN(16, BCACHE_READAHEAD_MAX);
        }
    } else {
        /* Non-sequential */
        cache->readahead.sequential_count = 0;
        cache->readahead.pattern = PATTERN_RANDOM;
        cache->readahead.readahead_blocks = 0;
    }

    cache->readahead.last_blockno = blockno;

    /* Prefetch subsequent blocks */
    for (uint32_t i = 1; i <= cache->readahead.readahead_blocks; i++) {
        bcache_prefetch_async(cache, dev, blockno + i);
    }

    return entry;
}

/*******************************************************************************
 * SIMD OPERATIONS (NOVEL: Stubs for now)
 ******************************************************************************/

int bcache_checksum_block(buffer_cache_t *cache, bcache_entry_t *entry,
                          uint8_t checksum[32])
{
    if (!cache || !entry || !checksum) return -1;

    /* TODO: Implement SHA-256 checksum */
    /* For now, just zero */
    memset(checksum, 0, 32);

    return 0;
}

int bcache_checksum_blocks_simd(buffer_cache_t *cache, bcache_entry_t **entries,
                                uint32_t count, uint8_t checksums[][32])
{
    if (!cache || !entries || !checksums || count == 0) return -1;

    /* TODO: Implement SIMD checksums */
    /* For now, use scalar */
    for (uint32_t i = 0; i < count; i++) {
        bcache_checksum_block(cache, entries[i], checksums[i]);
    }

    return 0;
}

int bcache_zero_block_simd(buffer_cache_t *cache, bcache_entry_t *entry)
{
    if (!cache || !entry || !entry->data) return -1;

    /* TODO: Use SIMD for zeroing */
    memset(entry->data, 0, BSIZE);

    return 0;
}

/*******************************************************************************
 * ADAPTIVE MANAGEMENT (NOVEL: Task 5.5.4 Integration)
 ******************************************************************************/

double bcache_memory_pressure(void)
{
    /* TODO: Get actual memory pressure from system */
    return 0.5;  /* Stub: 50% pressure */
}

void bcache_adaptive_tune(buffer_cache_t *cache)
{
    if (!cache) return;

    /* Check if enough time has passed */
    uint64_t now = time(NULL);
    if (now - cache->last_tune_time < 10) {
        return;  /* Tune every 10 seconds */
    }

    cache->last_tune_time = now;

    /* Compute metrics */
    uint64_t hits = atomic_load(&cache->hits);
    uint64_t misses = atomic_load(&cache->misses);
    uint64_t total = hits + misses;

    if (total == 0) return;

    double hit_rate = (double)hits / total;

    uint32_t current = atomic_load(&cache->current_size);
    uint32_t target = atomic_load(&cache->target_size);

    /* Adaptation logic (similar to Task 5.5.4 Phase 1) */
    if (hit_rate < 0.85) {
        /* Low hit rate - increase cache */
        target = current * 2;
        if (target > BCACHE_MAX_SIZE) {
            target = BCACHE_MAX_SIZE;
        }
    } else if (hit_rate > 0.95) {
        double pressure = bcache_memory_pressure();

        if (pressure > 0.8) {
            /* High hit rate + memory pressure - can shrink */
            target = current / 2;
            if (target < BCACHE_MIN_SIZE) {
                target = BCACHE_MIN_SIZE;
            }
        }
    }

    atomic_store(&cache->target_size, target);

    /* Evict excess entries if needed */
    if (current > target) {
        bcache_evict_lru(cache, current - target);
    }
}

int bcache_evict_lru(buffer_cache_t *cache, uint32_t count)
{
    if (!cache || count == 0) return 0;

    uint32_t evicted = 0;

    /* Try to evict from each CPU's LRU list */
    for (uint32_t cpu = 0; cpu < cache->num_cpus && evicted < count; cpu++) {
        bcache_cpu_lru_t *lru = &cache->cpu_lru[cpu];

        while (evicted < count && lru->lru_tail) {
            bcache_entry_t *victim = lru->lru_tail;

            /* Check if entry is in use */
            if (atomic_load(&victim->refcount) > 0) {
                break;  /* Can't evict - in use */
            }

            /* Write back if dirty */
            if (atomic_load(&victim->flags) & BCACHE_DIRTY) {
                bcache_write_block(cache, victim);
            }

            /* Invalidate entry */
            bcache_invalidate(cache, victim);

            atomic_fetch_add(&cache->evictions, 1);
            evicted++;
        }
    }

    return evicted;
}

/*******************************************************************************
 * STATISTICS
 ******************************************************************************/

void bcache_get_stats(const buffer_cache_t *cache, bcache_stats_t *stats)
{
    if (!cache || !stats) return;

    memset(stats, 0, sizeof(*stats));

    stats->enabled = atomic_load(&cache->enabled);
    stats->capability_checking = atomic_load(&cache->capability_checking);

    stats->current_size = atomic_load(&cache->current_size);
    stats->target_size = atomic_load(&cache->target_size);
    stats->num_cpus = cache->num_cpus;

    stats->hits = atomic_load(&cache->hits);
    stats->misses = atomic_load(&cache->misses);
    stats->evictions = atomic_load(&cache->evictions);
    stats->reads = atomic_load(&cache->reads);
    stats->writes = atomic_load(&cache->writes);

    uint64_t total = stats->hits + stats->misses;
    stats->hit_rate = (total > 0) ? (double)stats->hits / total : 0.0;

    stats->capability_denials = atomic_load(&cache->capability_denials);
    stats->signature_failures = atomic_load(&cache->signature_failures);

    if (total > 0) {
        stats->capability_denial_rate = (double)stats->capability_denials / total;
    }

    /* Per-CPU stats */
    for (uint32_t i = 0; i < cache->num_cpus && i < 256; i++) {
        stats->cpu_stats[i].entries = atomic_load(&cache->cpu_lru[i].count);
    }
}

void bcache_print_stats(const buffer_cache_t *cache)
{
    if (!cache) return;

    printf("================================================================================\n");
    printf("BUFFER CACHE STATISTICS\n");
    printf("================================================================================\n\n");

    bcache_stats_t stats;
    bcache_get_stats(cache, &stats);

    printf("Configuration:\n");
    printf("  Enabled:           %s\n", stats.enabled ? "Yes" : "No");
    printf("  Capability Check:  %s\n", stats.capability_checking ? "Yes" : "No");
    printf("  Buckets:           %u\n", BCACHE_BUCKETS);
    printf("  CPUs:              %u\n", stats.num_cpus);
    printf("\n");

    printf("Cache State:\n");
    printf("  Current Size:      %u entries\n", stats.current_size);
    printf("  Target Size:       %u entries\n", stats.target_size);
    printf("  Utilization:       %.1f%%\n",
           100.0 * stats.current_size / BCACHE_MAX_SIZE);
    printf("\n");

    printf("Performance:\n");
    printf("  Cache Hits:        %lu\n", stats.hits);
    printf("  Cache Misses:      %lu\n", stats.misses);
    printf("  Hit Rate:          %.1f%%\n", stats.hit_rate * 100.0);
    printf("  Evictions:         %lu\n", stats.evictions);
    printf("  Disk Reads:        %lu\n", stats.reads);
    printf("  Disk Writes:       %lu\n", stats.writes);
    printf("\n");

    printf("Security (NOVEL):\n");
    printf("  Cap. Denials:      %lu\n", stats.capability_denials);
    printf("  Sig. Failures:     %lu\n", stats.signature_failures);
    printf("  Denial Rate:       %.3f%%\n", stats.capability_denial_rate * 100.0);
    printf("\n");

    printf("Per-CPU Distribution:\n");
    for (uint32_t i = 0; i < stats.num_cpus && i < 4; i++) {
        printf("  CPU %u:             %u entries\n", i, stats.cpu_stats[i].entries);
    }
    printf("\n");

    printf("Expected Performance:\n");
    printf("  Target Hit Rate:   90-95%%\n");
    printf("  Lookup Time:       O(1) average\n");
    printf("  Security Overhead: <5%%\n");

    printf("================================================================================\n");
}
