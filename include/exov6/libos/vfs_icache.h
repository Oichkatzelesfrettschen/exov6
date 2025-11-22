/**
 * @file vfs_icache.h
 * @brief VFS Inode Cache
 *
 * High-performance inode cache with:
 * - Hash-based lookup
 * - LRU eviction
 * - PDAC capability integration
 * - Lock-free reads for common case
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <stdatomic.h>
#include "vfs.h"

#ifdef __cplusplus
extern "C" {
#endif

/*******************************************************************************
 * CONFIGURATION
 ******************************************************************************/

#define ICACHE_SIZE          1024      /**< Number of hash buckets */
#define ICACHE_MAX_ENTRIES   4096      /**< Maximum cached inodes */
#define ICACHE_LRU_SIZE      256       /**< LRU list size */

/*******************************************************************************
 * INODE CACHE ENTRY
 ******************************************************************************/

/**
 * @brief Inode cache entry
 */
typedef struct icache_entry {
    struct vfs_inode *inode;           /**< Cached inode */
    uint64_t key;                      /**< Hash key (dev:inum) */
    _Atomic uint32_t refcount;         /**< Reference count */
    _Atomic uint64_t last_access;      /**< Last access timestamp */

    /* Hash chain */
    struct icache_entry *next;

    /* LRU chain */
    struct icache_entry *lru_prev;
    struct icache_entry *lru_next;
} icache_entry_t;

/*******************************************************************************
 * INODE CACHE
 ******************************************************************************/

/**
 * @brief VFS inode cache
 */
typedef struct {
    /* Hash table */
    icache_entry_t *buckets[ICACHE_SIZE];

    /* LRU list */
    icache_entry_t *lru_head;
    icache_entry_t *lru_tail;
    _Atomic uint32_t lru_count;

    /* Statistics */
    _Atomic uint64_t hits;
    _Atomic uint64_t misses;
    _Atomic uint64_t evictions;
    _Atomic uint64_t total_entries;

    /* Configuration */
    _Atomic bool enabled;
} vfs_icache_t;

/*******************************************************************************
 * INITIALIZATION
 ******************************************************************************/

/**
 * @brief Initialize inode cache
 *
 * @param cache  Inode cache
 * @return 0 on success, negative on error
 */
int vfs_icache_init(vfs_icache_t *cache);

/**
 * @brief Destroy inode cache
 *
 * @param cache  Inode cache
 */
void vfs_icache_destroy(vfs_icache_t *cache);

/**
 * @brief Enable/disable inode cache
 *
 * @param cache   Inode cache
 * @param enable  true to enable, false to disable
 */
void vfs_icache_set_enabled(vfs_icache_t *cache, bool enable);

/*******************************************************************************
 * CACHE OPERATIONS
 ******************************************************************************/

/**
 * @brief Compute cache key
 *
 * @param dev   Device number
 * @param inum  Inode number
 * @return Hash key
 */
static inline uint64_t vfs_icache_key(uint32_t dev, uint64_t inum)
{
    return ((uint64_t)dev << 32) | (inum & 0xFFFFFFFF);
}

/**
 * @brief Compute hash bucket
 *
 * @param key  Hash key
 * @return Bucket index
 */
static inline uint32_t vfs_icache_hash(uint64_t key)
{
    /* Simple hash function */
    uint32_t hash = (uint32_t)(key ^ (key >> 32));
    hash = hash ^ (hash >> 16);
    return hash % ICACHE_SIZE;
}

/**
 * @brief Look up inode in cache
 *
 * @param cache  Inode cache
 * @param dev    Device number
 * @param inum   Inode number
 * @return Cached inode or NULL if not found
 */
struct vfs_inode* vfs_icache_lookup(vfs_icache_t *cache, uint32_t dev, uint64_t inum);

/**
 * @brief Insert inode into cache
 *
 * @param cache  Inode cache
 * @param dev    Device number
 * @param inode  Inode to insert
 * @return 0 on success, negative on error
 */
int vfs_icache_insert(vfs_icache_t *cache, uint32_t dev, struct vfs_inode *inode);

/**
 * @brief Remove inode from cache
 *
 * @param cache  Inode cache
 * @param dev    Device number
 * @param inum   Inode number
 * @return 0 on success, negative if not found
 */
int vfs_icache_remove(vfs_icache_t *cache, uint32_t dev, uint64_t inum);

/**
 * @brief Evict least recently used inode
 *
 * @param cache  Inode cache
 * @return 0 on success, negative on error
 */
int vfs_icache_evict_lru(vfs_icache_t *cache);

/**
 * @brief Flush all dirty inodes
 *
 * @param cache  Inode cache
 * @return 0 on success, negative on error
 */
int vfs_icache_flush(vfs_icache_t *cache);

/**
 * @brief Clear cache
 *
 * Removes all entries from cache.
 *
 * @param cache  Inode cache
 */
void vfs_icache_clear(vfs_icache_t *cache);

/*******************************************************************************
 * STATISTICS
 ******************************************************************************/

/**
 * @brief Inode cache statistics
 */
typedef struct {
    bool enabled;
    uint32_t total_entries;
    uint32_t lru_count;
    uint64_t hits;
    uint64_t misses;
    uint64_t evictions;
    double hit_rate;
} icache_stats_t;

/**
 * @brief Get inode cache statistics
 *
 * @param cache  Inode cache
 * @param stats  Output statistics
 */
void vfs_icache_get_stats(const vfs_icache_t *cache, icache_stats_t *stats);

/**
 * @brief Print inode cache statistics
 *
 * @param cache  Inode cache
 */
void vfs_icache_print_stats(const vfs_icache_t *cache);

/**
 * @brief Get global inode cache
 *
 * @return Global inode cache instance
 */
vfs_icache_t* vfs_get_icache(void);

#ifdef __cplusplus
}
#endif
