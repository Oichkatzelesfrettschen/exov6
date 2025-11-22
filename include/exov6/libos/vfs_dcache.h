/**
 * @file vfs_dcache.h
 * @brief VFS Dentry (Directory Entry) Cache
 *
 * High-performance directory entry cache with:
 * - Hash-based path lookup
 * - LRU eviction
 * - Negative caching (non-existent entries)
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

#define DCACHE_SIZE          2048      /**< Number of hash buckets */
#define DCACHE_MAX_ENTRIES   8192      /**< Maximum cached entries */
#define DCACHE_MAX_PATH      256       /**< Maximum path component length */

/*******************************************************************************
 * DENTRY CACHE ENTRY
 ******************************************************************************/

/**
 * @brief Dentry cache entry
 */
typedef struct dcache_entry {
    char name[DCACHE_MAX_PATH];        /**< Entry name */
    uint32_t name_len;                 /**< Name length */
    uint64_t parent_inum;              /**< Parent inode number */
    uint64_t inum;                     /**< Inode number (0 = negative entry) */
    uint32_t hash;                     /**< Name hash */

    _Atomic uint32_t refcount;         /**< Reference count */
    _Atomic uint64_t last_access;      /**< Last access timestamp */

    /* Flags */
    bool negative;                     /**< true = entry doesn't exist */

    /* Hash chain */
    struct dcache_entry *next;

    /* LRU chain */
    struct dcache_entry *lru_prev;
    struct dcache_entry *lru_next;
} dcache_entry_t;

/*******************************************************************************
 * DENTRY CACHE
 ******************************************************************************/

/**
 * @brief VFS dentry cache
 */
typedef struct {
    /* Hash table */
    dcache_entry_t *buckets[DCACHE_SIZE];

    /* LRU list */
    dcache_entry_t *lru_head;
    dcache_entry_t *lru_tail;
    _Atomic uint32_t lru_count;

    /* Statistics */
    _Atomic uint64_t hits;             /**< Cache hits */
    _Atomic uint64_t misses;           /**< Cache misses */
    _Atomic uint64_t negative_hits;    /**< Negative entry hits */
    _Atomic uint64_t evictions;        /**< Evictions */
    _Atomic uint64_t total_entries;    /**< Total entries */

    /* Configuration */
    _Atomic bool enabled;
    _Atomic bool negative_caching;     /**< Enable negative caching */
} vfs_dcache_t;

/*******************************************************************************
 * INITIALIZATION
 ******************************************************************************/

/**
 * @brief Initialize dentry cache
 *
 * @param cache  Dentry cache
 * @return 0 on success, negative on error
 */
int vfs_dcache_init(vfs_dcache_t *cache);

/**
 * @brief Destroy dentry cache
 *
 * @param cache  Dentry cache
 */
void vfs_dcache_destroy(vfs_dcache_t *cache);

/**
 * @brief Enable/disable dentry cache
 *
 * @param cache   Dentry cache
 * @param enable  true to enable, false to disable
 */
void vfs_dcache_set_enabled(vfs_dcache_t *cache, bool enable);

/**
 * @brief Enable/disable negative caching
 *
 * @param cache   Dentry cache
 * @param enable  true to enable, false to disable
 */
void vfs_dcache_set_negative_caching(vfs_dcache_t *cache, bool enable);

/*******************************************************************************
 * HASH FUNCTIONS
 ******************************************************************************/

/**
 * @brief Compute name hash
 *
 * Uses FNV-1a hash algorithm.
 *
 * @param name  Name to hash
 * @param len   Name length
 * @return Hash value
 */
static inline uint32_t vfs_dcache_hash_name(const char *name, uint32_t len)
{
    uint32_t hash = 2166136261u;  /* FNV offset basis */

    for (uint32_t i = 0; i < len; i++) {
        hash ^= (uint8_t)name[i];
        hash *= 16777619u;  /* FNV prime */
    }

    return hash;
}

/**
 * @brief Compute cache key
 *
 * @param parent_inum  Parent inode number
 * @param name_hash    Name hash
 * @return Cache key
 */
static inline uint64_t vfs_dcache_key(uint64_t parent_inum, uint32_t name_hash)
{
    return (parent_inum << 32) | name_hash;
}

/**
 * @brief Compute hash bucket
 *
 * @param key  Cache key
 * @return Bucket index
 */
static inline uint32_t vfs_dcache_bucket(uint64_t key)
{
    uint32_t hash = (uint32_t)(key ^ (key >> 32));
    hash = hash ^ (hash >> 16);
    return hash % DCACHE_SIZE;
}

/*******************************************************************************
 * CACHE OPERATIONS
 ******************************************************************************/

/**
 * @brief Look up directory entry in cache
 *
 * @param cache        Dentry cache
 * @param parent_inum  Parent inode number
 * @param name         Entry name
 * @param len          Name length
 * @param inum_out     Output inode number
 * @return 1 if found (positive), 0 if negative cached, -1 if not in cache
 */
int vfs_dcache_lookup(vfs_dcache_t *cache, uint64_t parent_inum,
                      const char *name, uint32_t len, uint64_t *inum_out);

/**
 * @brief Insert directory entry into cache
 *
 * @param cache        Dentry cache
 * @param parent_inum  Parent inode number
 * @param name         Entry name
 * @param len          Name length
 * @param inum         Inode number (0 for negative entry)
 * @return 0 on success, negative on error
 */
int vfs_dcache_insert(vfs_dcache_t *cache, uint64_t parent_inum,
                      const char *name, uint32_t len, uint64_t inum);

/**
 * @brief Remove directory entry from cache
 *
 * @param cache        Dentry cache
 * @param parent_inum  Parent inode number
 * @param name         Entry name
 * @param len          Name length
 * @return 0 on success, negative if not found
 */
int vfs_dcache_remove(vfs_dcache_t *cache, uint64_t parent_inum,
                      const char *name, uint32_t len);

/**
 * @brief Invalidate all entries for a directory
 *
 * @param cache        Dentry cache
 * @param parent_inum  Parent inode number
 * @return Number of entries invalidated
 */
int vfs_dcache_invalidate_dir(vfs_dcache_t *cache, uint64_t parent_inum);

/**
 * @brief Evict least recently used entry
 *
 * @param cache  Dentry cache
 * @return 0 on success, negative on error
 */
int vfs_dcache_evict_lru(vfs_dcache_t *cache);

/**
 * @brief Clear cache
 *
 * Removes all entries from cache.
 *
 * @param cache  Dentry cache
 */
void vfs_dcache_clear(vfs_dcache_t *cache);

/*******************************************************************************
 * STATISTICS
 ******************************************************************************/

/**
 * @brief Dentry cache statistics
 */
typedef struct {
    bool enabled;
    bool negative_caching;
    uint32_t total_entries;
    uint32_t lru_count;
    uint64_t hits;
    uint64_t misses;
    uint64_t negative_hits;
    uint64_t evictions;
    double hit_rate;
    double negative_hit_rate;
} dcache_stats_t;

/**
 * @brief Get dentry cache statistics
 *
 * @param cache  Dentry cache
 * @param stats  Output statistics
 */
void vfs_dcache_get_stats(const vfs_dcache_t *cache, dcache_stats_t *stats);

/**
 * @brief Print dentry cache statistics
 *
 * @param cache  Dentry cache
 */
void vfs_dcache_print_stats(const vfs_dcache_t *cache);

/**
 * @brief Get global dentry cache
 *
 * @return Global dentry cache instance
 */
vfs_dcache_t* vfs_get_dcache(void);

#ifdef __cplusplus
}
#endif
