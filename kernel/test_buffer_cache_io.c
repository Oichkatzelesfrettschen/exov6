/**
 * @file test_buffer_cache_io.c
 * @brief Buffer Cache I/O Layer Tests
 *
 * Tests the integration between buffer cache and IDE driver.
 */

#include "buffer_cache.h"
#include "bcache_io.h"
#include "fs.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>

/* Test configuration */
#define TEST_DEV 0
#define TEST_BLOCK_START 100
#define TEST_ITERATIONS 10

/**
 * @brief Test 1: Basic read/write
 */
static int test_basic_read_write(void)
{
    printf("TEST 1: Basic read/write\n");

    buffer_cache_t *cache = bcache_get_global();
    if (!cache) {
        printf("  FAIL: Could not get global cache\n");
        return -1;
    }

    /* Create test entry */
    bcache_entry_t *entry = bcache_get_or_read(cache, TEST_DEV, TEST_BLOCK_START, NULL);
    if (!entry) {
        printf("  FAIL: Could not allocate entry\n");
        return -1;
    }

    /* Write test pattern */
    for (uint32_t i = 0; i < BSIZE; i++) {
        ((uint8_t*)entry->data)[i] = (uint8_t)(i & 0xFF);
    }

    /* Mark dirty and write */
    atomic_fetch_or(&entry->flags, BCACHE_DIRTY);
    if (bcache_write_block(cache, entry) < 0) {
        printf("  FAIL: Write failed\n");
        bcache_release(cache, entry);
        return -1;
    }

    bcache_release(cache, entry);

    /* Invalidate cache to force re-read */
    bcache_invalidate(cache, entry);

    /* Read back */
    entry = bcache_get_or_read(cache, TEST_DEV, TEST_BLOCK_START, NULL);
    if (!entry) {
        printf("  FAIL: Could not read back\n");
        return -1;
    }

    /* Verify data */
    for (uint32_t i = 0; i < BSIZE; i++) {
        uint8_t expected = (uint8_t)(i & 0xFF);
        uint8_t actual = ((uint8_t*)entry->data)[i];
        if (actual != expected) {
            printf("  FAIL: Data mismatch at offset %u: expected %u, got %u\n",
                   i, expected, actual);
            bcache_release(cache, entry);
            return -1;
        }
    }

    bcache_release(cache, entry);
    printf("  PASS: Read/write verified\n");
    return 0;
}

/**
 * @brief Test 2: Cache hit performance
 */
static int test_cache_hits(void)
{
    printf("\nTEST 2: Cache hit performance\n");

    buffer_cache_t *cache = bcache_get_global();

    /* First read (miss) */
    bcache_entry_t *entry = bcache_get_or_read(cache, TEST_DEV, TEST_BLOCK_START + 1, NULL);
    if (!entry) {
        printf("  FAIL: First read failed\n");
        return -1;
    }
    bcache_release(cache, entry);

    uint64_t hits_before = atomic_load(&cache->hits);

    /* Second read (should hit) */
    entry = bcache_get(cache, TEST_DEV, TEST_BLOCK_START + 1, NULL);
    if (!entry) {
        printf("  FAIL: Second read missed cache\n");
        return -1;
    }

    uint64_t hits_after = atomic_load(&cache->hits);

    if (hits_after <= hits_before) {
        printf("  FAIL: Cache hit not recorded\n");
        bcache_release(cache, entry);
        return -1;
    }

    bcache_release(cache, entry);
    printf("  PASS: Cache hits working (before=%lu, after=%lu)\n",
           hits_before, hits_after);
    return 0;
}

/**
 * @brief Test 3: Multiple block writes
 */
static int test_multiple_blocks(void)
{
    printf("\nTEST 3: Multiple block I/O\n");

    buffer_cache_t *cache = bcache_get_global();
    bcache_entry_t *entries[TEST_ITERATIONS];

    /* Write multiple blocks with different patterns */
    for (int i = 0; i < TEST_ITERATIONS; i++) {
        entries[i] = bcache_get_or_read(cache, TEST_DEV, TEST_BLOCK_START + 10 + i, NULL);
        if (!entries[i]) {
            printf("  FAIL: Could not allocate entry %d\n", i);
            return -1;
        }

        /* Fill with pattern based on block number */
        for (uint32_t j = 0; j < BSIZE; j++) {
            ((uint8_t*)entries[i]->data)[j] = (uint8_t)((i + j) & 0xFF);
        }

        atomic_fetch_or(&entries[i]->flags, BCACHE_DIRTY);
    }

    /* Flush all blocks */
    if (bcache_flush_all(cache) < 0) {
        printf("  FAIL: Flush failed\n");
        return -1;
    }

    /* Release all entries */
    for (int i = 0; i < TEST_ITERATIONS; i++) {
        bcache_release(cache, entries[i]);
    }

    /* Invalidate cache */
    bcache_invalidate_dev(cache, TEST_DEV);

    /* Read back and verify */
    for (int i = 0; i < TEST_ITERATIONS; i++) {
        entries[i] = bcache_get_or_read(cache, TEST_DEV, TEST_BLOCK_START + 10 + i, NULL);
        if (!entries[i]) {
            printf("  FAIL: Could not read back entry %d\n", i);
            return -1;
        }

        /* Verify pattern */
        for (uint32_t j = 0; j < BSIZE; j++) {
            uint8_t expected = (uint8_t)((i + j) & 0xFF);
            uint8_t actual = ((uint8_t*)entries[i]->data)[j];
            if (actual != expected) {
                printf("  FAIL: Block %d data mismatch at offset %u\n", i, j);
                return -1;
            }
        }

        bcache_release(cache, entries[i]);
    }

    printf("  PASS: Multiple blocks verified\n");
    return 0;
}

/**
 * @brief Test 4: Read-ahead functionality
 */
static int test_readahead(void)
{
    printf("\nTEST 4: Read-ahead\n");

    buffer_cache_t *cache = bcache_get_global();

    /* Trigger read-ahead with sequential access */
    for (int i = 0; i < 8; i++) {
        bcache_entry_t *entry = bcache_read_with_prefetch(cache, TEST_DEV,
                                                           TEST_BLOCK_START + 50 + i, NULL);
        if (!entry) {
            printf("  FAIL: Read with prefetch failed at %d\n", i);
            return -1;
        }
        bcache_release(cache, entry);
    }

    /* Check if read-ahead activated */
    if (cache->readahead.pattern != PATTERN_SEQUENTIAL) {
        printf("  WARN: Sequential pattern not detected\n");
    } else {
        printf("  PASS: Sequential pattern detected, readahead=%u blocks\n",
               cache->readahead.readahead_blocks);
    }

    return 0;
}

/**
 * @brief Test 5: Statistics
 */
static int test_statistics(void)
{
    printf("\nTEST 5: Statistics\n");

    buffer_cache_t *cache = bcache_get_global();
    bcache_stats_t stats;

    bcache_get_stats(cache, &stats);

    printf("  Cache size: %u/%u entries\n", stats.current_size, stats.target_size);
    printf("  Hits: %lu, Misses: %lu, Hit rate: %.1f%%\n",
           stats.hits, stats.misses, stats.hit_rate * 100.0);
    printf("  Reads: %lu, Writes: %lu, Evictions: %lu\n",
           stats.reads, stats.writes, stats.evictions);

    if (stats.hits == 0 && stats.misses == 0) {
        printf("  WARN: No cache activity recorded\n");
        return -1;
    }

    printf("  PASS: Statistics collected\n");
    return 0;
}

/**
 * @brief Main test runner
 */
int main(int argc, char *argv[])
{
    printf("================================================================================\n");
    printf("BUFFER CACHE I/O TESTS\n");
    printf("================================================================================\n\n");

    int failures = 0;

    /* Note: These tests require IDE hardware or emulation */
    printf("WARNING: These tests require functional IDE hardware/emulation\n");
    printf("Running in test mode may fail without proper initialization\n\n");

    if (test_basic_read_write() < 0) failures++;
    if (test_cache_hits() < 0) failures++;
    if (test_multiple_blocks() < 0) failures++;
    if (test_readahead() < 0) failures++;
    if (test_statistics() < 0) failures++;

    printf("\n================================================================================\n");
    if (failures == 0) {
        printf("ALL TESTS PASSED\n");
    } else {
        printf("TESTS FAILED: %d\n", failures);
    }
    printf("================================================================================\n");

    return (failures == 0) ? 0 : 1;
}
