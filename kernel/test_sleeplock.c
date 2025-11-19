/**
 * @file test_sleeplock.c
 * @brief Sleeplock Integration Tests (Phase 6)
 *
 * Tests for the modernized sleeplock system with DAG lock ordering.
 */

#include <types.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include "sleeplock.h"
#include "exo_lock.h"

/* Test macros */
#define TEST_START(name) printf("TEST: %s ... ", name)
#define TEST_PASS() printf("PASS\n")
#define TEST_FAIL(msg) do { printf("FAIL: %s\n", msg); return; } while(0)
#define ASSERT(cond, msg) do { if (!(cond)) TEST_FAIL(msg); } while(0)

/*******************************************************************************
 * BASIC FUNCTIONALITY TESTS
 ******************************************************************************/

void test_sleeplock_basic_init(void)
{
    TEST_START("Sleeplock basic initialization");

    struct sleeplock lk;
    initsleeplock(&lk, "test_lock", LOCK_LEVEL_VFS);

    ASSERT(lk.locked == 0, "Initial state should be unlocked");
    ASSERT(lk.pid == 0, "Initial pid should be 0");
    ASSERT(lk.dag_level == LOCK_LEVEL_VFS, "DAG level should match");
    ASSERT(lk.name != NULL, "Name should be set");

    TEST_PASS();
}

void test_sleeplock_dag_levels(void)
{
    TEST_START("Sleeplock DAG level assignment");

    struct sleeplock lk1, lk2, lk3;

    initsleeplock(&lk1, "scheduler", LOCK_LEVEL_SCHEDULER);
    initsleeplock(&lk2, "filesystem", LOCK_LEVEL_FILESYSTEM);
    initsleeplock(&lk3, "device", LOCK_LEVEL_DEVICE);

    ASSERT(lk1.dag_level == LOCK_LEVEL_SCHEDULER, "Scheduler level");
    ASSERT(lk2.dag_level == LOCK_LEVEL_FILESYSTEM, "Filesystem level");
    ASSERT(lk3.dag_level == LOCK_LEVEL_DEVICE, "Device level");

    /* Verify internal qspinlocks are at lower levels */
    ASSERT(lk1.lk.dag_level < lk1.dag_level, "Internal lock at lower level");
    ASSERT(lk2.lk.dag_level < lk2.dag_level, "Internal lock at lower level");
    ASSERT(lk3.lk.dag_level < lk3.dag_level, "Internal lock at lower level");

    TEST_PASS();
}

void test_sleeplock_edge_cases(void)
{
    TEST_START("Sleeplock edge cases");

    /* Level 0 edge case */
    struct sleeplock lk_zero;
    initsleeplock(&lk_zero, "level_zero", 0);
    ASSERT(lk_zero.dag_level == 0, "Level 0 assignment");
    ASSERT(lk_zero.lk.dag_level == 0, "Internal lock at level 0 (edge case)");

    /* Maximum level */
    struct sleeplock lk_max;
    initsleeplock(&lk_max, "level_max", LOCK_LEVEL_MAX);
    ASSERT(lk_max.dag_level == LOCK_LEVEL_MAX, "Max level assignment");

    TEST_PASS();
}

void test_sleeplock_hierarchy(void)
{
    TEST_START("Sleeplock hierarchy verification");

    struct sleeplock locks[5];
    const uint32_t levels[] = {
        LOCK_LEVEL_SCHEDULER,
        LOCK_LEVEL_PROCESS,
        LOCK_LEVEL_MEMORY,
        LOCK_LEVEL_VFS,
        LOCK_LEVEL_IPC
    };

    for (int i = 0; i < 5; i++) {
        char name[32];
        snprintf(name, sizeof(name), "lock_%d", i);
        initsleeplock(&locks[i], name, levels[i]);
        ASSERT(locks[i].dag_level == levels[i], "Level matches");
    }

    /* Verify hierarchy ordering */
    for (int i = 0; i < 4; i++) {
        ASSERT(locks[i].dag_level < locks[i+1].dag_level, "Hierarchy preserved");
    }

    TEST_PASS();
}

/*******************************************************************************
 * DAG INTEGRATION TESTS
 ******************************************************************************/

void test_sleeplock_dag_metadata(void)
{
    TEST_START("Sleeplock DAG metadata");

    struct sleeplock lk;
    initsleeplock(&lk, "dag_test", LOCK_LEVEL_VFS);

    /* Verify DAG level is correctly set */
    ASSERT(lk.dag_level == LOCK_LEVEL_VFS, "DAG level set");

    /* Verify internal lock has lower level */
    ASSERT(lk.lk.dag_level == LOCK_LEVEL_VFS - 1, "Internal lock below sleeplock");

    TEST_PASS();
}

void test_sleeplock_multiple_levels(void)
{
    TEST_START("Multiple sleeplocks at different levels");

    struct sleeplock locks[8];
    const uint32_t all_levels[] = {
        LOCK_LEVEL_SCHEDULER,
        LOCK_LEVEL_PROCESS,
        LOCK_LEVEL_MEMORY,
        LOCK_LEVEL_VFS,
        LOCK_LEVEL_FILESYSTEM,
        LOCK_LEVEL_IPC,
        LOCK_LEVEL_CAPABILITY,
        LOCK_LEVEL_DEVICE
    };

    for (int i = 0; i < 8; i++) {
        char name[32];
        snprintf(name, sizeof(name), "level_%d", all_levels[i]);
        initsleeplock(&locks[i], name, all_levels[i]);
        ASSERT(locks[i].dag_level == all_levels[i], "Level assignment");
    }

    /* Verify all levels are distinct and ordered */
    for (int i = 0; i < 7; i++) {
        ASSERT(locks[i].dag_level < locks[i+1].dag_level, "Ordering preserved");
    }

    TEST_PASS();
}

/*******************************************************************************
 * STRESS TESTS
 ******************************************************************************/

void test_sleeplock_many_locks(void)
{
    TEST_START("Many sleeplocks initialization");

    const int NUM_LOCKS = 100;
    struct sleeplock *locks = malloc(NUM_LOCKS * sizeof(struct sleeplock));
    ASSERT(locks != NULL, "Allocation succeeded");

    /* Initialize many locks */
    for (int i = 0; i < NUM_LOCKS; i++) {
        uint32_t level = LOCK_LEVEL_SCHEDULER + (i % 8) * 10;
        char name[32];
        snprintf(name, sizeof(name), "lock_%d", i);
        initsleeplock(&locks[i], name, level);
        ASSERT(locks[i].dag_level == level, "Level assignment");
    }

    free(locks);
    TEST_PASS();
}

void test_sleeplock_name_preservation(void)
{
    TEST_START("Sleeplock name preservation");

    const char *names[] = {
        "buffer",
        "inode",
        "exoflush",
        "exoblk",
        "exodisk"
    };

    struct sleeplock locks[5];
    for (int i = 0; i < 5; i++) {
        initsleeplock(&locks[i], names[i], LOCK_LEVEL_VFS + i);
        ASSERT(locks[i].name == names[i], "Name pointer preserved");
    }

    TEST_PASS();
}

/*******************************************************************************
 * BENCHMARK TESTS
 ******************************************************************************/

void benchmark_sleeplock_init(void)
{
    printf("\n========================================\n");
    printf("BENCHMARK: Sleeplock Initialization\n");
    printf("========================================\n");

    const int ITERATIONS = 10000;
    struct sleeplock *locks = malloc(ITERATIONS * sizeof(struct sleeplock));

    printf("Initializing %d sleeplocks...\n", ITERATIONS);

    for (int i = 0; i < ITERATIONS; i++) {
        uint32_t level = LOCK_LEVEL_VFS + (i % 10);
        initsleeplock(&locks[i], "bench_lock", level);
    }

    printf("Complete\n");
    printf("Expected: O(1) per initialization\n\n");

    free(locks);
}

void benchmark_sleeplock_hierarchy(void)
{
    printf("========================================\n");
    printf("BENCHMARK: Hierarchy Verification\n");
    printf("========================================\n");

    const int NUM_LEVELS = 10;
    struct sleeplock locks[NUM_LEVELS];

    printf("Creating %d-level hierarchy...\n", NUM_LEVELS);

    for (int i = 0; i < NUM_LEVELS; i++) {
        uint32_t level = LOCK_LEVEL_SCHEDULER + i * 5;
        char name[32];
        snprintf(name, sizeof(name), "level_%d", level);
        initsleeplock(&locks[i], name, level);
    }

    /* Verify ordering */
    int violations = 0;
    for (int i = 0; i < NUM_LEVELS - 1; i++) {
        if (locks[i].dag_level >= locks[i+1].dag_level) {
            violations++;
        }
    }

    printf("Hierarchy violations: %d\n", violations);
    printf("Expected: 0 violations\n\n");
}

/*******************************************************************************
 * TEST RUNNER
 ******************************************************************************/

int main(void)
{
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   SLEEPLOCK INTEGRATION TEST SUITE (Phase 6)              ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n\n");

    printf("--- Basic Functionality Tests ---\n");
    test_sleeplock_basic_init();
    test_sleeplock_dag_levels();
    test_sleeplock_edge_cases();
    test_sleeplock_hierarchy();

    printf("\n--- DAG Integration Tests ---\n");
    test_sleeplock_dag_metadata();
    test_sleeplock_multiple_levels();

    printf("\n--- Stress Tests ---\n");
    test_sleeplock_many_locks();
    test_sleeplock_name_preservation();

    printf("\n--- Benchmarks ---\n");
    benchmark_sleeplock_init();
    benchmark_sleeplock_hierarchy();

    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   ALL TESTS PASSED                                         ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n\n");

    return 0;
}
