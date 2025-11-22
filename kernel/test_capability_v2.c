/**
 * @file test_capability_v2.c
 * @brief Comprehensive Unit Tests for PDAC Capability System V2
 *
 * This file contains extensive unit tests for the capability system,
 * covering all core operations, edge cases, and security properties.
 *
 * TEST CATEGORIES:
 * 1. Table Management (init, stats, allocation)
 * 2. Core Operations (alloc, free, grant, revoke, derive)
 * 3. Security Properties (rights attenuation, ABA prevention)
 * 4. Concurrency (TODO: requires threading support)
 * 5. Edge Cases (table full, invalid slots, overflow)
 *
 * TESTING METHODOLOGY:
 * - Each test is self-contained
 * - Tests print PASS/FAIL with detailed error messages
 * - Tests verify both positive and negative cases
 * - Tests validate security properties
 *
 * @see include/capability_v2.h for API documentation
 */

#include "capability_v2.h"
#include <stdio.h>
#include <stdint.h>

#define CAP_TABLE_SIZE CAP_TABLE_V2_SIZE

/*******************************************************************************
 * TEST FRAMEWORK
 ******************************************************************************/

static int g_tests_run = 0;
static int g_tests_passed = 0;
static int g_tests_failed = 0;

#define TEST_ASSERT(condition, message) \
    do { \
        if (!(condition)) { \
            printf("  FAIL: %s\n", message); \
            printf("    at %s:%d\n", __FILE__, __LINE__); \
            return -1; \
        } \
    } while (0)

#define TEST_ASSERT_EQ(actual, expected, message) \
    do { \
        if ((actual) != (expected)) { \
            printf("  FAIL: %s\n", message); \
            printf("    Expected: %d, Got: %d\n", (int)(expected), (int)(actual)); \
            printf("    at %s:%d\n", __FILE__, __LINE__); \
            return -1; \
        } \
    } while (0)

#define RUN_TEST(test_func) \
    do { \
        printf("\n[TEST] %s\n", #test_func); \
        g_tests_run++; \
        if (test_func() == 0) { \
            printf("  PASS\n"); \
            g_tests_passed++; \
        } else { \
            g_tests_failed++; \
        } \
    } while (0)

/*******************************************************************************
 * TABLE MANAGEMENT TESTS
 ******************************************************************************/

/**
 * Test: Capability table initialization
 */
static int test_table_init(void)
{
    capv2_table_init();

    uint32_t num_free, num_allocated;
    capv2_table_stats(&num_free, &num_allocated);

    TEST_ASSERT_EQ(num_allocated, 0, "Table should start with 0 allocated");
    TEST_ASSERT_EQ(num_free, CAP_TABLE_SIZE, "All slots should be free");

    return 0;
}

/**
 * Test: Table statistics tracking
 */
static int test_table_stats(void)
{
    capv2_table_init();

    /* Allocate some capabilities */
    resource_vector_t quota = {0};
    for (int i = 0; i < 10; i++) {
        int slot = capv2_alloc(i, CAP_TYPE_MEMORY_PAGE, CAP_RIGHT_READ, quota);
        TEST_ASSERT(slot >= 0, "Allocation should succeed");
    }

    uint32_t num_free, num_allocated;
    capv2_table_stats(&num_free, &num_allocated);

    TEST_ASSERT_EQ(num_allocated, 10, "Should have 10 allocated");
    TEST_ASSERT_EQ(num_free, CAP_TABLE_SIZE - 10, "Free count should match");

    return 0;
}

/**
 * Test: Table exhaustion (allocate until full)
 */
static int test_table_full(void)
{
    capv2_table_init();

    resource_vector_t quota = {0};
    int count = 0;

    /* Allocate until full */
    while (1) {
        int slot = capv2_alloc(count, CAP_TYPE_MEMORY_PAGE, CAP_RIGHT_READ, quota);
        if (slot < 0) {
            TEST_ASSERT_EQ(slot, CAPV2_ERR_TABLE_FULL, "Should return TABLE_FULL error");
            break;
        }
        count++;
    }

    TEST_ASSERT_EQ(count, CAP_TABLE_SIZE, "Should allocate exactly CAP_TABLE_SIZE slots");

    return 0;
}

/*******************************************************************************
 * CORE OPERATION TESTS
 ******************************************************************************/

/**
 * Test: Basic capability allocation
 */
static int test_alloc_basic(void)
{
    capv2_table_init();

    resource_vector_t quota = {.memory = Q16(1024)};
    int slot = capv2_alloc(0x1000, CAP_TYPE_MEMORY_PAGE,
                           CAP_RIGHT_READ | CAP_RIGHT_WRITE, quota);

    TEST_ASSERT(slot >= 0, "Allocation should succeed");
    TEST_ASSERT(slot < CAP_TABLE_SIZE, "Slot should be in valid range");

    /* Verify capability properties */
    struct capability_v2 cap_info;
    int ret = capv2_get_info(slot, &cap_info);

    TEST_ASSERT_EQ(ret, CAPV2_OK, "get_info should succeed");
    TEST_ASSERT_EQ(cap_info.resource_id, 0x1000, "Resource ID should match");
    TEST_ASSERT_EQ(cap_info.cap_type, CAP_TYPE_MEMORY_PAGE, "Type should match");
    TEST_ASSERT_EQ(cap_info.static_rights, CAP_RIGHT_READ | CAP_RIGHT_WRITE, "Rights should match");
    TEST_ASSERT_EQ(cap_info.refcount, 1, "Initial refcount should be 1");
    TEST_ASSERT_EQ(cap_info.quota.memory, Q16(1024), "Quota should match");

    return 0;
}

/**
 * Test: Invalid allocation (bad type)
 */
static int test_alloc_invalid_type(void)
{
    capv2_table_init();

    resource_vector_t quota = {0};
    int slot = capv2_alloc(0x1000, CAP_TYPE_NULL, CAP_RIGHT_READ, quota);

    TEST_ASSERT_EQ(slot, CAPV2_ERR_INVALID_TYPE, "Should reject NULL type");

    slot = capv2_alloc(0x1000, 99, CAP_RIGHT_READ, quota);
    TEST_ASSERT_EQ(slot, CAPV2_ERR_INVALID_TYPE, "Should reject invalid type");

    return 0;
}

/**
 * Test: Capability free
 */
static int test_free_basic(void)
{
    capv2_table_init();

    resource_vector_t quota = {0};
    int slot = capv2_alloc(0x1000, CAP_TYPE_MEMORY_PAGE, CAP_RIGHT_READ, quota);
    TEST_ASSERT(slot >= 0, "Allocation should succeed");

    /* Can't free while refcount > 0 */
    int ret = capv2_free(slot);
    TEST_ASSERT_EQ(ret, CAPV2_ERR_REFCOUNT_OVERFLOW, "Should fail with refcount > 0");

    /* Manually set refcount to 0 for testing */
    extern struct capability_v2 g_cap_table[];
    g_cap_table[slot].refcount = 0;

    ret = capv2_free(slot);
    TEST_ASSERT_EQ(ret, CAPV2_OK, "Free should succeed with refcount = 0");

    /* Verify slot is freed */
    ret = capv2_get_info(slot, NULL);
    TEST_ASSERT_EQ(ret, CAPV2_ERR_INVALID_SLOT, "Slot should be invalid after free");

    return 0;
}

/**
 * Test: Generation counter increment (ABA prevention)
 */
static int test_generation_counter(void)
{
    capv2_table_init();

    resource_vector_t quota = {0};
    int slot = capv2_alloc(0x1000, CAP_TYPE_MEMORY_PAGE, CAP_RIGHT_READ, quota);
    TEST_ASSERT(slot >= 0, "Allocation should succeed");

    struct capability_v2 cap_info;
    capv2_get_info(slot, &cap_info);
    uint32_t gen1 = cap_info.generation;

    /* Free and reallocate same slot */
    extern struct capability_v2 g_cap_table[];
    g_cap_table[slot].refcount = 0;
    capv2_free(slot);

    slot = capv2_alloc(0x2000, CAP_TYPE_MEMORY_PAGE, CAP_RIGHT_READ, quota);
    capv2_get_info(slot, &cap_info);
    uint32_t gen2 = cap_info.generation;

    TEST_ASSERT(gen2 > gen1, "Generation counter should increment");

    return 0;
}

/**
 * Test: Capability grant (delegation)
 */
static int test_grant_basic(void)
{
    capv2_table_init();

    resource_vector_t quota = {0};
    int src_slot = capv2_alloc(0x1000, CAP_TYPE_MEMORY_PAGE,
                               CAP_RIGHT_READ | CAP_RIGHT_WRITE | CAP_RIGHT_GRANT,
                               quota);
    TEST_ASSERT(src_slot >= 0, "Source allocation should succeed");

    /* Grant read-only to another process */
    int dst_slot = capv2_grant(src_slot, 100, CAP_RIGHT_READ);
    TEST_ASSERT(dst_slot >= 0, "Grant should succeed");

    /* Verify destination capability */
    struct capability_v2 dst_info;
    capv2_get_info(dst_slot, &dst_info);

    TEST_ASSERT_EQ(dst_info.resource_id, 0x1000, "Resource ID should match");
    TEST_ASSERT_EQ(dst_info.static_rights, CAP_RIGHT_READ, "Rights should be attenuated");
    TEST_ASSERT_EQ(dst_info.owner_pid, 100, "Owner PID should be recipient");
    TEST_ASSERT_EQ(dst_info.parent_slot, src_slot, "Parent should be source");

    /* Verify source refcount incremented */
    struct capability_v2 src_info;
    capv2_get_info(src_slot, &src_info);
    TEST_ASSERT_EQ(src_info.refcount, 2, "Source refcount should be 2");

    return 0;
}

/**
 * Test: Grant without GRANT right (should fail)
 */
static int test_grant_no_permission(void)
{
    capv2_table_init();

    resource_vector_t quota = {0};
    int src_slot = capv2_alloc(0x1000, CAP_TYPE_MEMORY_PAGE,
                               CAP_RIGHT_READ, /* No GRANT right */
                               quota);
    TEST_ASSERT(src_slot >= 0, "Allocation should succeed");

    int dst_slot = capv2_grant(src_slot, 100, CAP_RIGHT_READ);
    TEST_ASSERT_EQ(dst_slot, CAPV2_ERR_NO_PERMISSION, "Grant should fail without GRANT right");

    return 0;
}

/**
 * Test: Rights attenuation (can't escalate)
 */
static int test_grant_rights_attenuation(void)
{
    capv2_table_init();

    resource_vector_t quota = {0};
    int src_slot = capv2_alloc(0x1000, CAP_TYPE_MEMORY_PAGE,
                               CAP_RIGHT_READ | CAP_RIGHT_GRANT,
                               quota);
    TEST_ASSERT(src_slot >= 0, "Allocation should succeed");

    /* Try to grant WRITE (which source doesn't have) */
    int dst_slot = capv2_grant(src_slot, 100, CAP_RIGHT_READ | CAP_RIGHT_WRITE);
    TEST_ASSERT_EQ(dst_slot, CAPV2_ERR_NO_PERMISSION, "Should fail (rights escalation attempt)");

    /* Grant subset of rights (should succeed) */
    dst_slot = capv2_grant(src_slot, 100, CAP_RIGHT_READ);
    TEST_ASSERT(dst_slot >= 0, "Should succeed (rights attenuation)");

    return 0;
}

/**
 * Test: Capability revocation
 */
static int test_revoke_basic(void)
{
    capv2_table_init();

    resource_vector_t quota = {0};
    int parent = capv2_alloc(0x1000, CAP_TYPE_MEMORY_PAGE,
                             CAP_RIGHT_READ | CAP_RIGHT_GRANT | CAP_RIGHT_REVOKE,
                             quota);
    TEST_ASSERT(parent >= 0, "Parent allocation should succeed");

    /* Grant to create child */
    int child = capv2_grant(parent, 100, CAP_RIGHT_READ);
    TEST_ASSERT(child >= 0, "Grant should succeed");

    /* Revoke parent (should also revoke child) */
    int ret = capv2_revoke(parent);
    TEST_ASSERT_EQ(ret, CAPV2_OK, "Revoke should succeed");

    /* Verify child is also revoked */
    ret = capv2_get_info(child, NULL);
    TEST_ASSERT_EQ(ret, CAPV2_ERR_INVALID_SLOT, "Child should be revoked");

    return 0;
}

/**
 * Test: Derive with quota partitioning
 */
static int test_derive_quota_partition(void)
{
    capv2_table_init();

    resource_vector_t parent_quota = {.memory = Q16(1024)}; /* 1 MB */
    int parent = capv2_alloc(0x1000, CAP_TYPE_MEMORY_PAGE,
                             CAP_RIGHT_READ | CAP_RIGHT_DERIVE,
                             parent_quota);
    TEST_ASSERT(parent >= 0, "Parent allocation should succeed");

    resource_vector_t child_quota = {.memory = Q16(256)}; /* 256 KB */
    int child = capv2_derive(parent, child_quota, CAP_RIGHT_READ);
    TEST_ASSERT(child >= 0, "Derive should succeed");

    /* Verify parent quota reduced */
    struct capability_v2 parent_info;
    capv2_get_info(parent, &parent_info);
    TEST_ASSERT_EQ(parent_info.quota.memory, Q16(768), "Parent quota should be reduced by 256");

    /* Verify child has allocated quota */
    struct capability_v2 child_info;
    capv2_get_info(child, &child_info);
    TEST_ASSERT_EQ(child_info.quota.memory, Q16(256), "Child should have 256 KB quota");

    return 0;
}

/**
 * Test: Derive with quota exceeded (should fail)
 */
static int test_derive_quota_exceeded(void)
{
    capv2_table_init();

    resource_vector_t parent_quota = {.memory = Q16(100)};
    int parent = capv2_alloc(0x1000, CAP_TYPE_MEMORY_PAGE,
                             CAP_RIGHT_READ | CAP_RIGHT_DERIVE,
                             parent_quota);
    TEST_ASSERT(parent >= 0, "Parent allocation should succeed");

    resource_vector_t child_quota = {.memory = Q16(200)}; /* Exceeds parent */
    int child = capv2_derive(parent, child_quota, CAP_RIGHT_READ);
    TEST_ASSERT_EQ(child, CAPV2_ERR_QUOTA_EXCEEDED, "Should fail (quota exceeded)");

    return 0;
}

/**
 * Test: Check rights (basic)
 */
static int test_check_rights_basic(void)
{
    capv2_table_init();

    resource_vector_t quota = {0};
    int slot = capv2_alloc(0x1000, CAP_TYPE_MEMORY_PAGE,
                           CAP_RIGHT_READ | CAP_RIGHT_WRITE,
                           quota);
    TEST_ASSERT(slot >= 0, "Allocation should succeed");

    /* Check for rights we have */
    int ret = capv2_check_rights(slot, CAP_RIGHT_READ);
    TEST_ASSERT_EQ(ret, CAPV2_OK, "Should have READ right");

    ret = capv2_check_rights(slot, CAP_RIGHT_READ | CAP_RIGHT_WRITE);
    TEST_ASSERT_EQ(ret, CAPV2_OK, "Should have READ|WRITE");

    /* Check for rights we don't have */
    ret = capv2_check_rights(slot, CAP_RIGHT_EXECUTE);
    TEST_ASSERT_EQ(ret, CAPV2_ERR_NO_PERMISSION, "Should not have EXECUTE");

    return 0;
}

/**
 * Test: Find capability by resource ID
 */
static int test_find_capability(void)
{
    capv2_table_init();

    resource_vector_t quota = {0};
    int slot = capv2_alloc(0xCAFE, CAP_TYPE_MEMORY_PAGE, CAP_RIGHT_READ, quota);
    TEST_ASSERT(slot >= 0, "Allocation should succeed");

    /* Find by resource ID */
    int found = capv2_find(0xCAFE, -1);
    TEST_ASSERT_EQ(found, slot, "Should find correct slot");

    /* Find non-existent resource */
    found = capv2_find(0xDEAD, -1);
    TEST_ASSERT_EQ(found, CAPV2_ERR_NOT_FOUND, "Should not find non-existent resource");

    return 0;
}

/*******************************************************************************
 * EDGE CASE TESTS
 ******************************************************************************/

/**
 * Test: Invalid slot operations
 */
static int test_invalid_slot_operations(void)
{
    capv2_table_init();

    /* Try operations on invalid slots */
    int ret = capv2_free(-1);
    TEST_ASSERT_EQ(ret, CAPV2_ERR_INVALID_SLOT, "Should reject negative slot");

    ret = capv2_free(CAP_TABLE_SIZE);
    TEST_ASSERT_EQ(ret, CAPV2_ERR_INVALID_SLOT, "Should reject out-of-range slot");

    ret = capv2_check_rights(9999, CAP_RIGHT_READ);
    TEST_ASSERT_EQ(ret, CAPV2_ERR_INVALID_SLOT, "Should reject invalid slot");

    return 0;
}

/**
 * Test: Refcount overflow protection
 */
static int test_refcount_overflow(void)
{
    capv2_table_init();

    resource_vector_t quota = {0};
    int slot = capv2_alloc(0x1000, CAP_TYPE_MEMORY_PAGE,
                           CAP_RIGHT_READ | CAP_RIGHT_GRANT,
                           quota);
    TEST_ASSERT(slot >= 0, "Allocation should succeed");

    /* Manually set refcount to max */
    extern struct capability_v2 g_cap_table[];
    g_cap_table[slot].refcount = UINT32_MAX;

    /* Try to grant (should fail due to refcount overflow) */
    int ret = capv2_grant(slot, 100, CAP_RIGHT_READ);
    TEST_ASSERT_EQ(ret, CAPV2_ERR_REFCOUNT_OVERFLOW, "Should fail (refcount overflow)");

    return 0;
}

/*******************************************************************************
 * TEST SUITE RUNNER
 ******************************************************************************/

/**
 * Run all capability system unit tests
 */
void run_all_capability_tests(void)
{
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   PDAC CAPABILITY SYSTEM V2 - UNIT TESTS                   ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n");

    /* Table Management Tests */
    printf("\n=== TABLE MANAGEMENT TESTS ===\n");
    RUN_TEST(test_table_init);
    RUN_TEST(test_table_stats);
    RUN_TEST(test_table_full);

    /* Core Operation Tests */
    printf("\n=== CORE OPERATION TESTS ===\n");
    RUN_TEST(test_alloc_basic);
    RUN_TEST(test_alloc_invalid_type);
    RUN_TEST(test_free_basic);
    RUN_TEST(test_generation_counter);
    RUN_TEST(test_grant_basic);
    RUN_TEST(test_grant_no_permission);
    RUN_TEST(test_grant_rights_attenuation);
    RUN_TEST(test_revoke_basic);
    RUN_TEST(test_derive_quota_partition);
    RUN_TEST(test_derive_quota_exceeded);
    RUN_TEST(test_check_rights_basic);
    RUN_TEST(test_find_capability);

    /* Edge Case Tests */
    printf("\n=== EDGE CASE TESTS ===\n");
    RUN_TEST(test_invalid_slot_operations);
    RUN_TEST(test_refcount_overflow);

    /* Summary */
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   TEST SUMMARY                                              ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n");
    printf("Tests Run:    %d\n", g_tests_run);
    printf("Tests Passed: %d\n", g_tests_passed);
    printf("Tests Failed: %d\n", g_tests_failed);

    if (g_tests_failed == 0) {
        printf("\n✓ ALL TESTS PASSED\n\n");
    } else {
        printf("\n✗ SOME TESTS FAILED\n\n");
    }
}
