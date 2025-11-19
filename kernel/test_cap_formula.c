/**
 * @file test_cap_formula.c
 * @brief Unit Tests for Lambda Formula System
 *
 * Tests all formula types and combinators to ensure correct rights computation.
 *
 * @see include/cap_formula.h for API documentation
 */

#include "cap_formula.h"
#include "capability_v2.h"
#include "printf.h"
#include <stdint.h>

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
            return -1; \
        } \
    } while (0)

#define TEST_ASSERT_EQ(actual, expected, message) \
    do { \
        if ((actual) != (expected)) { \
            printf("  FAIL: %s (expected %d, got %d)\n", message, (int)(expected), (int)(actual)); \
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
 * FORMULA TESTS
 ******************************************************************************/

/**
 * Test: Static formula
 */
static int test_formula_static(void)
{
    struct capability_v2 dummy_cap = {0};
    uint32_t rights = CAP_RIGHT_READ | CAP_RIGHT_WRITE;

    uint32_t result = formula_static(&dummy_cap, &rights);
    TEST_ASSERT_EQ(result, rights, "Static formula should return exact rights");

    return 0;
}

/**
 * Test: Time-based formula (before expiry)
 */
static int test_formula_time_based_before_expiry(void)
{
    struct capability_v2 dummy_cap = {0};

    time_based_formula_data_t data;
    data.expiry_time = UINT64_MAX; /* Far in future */
    data.base_rights = CAP_RIGHT_READ | CAP_RIGHT_WRITE;
    data.expired_rights = 0;

    uint32_t result = formula_time_based(&dummy_cap, &data);
    TEST_ASSERT_EQ(result, data.base_rights, "Should grant base rights before expiry");

    return 0;
}

/**
 * Test: Time-based formula (after expiry)
 */
static int test_formula_time_based_after_expiry(void)
{
    struct capability_v2 dummy_cap = {0};

    time_based_formula_data_t data;
    data.expiry_time = 0; /* Already expired */
    data.base_rights = CAP_RIGHT_READ | CAP_RIGHT_WRITE;
    data.expired_rights = CAP_RIGHT_READ; /* Read-only after expiry */

    uint32_t result = formula_time_based(&dummy_cap, &data);
    TEST_ASSERT_EQ(result, data.expired_rights, "Should grant expired rights after expiry");

    return 0;
}

/**
 * Test: Usage-based formula (under quota)
 */
static int test_formula_usage_based_under_quota(void)
{
    struct capability_v2 cap = {0};
    cap.access_count = 50;

    usage_based_formula_data_t data;
    data.max_accesses = 100;
    data.base_rights = CAP_RIGHT_READ;
    data.quota_exceeded_rights = 0;

    uint32_t result = formula_usage_based(&cap, &data);
    TEST_ASSERT_EQ(result, data.base_rights, "Should grant base rights under quota");

    return 0;
}

/**
 * Test: Usage-based formula (quota exceeded)
 */
static int test_formula_usage_based_quota_exceeded(void)
{
    struct capability_v2 cap = {0};
    cap.access_count = 150;

    usage_based_formula_data_t data;
    data.max_accesses = 100;
    data.base_rights = CAP_RIGHT_READ;
    data.quota_exceeded_rights = 0;

    uint32_t result = formula_usage_based(&cap, &data);
    TEST_ASSERT_EQ(result, data.quota_exceeded_rights, "Should grant reduced rights after quota");

    return 0;
}

/**
 * Test: User-based formula (matching user)
 */
static int test_formula_user_based_match(void)
{
    struct capability_v2 dummy_cap = {0};

    user_based_formula_data_t data;
    data.user_pids[0] = 0; /* Current PID (placeholder returns 0) */
    data.user_rights[0] = CAP_RIGHT_READ | CAP_RIGHT_WRITE;
    data.user_pids[1] = 100;
    data.user_rights[1] = CAP_RIGHT_READ;
    data.num_policies = 2;
    data.default_rights = 0;

    uint32_t result = formula_user_based(&dummy_cap, &data);
    TEST_ASSERT_EQ(result, CAP_RIGHT_READ | CAP_RIGHT_WRITE, "Should match first user");

    return 0;
}

/**
 * Test: User-based formula (no match, use default)
 */
static int test_formula_user_based_default(void)
{
    struct capability_v2 dummy_cap = {0};

    user_based_formula_data_t data;
    data.user_pids[0] = 999; /* Won't match (current PID is 0) */
    data.user_rights[0] = CAP_RIGHT_READ | CAP_RIGHT_WRITE;
    data.num_policies = 1;
    data.default_rights = CAP_RIGHT_READ;

    uint32_t result = formula_user_based(&dummy_cap, &data);
    TEST_ASSERT_EQ(result, CAP_RIGHT_READ, "Should use default rights");

    return 0;
}

/**
 * Test: Quota-based formula (under quota)
 */
static int test_formula_quota_based_under(void)
{
    struct capability_v2 cap = {0};
    cap.consumed.memory = Q16(500); /* 500 KB consumed */

    quota_based_formula_data_t data;
    data.max_quota.memory = Q16(1024); /* 1 MB limit */
    data.max_quota.cpu = Q16(1.0);
    data.max_quota.io_bandwidth = 0;
    data.max_quota.network_bandwidth = 0;
    data.max_quota.gpu_time = 0;
    data.max_quota.disk_quota = 0;
    data.max_quota.irq_count = 0;
    data.max_quota.capability_count = 0;
    data.base_rights = CAP_RIGHT_READ | CAP_RIGHT_WRITE;
    data.quota_exceeded_rights = CAP_RIGHT_READ;

    uint32_t result = formula_quota_based(&cap, &data);
    TEST_ASSERT_EQ(result, data.base_rights, "Should grant full rights under quota");

    return 0;
}

/**
 * Test: Quota-based formula (quota exceeded)
 */
static int test_formula_quota_based_exceeded(void)
{
    struct capability_v2 cap = {0};
    cap.consumed.memory = Q16(2048); /* 2 MB consumed (exceeds limit) */

    quota_based_formula_data_t data;
    data.max_quota.memory = Q16(1024); /* 1 MB limit */
    data.max_quota.cpu = Q16(1.0);
    data.max_quota.io_bandwidth = 0;
    data.max_quota.network_bandwidth = 0;
    data.max_quota.gpu_time = 0;
    data.max_quota.disk_quota = 0;
    data.max_quota.irq_count = 0;
    data.max_quota.capability_count = 0;
    data.base_rights = CAP_RIGHT_READ | CAP_RIGHT_WRITE;
    data.quota_exceeded_rights = CAP_RIGHT_READ;

    uint32_t result = formula_quota_based(&cap, &data);
    TEST_ASSERT_EQ(result, data.quota_exceeded_rights, "Should grant reduced rights over quota");

    return 0;
}

/**
 * Test: Combinator formula (AND)
 */
static int test_formula_combinator_and(void)
{
    struct capability_v2 dummy_cap = {0};

    uint32_t rights1 = CAP_RIGHT_READ | CAP_RIGHT_WRITE;
    uint32_t rights2 = CAP_RIGHT_READ | CAP_RIGHT_EXECUTE;

    combinator_formula_data_t comb;
    comb.formula1 = formula_static;
    comb.data1 = &rights1;
    comb.formula2 = formula_static;
    comb.data2 = &rights2;
    comb.combinator = FORMULA_COMBINATOR_AND;

    uint32_t result = formula_combinator(&dummy_cap, &comb);
    TEST_ASSERT_EQ(result, CAP_RIGHT_READ, "AND should return intersection (READ only)");

    return 0;
}

/**
 * Test: Combinator formula (OR)
 */
static int test_formula_combinator_or(void)
{
    struct capability_v2 dummy_cap = {0};

    uint32_t rights1 = CAP_RIGHT_READ;
    uint32_t rights2 = CAP_RIGHT_WRITE;

    combinator_formula_data_t comb;
    comb.formula1 = formula_static;
    comb.data1 = &rights1;
    comb.formula2 = formula_static;
    comb.data2 = &rights2;
    comb.combinator = FORMULA_COMBINATOR_OR;

    uint32_t result = formula_combinator(&dummy_cap, &comb);
    TEST_ASSERT_EQ(result, CAP_RIGHT_READ | CAP_RIGHT_WRITE, "OR should return union");

    return 0;
}

/**
 * Test: Combinator formula (NOT)
 */
static int test_formula_combinator_not(void)
{
    struct capability_v2 dummy_cap = {0};

    uint32_t rights = CAP_RIGHT_READ;

    combinator_formula_data_t comb;
    comb.formula1 = formula_static;
    comb.data1 = &rights;
    comb.formula2 = NULL;
    comb.data2 = NULL;
    comb.combinator = FORMULA_COMBINATOR_NOT;

    uint32_t result = formula_combinator(&dummy_cap, &comb);
    TEST_ASSERT_EQ(result, ~CAP_RIGHT_READ, "NOT should return bitwise complement");

    return 0;
}

/**
 * Test: Combinator formula (XOR)
 */
static int test_formula_combinator_xor(void)
{
    struct capability_v2 dummy_cap = {0};

    uint32_t rights1 = CAP_RIGHT_READ | CAP_RIGHT_WRITE;
    uint32_t rights2 = CAP_RIGHT_READ | CAP_RIGHT_EXECUTE;

    combinator_formula_data_t comb;
    comb.formula1 = formula_static;
    comb.data1 = &rights1;
    comb.formula2 = formula_static;
    comb.data2 = &rights2;
    comb.combinator = FORMULA_COMBINATOR_XOR;

    uint32_t result = formula_combinator(&dummy_cap, &comb);
    uint32_t expected = CAP_RIGHT_WRITE | CAP_RIGHT_EXECUTE; /* Symmetric difference */
    TEST_ASSERT_EQ(result, expected, "XOR should return symmetric difference");

    return 0;
}

/**
 * Test: Complex formula composition (time AND user)
 */
static int test_formula_complex_composition(void)
{
    struct capability_v2 dummy_cap = {0};

    /* Time-based: grants all rights (before expiry) */
    time_based_formula_data_t time_data;
    time_data.expiry_time = UINT64_MAX;
    time_data.base_rights = 0xFFFFFFFF;
    time_data.expired_rights = 0;

    /* User-based: grants READ|WRITE for PID 0 */
    user_based_formula_data_t user_data;
    user_data.user_pids[0] = 0;
    user_data.user_rights[0] = CAP_RIGHT_READ | CAP_RIGHT_WRITE;
    user_data.num_policies = 1;
    user_data.default_rights = 0;

    /* Combine with AND (both must pass) */
    combinator_formula_data_t comb;
    comb.formula1 = formula_time_based;
    comb.data1 = &time_data;
    comb.formula2 = formula_user_based;
    comb.data2 = &user_data;
    comb.combinator = FORMULA_COMBINATOR_AND;

    uint32_t result = formula_combinator(&dummy_cap, &comb);
    TEST_ASSERT_EQ(result, CAP_RIGHT_READ | CAP_RIGHT_WRITE,
                   "Composite should grant READ|WRITE (intersection of all rights and user rights)");

    return 0;
}

/*******************************************************************************
 * INTEGRATION TESTS (Formula with Capability System)
 ******************************************************************************/

/**
 * Test: Set and evaluate formula on capability
 */
static int test_formula_integration(void)
{
    extern void capv2_table_init(void);
    extern int capv2_alloc(uint64_t, uint8_t, uint32_t, resource_vector_t);
    extern int capv2_set_formula(int, cap_formula_t, void *);
    extern int capv2_check_rights(int, uint32_t);

    capv2_table_init();

    resource_vector_t quota = {0};
    int slot = capv2_alloc(0x1000, 1, CAP_RIGHT_READ | CAP_RIGHT_WRITE, quota);
    TEST_ASSERT(slot >= 0, "Allocation should succeed");

    /* Set time-based formula that expires immediately */
    time_based_formula_data_t data;
    data.expiry_time = 0; /* Already expired */
    data.base_rights = CAP_RIGHT_READ | CAP_RIGHT_WRITE;
    data.expired_rights = CAP_RIGHT_READ; /* Read-only after expiry */

    int ret = capv2_set_formula(slot, formula_time_based, &data);
    TEST_ASSERT_EQ(ret, 0, "Set formula should succeed");

    /* Check rights - should use formula, not static_rights */
    ret = capv2_check_rights(slot, CAP_RIGHT_WRITE);
    TEST_ASSERT_EQ(ret, -2, "Should deny WRITE (formula says expired, READ only)");

    ret = capv2_check_rights(slot, CAP_RIGHT_READ);
    TEST_ASSERT_EQ(ret, 0, "Should grant READ (formula allows)");

    return 0;
}

/*******************************************************************************
 * TEST SUITE RUNNER
 ******************************************************************************/

void run_all_formula_tests(void)
{
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   LAMBDA FORMULA SYSTEM - UNIT TESTS                       ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n");

    printf("\n=== BASIC FORMULA TESTS ===\n");
    RUN_TEST(test_formula_static);
    RUN_TEST(test_formula_time_based_before_expiry);
    RUN_TEST(test_formula_time_based_after_expiry);
    RUN_TEST(test_formula_usage_based_under_quota);
    RUN_TEST(test_formula_usage_based_quota_exceeded);
    RUN_TEST(test_formula_user_based_match);
    RUN_TEST(test_formula_user_based_default);
    RUN_TEST(test_formula_quota_based_under);
    RUN_TEST(test_formula_quota_based_exceeded);

    printf("\n=== COMBINATOR TESTS ===\n");
    RUN_TEST(test_formula_combinator_and);
    RUN_TEST(test_formula_combinator_or);
    RUN_TEST(test_formula_combinator_not);
    RUN_TEST(test_formula_combinator_xor);
    RUN_TEST(test_formula_complex_composition);

    printf("\n=== INTEGRATION TESTS ===\n");
    RUN_TEST(test_formula_integration);

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
