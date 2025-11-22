/**
 * @file cap_formula.c
 * @brief Lambda Formula System Implementation
 *
 * This file implements standard formula functions for dynamic capability
 * rights computation. Formulas demonstrate how lambda calculus enables
 * flexible security policies at kernel level.
 *
 * @see include/cap_formula.h for API documentation
 */

#include "cap_formula.h"
#include "capability_v2.h"
#include "printf.h"
#include <stddef.h>
#include <stdint.h>
#include <string.h>

/*******************************************************************************
 * PLATFORM-SPECIFIC HELPERS
 ******************************************************************************/

/**
 * Get current timestamp (milliseconds since boot)
 *
 * TODO: Implement using platform timer
 * For now, returns a placeholder value for testing
 */
uint64_t formula_get_time(void)
{
    /* TODO: Integrate with kernel timer (TSC, HPET, etc.) */
    return 0; /* Placeholder */
}

/**
 * Get current process ID
 *
 * TODO: Implement using process manager API
 * For now, returns a placeholder value for testing
 */
uint32_t formula_get_pid(void)
{
    /* TODO: Integrate with process manager */
    return 0; /* Placeholder */
}

/*******************************************************************************
 * STANDARD FORMULA IMPLEMENTATIONS
 ******************************************************************************/

/**
 * Time-based formula: Grant rights before expiry
 *
 * LAMBDA CALCULUS NOTATION:
 * λ(cap, data). if (current_time < data->expiry_time)
 *               then data->base_rights
 *               else data->expired_rights
 *
 * REAL-WORLD ANALOGY:
 * Like OAuth access tokens that expire after N hours
 */
uint32_t formula_time_based(const struct capability_v2 *cap, void *data)
{
    if (data == NULL) {
        return 0; /* No rights if data is NULL */
    }

    time_based_formula_data_t *tdata = (time_based_formula_data_t *)data;

    uint64_t current_time = formula_get_time();

    if (current_time < tdata->expiry_time) {
        /* Before expiry: grant base rights */
        return tdata->base_rights;
    } else {
        /* After expiry: grant expired rights (usually 0) */
        return tdata->expired_rights;
    }
}

/**
 * Usage-based formula: Grant rights for first N accesses
 *
 * LAMBDA CALCULUS NOTATION:
 * λ(cap, data). if (cap->access_count < data->max_accesses)
 *               then data->base_rights
 *               else data->quota_exceeded_rights
 *
 * REAL-WORLD ANALOGY:
 * Like AWS free tier (first N requests free, then pay-per-use)
 * Like trial software (first N runs free, then requires license)
 */
uint32_t formula_usage_based(const struct capability_v2 *cap, void *data)
{
    if (cap == NULL || data == NULL) {
        return 0;
    }

    usage_based_formula_data_t *udata = (usage_based_formula_data_t *)data;

    if (cap->access_count < udata->max_accesses) {
        /* Under quota: grant base rights */
        return udata->base_rights;
    } else {
        /* Quota exceeded: grant reduced rights */
        return udata->quota_exceeded_rights;
    }
}

/**
 * User-based formula: Grant rights based on calling process
 *
 * LAMBDA CALCULUS NOTATION:
 * λ(cap, data). lookup(current_pid, data->user_policies)
 *               ?: data->default_rights
 *
 * REAL-WORLD ANALOGY:
 * Like Unix file permissions (owner vs. group vs. other)
 * Like SELinux user-based access control
 */
uint32_t formula_user_based(const struct capability_v2 *cap, void *data)
{
    if (data == NULL) {
        return 0;
    }

    user_based_formula_data_t *udata = (user_based_formula_data_t *)data;

    uint32_t current_pid = formula_get_pid();

    /* Search for matching user policy */
    for (uint32_t i = 0; i < udata->num_policies && i < MAX_USER_POLICIES; i++) {
        if (udata->user_pids[i] == current_pid) {
            return udata->user_rights[i];
        }
    }

    /* No match found: return default rights */
    return udata->default_rights;
}

/**
 * Quota-based formula: Grant rights while under resource quota
 *
 * LAMBDA CALCULUS NOTATION:
 * λ(cap, data). if (cap->consumed ≤ data->max_quota)  [8D comparison]
 *               then data->base_rights
 *               else data->quota_exceeded_rights
 *
 * PDAC INNOVATION:
 * Uses 8D resource vectors for multi-dimensional quota enforcement.
 * Checks CPU, memory, I/O, network, GPU, disk, IRQ, capability consumption.
 *
 * REAL-WORLD ANALOGY:
 * Like cgroups memory limits (SIGKILL when exceeded)
 * Like disk quotas (read-only when full)
 */
uint32_t formula_quota_based(const struct capability_v2 *cap, void *data)
{
    if (cap == NULL || data == NULL) {
        return 0;
    }

    quota_based_formula_data_t *qdata = (quota_based_formula_data_t *)data;

    /* Check if any dimension exceeds quota (8D component-wise check)
     * Using octonion components: e0=CPU, e1=memory, e2=IO, e3=network,
     * e4=GPU, e5=disk, e6=IRQ, e7=capability_count */
    if (cap->consumed.e0 > qdata->max_quota.e0 ||
        cap->consumed.e1 > qdata->max_quota.e1 ||
        cap->consumed.e2 > qdata->max_quota.e2 ||
        cap->consumed.e3 > qdata->max_quota.e3 ||
        cap->consumed.e4 > qdata->max_quota.e4 ||
        cap->consumed.e5 > qdata->max_quota.e5 ||
        cap->consumed.e6 > qdata->max_quota.e6 ||
        cap->consumed.e7 > qdata->max_quota.e7) {
        /* Quota exceeded: grant reduced rights */
        return qdata->quota_exceeded_rights;
    } else {
        /* Under quota: grant full rights */
        return qdata->base_rights;
    }
}

/**
 * Combinator formula: Compose two formulas with Boolean operator
 *
 * LAMBDA CALCULUS NOTATION (for AND):
 * λ(cap, data). (data->formula1)(cap, data->data1) ∧
 *               (data->formula2)(cap, data->data2)
 *
 * HIGHER-ORDER FUNCTION:
 * This is a higher-order function: it takes functions as arguments
 * and composes them. Enables building complex policies from simple ones.
 *
 * COMBINATOR LOGIC:
 * - AND: rights1 & rights2  (both formulas must grant)
 * - OR:  rights1 | rights2  (either formula grants)
 * - NOT: ~rights1           (invert all bits)
 * - XOR: rights1 ^ rights2  (exactly one formula grants)
 */
uint32_t formula_combinator(const struct capability_v2 *cap, void *data)
{
    if (data == NULL) {
        return 0;
    }

    combinator_formula_data_t *cdata = (combinator_formula_data_t *)data;

    /* Evaluate first formula */
    uint32_t rights1 = 0;
    if (cdata->formula1 != NULL) {
        rights1 = cdata->formula1(cap, cdata->data1);
    }

    /* For NOT combinator, skip second formula */
    if (cdata->combinator == FORMULA_COMBINATOR_NOT) {
        return ~rights1;
    }

    /* Evaluate second formula */
    uint32_t rights2 = 0;
    if (cdata->formula2 != NULL) {
        rights2 = cdata->formula2(cap, cdata->data2);
    }

    /* Apply combinator */
    switch (cdata->combinator) {
        case FORMULA_COMBINATOR_AND:
            return rights1 & rights2;

        case FORMULA_COMBINATOR_OR:
            return rights1 | rights2;

        case FORMULA_COMBINATOR_XOR:
            return rights1 ^ rights2;

        case FORMULA_COMBINATOR_NOT:
            /* Already handled above */
            return ~rights1;

        default:
            return 0; /* Unknown combinator */
    }
}

/**
 * Static formula: Always return fixed rights (for testing)
 *
 * LAMBDA CALCULUS NOTATION:
 * λ(cap, data). *data  (constant function)
 */
uint32_t formula_static(const struct capability_v2 *cap, void *data)
{
    if (data == NULL) {
        return 0;
    }

    return *(uint32_t *)data;
}

/*******************************************************************************
 * FORMULA COMPOSITION API
 ******************************************************************************/

/**
 * Create a combinator formula (higher-order function)
 *
 * ALLOCATES: combinator_formula_data_t structure
 * CALLER MUST FREE: Using free_combinator()
 *
 * NOTE: This does NOT allocate or copy child data (d1, d2).
 * Caller is responsible for managing child data lifetime.
 */
combinator_formula_data_t *create_combinator(
    cap_formula_t f1, void *d1,
    cap_formula_t f2, void *d2,
    formula_combinator_t combinator)
{
    /* TODO: Replace with proper kernel allocator (kmalloc, slab, etc.) */
    /* For now, return NULL (will implement in Phase 2.3.3) */
    (void)f1; (void)d1; (void)f2; (void)d2; (void)combinator;
    return NULL;
}

/**
 * Free combinator formula data (non-recursive)
 *
 * NOTE: This does NOT free child data (data1, data2).
 * Caller must manage child data separately.
 */
void free_combinator(combinator_formula_data_t *comb_data)
{
    if (comb_data == NULL) {
        return;
    }

    /* TODO: Replace with proper kernel deallocator (kfree, etc.) */
    /* For now, no-op (will implement in Phase 2.3.3) */
}

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Time-limited read-only access
 *
 * SCENARIO: Grant READ access to a file for 1 hour, then revoke
 *
 * USE CASE:
 * - Temporary file sharing
 * - Time-limited delegation
 * - OAuth-style expiring tokens
 *
 * DEMONSTRATES:
 * - Time-based formulas
 * - Automatic revocation without kernel intervention
 */
void example_time_limited_access(void)
{
    printf("\n=== Example: Time-Limited Access ===\n");
    printf("Scenario: Grant READ access for 1 hour, then revoke\n\n");

    /* Create time-based formula data */
    time_based_formula_data_t time_data;
    time_data.expiry_time = formula_get_time() + (60 * 60 * 1000); /* 1 hour */
    time_data.base_rights = CAP_RIGHT_READ;
    time_data.expired_rights = 0; /* No rights after expiry */

    printf("Formula: λ(cap). if (time < %lu) then READ else NONE\n",
           time_data.expiry_time);

    /* Test formula before expiry */
    struct capability_v2 dummy_cap;
    uint32_t rights = formula_time_based(&dummy_cap, &time_data);

    printf("Rights before expiry: 0x%x ", rights);
    if (rights & CAP_RIGHT_READ) printf("(READ)");
    printf("\n");

    /* Simulate time passing (set expiry to past) */
    time_data.expiry_time = 0;
    rights = formula_time_based(&dummy_cap, &time_data);

    printf("Rights after expiry:  0x%x ", rights);
    if (rights == 0) printf("(NONE)");
    printf("\n");

    printf("===================================\n\n");
}

/**
 * Example: Metered access (100 reads, then revoke)
 *
 * SCENARIO: Grant READ for first 100 accesses, then revoke
 *
 * USE CASE:
 * - Free tier / trial access
 * - Usage quotas
 * - Rate limiting
 *
 * DEMONSTRATES:
 * - Usage-based formulas
 * - Access counting
 */
void example_metered_access(void)
{
    printf("\n=== Example: Metered Access ===\n");
    printf("Scenario: Grant READ for first 100 accesses, then revoke\n\n");

    /* Create usage-based formula data */
    usage_based_formula_data_t usage_data;
    usage_data.max_accesses = 100;
    usage_data.base_rights = CAP_RIGHT_READ;
    usage_data.quota_exceeded_rights = 0; /* No rights after quota */

    printf("Formula: λ(cap). if (cap->access_count < 100) then READ else NONE\n");

    /* Test formula with different access counts */
    struct capability_v2 dummy_cap;

    dummy_cap.access_count = 50;
    uint32_t rights = formula_usage_based(&dummy_cap, &usage_data);
    printf("After 50 accesses:  0x%x ", rights);
    if (rights & CAP_RIGHT_READ) printf("(READ)");
    printf("\n");

    dummy_cap.access_count = 100;
    rights = formula_usage_based(&dummy_cap, &usage_data);
    printf("After 100 accesses: 0x%x ", rights);
    if (rights == 0) printf("(NONE - quota exceeded)");
    printf("\n");

    printf("===============================\n\n");
}

/**
 * Example: Role-based access control (RBAC)
 *
 * SCENARIO: Admin gets READ|WRITE, guest gets READ, others get NONE
 *
 * USE CASE:
 * - Multi-user systems
 * - Role-based policies
 * - User isolation
 *
 * DEMONSTRATES:
 * - User-based formulas
 * - Different rights per user
 */
void example_rbac(void)
{
    printf("\n=== Example: Role-Based Access Control ===\n");
    printf("Scenario: Admin (PID 1) gets READ|WRITE, Guest (PID 100) gets READ\n\n");

    /* Create user-based formula data */
    user_based_formula_data_t user_data;
    user_data.user_pids[0] = 1;    /* Admin PID */
    user_data.user_rights[0] = CAP_RIGHT_READ | CAP_RIGHT_WRITE;
    user_data.user_pids[1] = 100;  /* Guest PID */
    user_data.user_rights[1] = CAP_RIGHT_READ;
    user_data.num_policies = 2;
    user_data.default_rights = 0;  /* No access for others */

    printf("Formula: λ(cap). match current_pid with\n");
    printf("         | 1   -> READ|WRITE\n");
    printf("         | 100 -> READ\n");
    printf("         | _   -> NONE\n\n");

    /* Note: formula_get_pid() currently returns 0 (placeholder) */
    printf("(Current implementation uses placeholder PID = 0)\n");

    printf("==========================================\n\n");
}

/**
 * Example: Complex policy composition
 *
 * SCENARIO: Grant READ|WRITE if (time valid) AND (user authorized)
 *
 * USE CASE:
 * - Complex enterprise policies
 * - Multi-factor access control
 * - AWS IAM-style policy composition
 *
 * DEMONSTRATES:
 * - Combinator formulas (higher-order functions)
 * - Policy composition via AND combinator
 * - Building complex policies from simple ones
 */
void example_complex_policy(void)
{
    printf("\n=== Example: Complex Policy Composition ===\n");
    printf("Policy: Grant READ|WRITE if (time valid) AND (user == admin)\n\n");

    /* Create time-based sub-policy */
    time_based_formula_data_t time_data;
    time_data.expiry_time = formula_get_time() + 3600000; /* 1 hour */
    time_data.base_rights = 0xFFFFFFFF; /* All rights (will be filtered by AND) */
    time_data.expired_rights = 0;

    /* Create user-based sub-policy */
    user_based_formula_data_t user_data;
    user_data.user_pids[0] = 1; /* Admin */
    user_data.user_rights[0] = CAP_RIGHT_READ | CAP_RIGHT_WRITE;
    user_data.num_policies = 1;
    user_data.default_rights = 0;

    /* Create AND combinator */
    combinator_formula_data_t comb_data;
    comb_data.formula1 = formula_time_based;
    comb_data.data1 = &time_data;
    comb_data.formula2 = formula_user_based;
    comb_data.data2 = &user_data;
    comb_data.combinator = FORMULA_COMBINATOR_AND;

    printf("Formula: λ(cap). time_check(cap) ∧ user_check(cap)\n");
    printf("         where time_check grants ALL if before expiry\n");
    printf("               user_check grants READ|WRITE if PID == 1\n\n");

    /* Test combined formula */
    struct capability_v2 dummy_cap;
    uint32_t rights = formula_combinator(&dummy_cap, &comb_data);

    printf("Combined rights: 0x%x\n", rights);
    printf("(Result depends on current time and PID)\n");

    printf("==========================================\n\n");
}

/**
 * Example: Resource quota enforcement
 *
 * SCENARIO: Grant full access until memory quota exceeded, then read-only
 *
 * USE CASE:
 * - Resource accounting
 * - Fair scheduling
 * - Cgroups-style limits
 *
 * DEMONSTRATES:
 * - Quota-based formulas
 * - 8D resource vector enforcement
 * - Graceful degradation (full -> read-only -> none)
 */
void example_quota_enforcement(void)
{
    printf("\n=== Example: Resource Quota Enforcement ===\n");
    printf("Scenario: Full access until 1 MB consumed, then read-only\n\n");

    /* Create quota-based formula data */
    quota_based_formula_data_t quota_data;
    quota_data.max_quota.cpu = Q16(1.0);     /* 100% CPU */
    quota_data.max_quota.memory = Q16(1024); /* 1 MB */
    quota_data.max_quota.io_bandwidth = Q16(10000);
    quota_data.max_quota.network_bandwidth = Q16(10000);
    quota_data.max_quota.gpu_time = Q16(1.0);
    quota_data.max_quota.disk_quota = Q16(10000);
    quota_data.max_quota.irq_count = 0;
    quota_data.max_quota.capability_count = 0;

    quota_data.base_rights = CAP_RIGHT_READ | CAP_RIGHT_WRITE;
    quota_data.quota_exceeded_rights = CAP_RIGHT_READ; /* Read-only after quota */

    printf("Formula: λ(cap). if (cap->consumed.memory ≤ 1 MB)\n");
    printf("                 then READ|WRITE\n");
    printf("                 else READ\n\n");

    /* Test with different consumption levels */
    struct capability_v2 dummy_cap;

    /* Initialize consumed to zero */
    dummy_cap.consumed.cpu = 0;
    dummy_cap.consumed.memory = Q16(512); /* 512 KB */
    dummy_cap.consumed.io_bandwidth = 0;
    dummy_cap.consumed.network_bandwidth = 0;
    dummy_cap.consumed.gpu_time = 0;
    dummy_cap.consumed.disk_quota = 0;
    dummy_cap.consumed.irq_count = 0;
    dummy_cap.consumed.capability_count = 0;

    uint32_t rights = formula_quota_based(&dummy_cap, &quota_data);
    printf("After 512 KB consumed: 0x%x ", rights);
    if (rights & CAP_RIGHT_WRITE) printf("(READ|WRITE)");
    printf("\n");

    /* Exceed quota */
    dummy_cap.consumed.memory = Q16(2048); /* 2 MB (exceeds 1 MB quota) */
    rights = formula_quota_based(&dummy_cap, &quota_data);
    printf("After 2 MB consumed:   0x%x ", rights);
    if ((rights & CAP_RIGHT_READ) && !(rights & CAP_RIGHT_WRITE)) {
        printf("(READ only - quota exceeded)");
    }
    printf("\n");

    printf("==========================================\n\n");
}

/**
 * Run all pedagogical examples
 *
 * USAGE: Call during kernel boot or from user command
 */
void formula_run_all_examples(void)
{
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   PDAC LAMBDA FORMULA SYSTEM - PEDAGOGICAL EXAMPLES        ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n");

    example_time_limited_access();
    example_metered_access();
    example_rbac();
    example_complex_policy();
    example_quota_enforcement();

    printf("All formula examples completed.\n");
    printf("See docs/PDAC_UNIFIED_FRAMEWORK.md for theoretical background.\n\n");
}
