/**
 * @file cap_formula.h
 * @brief Lambda Formula System for Dynamic Capability Rights
 *
 * This file implements a lambda calculus-based formula system for computing
 * capability rights dynamically. Formulas are first-class functions that
 * evaluate rights based on context (time, usage, user, etc.).
 *
 * THEORETICAL FOUNDATION:
 * - Lambda calculus: Functions as first-class values
 * - Combinatory logic: Formula composition via AND/OR/NOT combinators
 * - Higher-order functions: Formulas that produce formulas
 *
 * REAL-WORLD INSPIRATION:
 * - AWS IAM policy evaluation (JSON-based policies)
 * - SELinux policy language (TE rules with boolean expressions)
 * - OAuth scopes with time-limited tokens
 * - Our approach: Kernel-level, C-based lambda calculus
 *
 * PEDAGOGICAL NOTES:
 * This demonstrates how functional programming concepts (lambda calculus,
 * combinators, higher-order functions) can be implemented in C and used
 * in kernel-level security primitives.
 *
 * @see kernel/cap_formula.c for standard formula implementations
 * @see docs/PDAC_UNIFIED_FRAMEWORK.md for theoretical background
 */

#ifndef CAP_FORMULA_H
#define CAP_FORMULA_H

#include <stdint.h>
#include "capability_v2.h"

/*******************************************************************************
 * FORWARD DECLARATIONS
 ******************************************************************************/

struct capability_v2; /* Defined in capability_v2.h */

/*******************************************************************************
 * FORMULA FUNCTION SIGNATURE
 ******************************************************************************/

/**
 * Formula function signature
 *
 * A formula is a function that takes a capability and opaque data, and
 * returns a rights bitmask.
 *
 * @param cap Capability to evaluate (read-only)
 * @param data Opaque formula-specific data (state, parameters, etc.)
 * @return Rights bitmask (combination of CAP_RIGHT_* flags)
 *
 * LAMBDA CALCULUS:
 * In lambda calculus notation: λ(cap, data).rights
 * In C: uint32_t (*formula)(const struct capability_v2 *, void *)
 *
 * EXAMPLES:
 * - Time-based: Return 0 (no rights) if current_time > expiry_time
 * - Usage-based: Return 0 after N accesses
 * - User-based: Return different rights for different users
 *
 * NOTE: cap_formula_t is defined in capability_v2.h as the primary type.
 * This legacy signature is used for simpler formula implementations.
 */
typedef uint32_t (*cap_formula_legacy_t)(const struct capability_v2 *cap, void *data);

/*******************************************************************************
 * COMBINATOR TYPES
 ******************************************************************************/

/**
 * Formula combinator types
 *
 * Combinators allow composing simple formulas into complex policies.
 * Based on combinatory logic (SKI calculus, Boolean algebra).
 *
 * BOOLEAN ALGEBRA MAPPING:
 * - AND: Intersection of rights (both formulas must grant)
 * - OR: Union of rights (either formula grants)
 * - NOT: Complement of rights (invert all bits)
 * - XOR: Symmetric difference (exactly one formula grants)
 */
typedef enum {
    FORMULA_COMBINATOR_AND,  /* Intersection: rights1 & rights2 */
    FORMULA_COMBINATOR_OR,   /* Union: rights1 | rights2 */
    FORMULA_COMBINATOR_NOT,  /* Complement: ~rights */
    FORMULA_COMBINATOR_XOR,  /* Symmetric difference: rights1 ^ rights2 */
} formula_combinator_t;

/*******************************************************************************
 * FORMULA DATA STRUCTURES
 ******************************************************************************/

/**
 * Time-based formula data
 *
 * Grants rights only before expiry timestamp.
 *
 * USE CASE: Temporary access grants, time-limited delegation
 * REAL-WORLD: OAuth access tokens with expiry, Kerberos tickets
 */
typedef struct {
    uint64_t expiry_time;     /* Timestamp when rights expire */
    uint32_t base_rights;     /* Rights to grant before expiry */
    uint32_t expired_rights;  /* Rights to grant after expiry (usually 0) */
} time_based_formula_data_t;

/**
 * Usage-based formula data
 *
 * Grants rights for first N accesses, then revokes.
 *
 * USE CASE: Metered access, quota enforcement, rate limiting
 * REAL-WORLD: AWS free tier (first N requests free), trial licenses
 */
typedef struct {
    uint64_t max_accesses;    /* Maximum number of accesses allowed */
    uint32_t base_rights;     /* Rights to grant before quota exceeded */
    uint32_t quota_exceeded_rights; /* Rights after quota (usually 0) */
} usage_based_formula_data_t;

/**
 * User-based formula data
 *
 * Grants different rights based on calling user/process.
 *
 * USE CASE: Multi-user systems, role-based access control (RBAC)
 * REAL-WORLD: Unix file permissions (owner vs. group vs. other),
 *             SELinux user-based policies
 */
#define MAX_USER_POLICIES 8

typedef struct {
    uint32_t user_pids[MAX_USER_POLICIES];   /* PIDs to match */
    uint32_t user_rights[MAX_USER_POLICIES]; /* Rights per user */
    uint32_t default_rights;                 /* Rights for unlisted users */
    uint32_t num_policies;                   /* Number of user policies */
} user_based_formula_data_t;

/**
 * Quota-based formula data
 *
 * Grants rights while resource consumption is below quota.
 *
 * USE CASE: Resource accounting, fair scheduling
 * REAL-WORLD: Cgroups memory limits, disk quotas
 *
 * PDAC INTEGRATION:
 * Uses 8D resource vectors to track consumption across all dimensions.
 */
typedef struct {
    resource_vector_t max_quota;  /* Maximum allowed consumption */
    uint32_t base_rights;         /* Rights when under quota */
    uint32_t quota_exceeded_rights; /* Rights when quota exceeded */
} quota_based_formula_data_t;

/**
 * Combinator formula data
 *
 * Composes two child formulas using Boolean combinator (AND/OR/NOT/XOR).
 *
 * USE CASE: Complex policies (e.g., "grant READ if (time valid) AND (user authorized)")
 * REAL-WORLD: AWS IAM policy composition, SELinux boolean expressions
 *
 * HIGHER-ORDER FUNCTION:
 * This is a higher-order formula: a formula that operates on other formulas.
 * In lambda calculus: λ(f1, f2, op). λ(cap). op(f1(cap), f2(cap))
 */
typedef struct {
    cap_formula_legacy_t formula1;    /* First child formula */
    void *data1;                      /* Data for first formula */
    cap_formula_legacy_t formula2;    /* Second child formula (NULL for NOT) */
    void *data2;                      /* Data for second formula */
    formula_combinator_t combinator;  /* Combinator type (AND/OR/NOT/XOR) */
} combinator_formula_data_t;

/*******************************************************************************
 * STANDARD FORMULAS (Implemented in kernel/cap_formula.c)
 ******************************************************************************/

/**
 * Time-based formula: Grant rights before expiry
 *
 * @param cap Capability being evaluated
 * @param data Pointer to time_based_formula_data_t
 * @return base_rights if before expiry, expired_rights otherwise
 *
 * ALGORITHM:
 * 1. Get current timestamp from system timer
 * 2. Compare with expiry_time
 * 3. Return base_rights if before, expired_rights if after
 *
 * EXAMPLE:
 * ```c
 * time_based_formula_data_t *data = malloc(...);
 * data->expiry_time = current_time() + 3600; // Expire in 1 hour
 * data->base_rights = CAP_RIGHT_READ | CAP_RIGHT_WRITE;
 * data->expired_rights = 0; // No rights after expiry
 *
 * capv2_set_formula(slot, formula_time_based, data);
 * ```
 */
uint32_t formula_time_based(const struct capability_v2 *cap, void *data);

/**
 * Usage-based formula: Grant rights for first N accesses
 *
 * @param cap Capability being evaluated (uses cap->access_count)
 * @param data Pointer to usage_based_formula_data_t
 * @return base_rights if under quota, quota_exceeded_rights otherwise
 *
 * ALGORITHM:
 * 1. Read cap->access_count (incremented by capv2_check_rights)
 * 2. Compare with max_accesses
 * 3. Return base_rights if under, quota_exceeded_rights if over
 *
 * EXAMPLE:
 * ```c
 * usage_based_formula_data_t *data = malloc(...);
 * data->max_accesses = 100; // Allow 100 accesses
 * data->base_rights = CAP_RIGHT_READ;
 * data->quota_exceeded_rights = 0; // Revoke after 100 accesses
 *
 * capv2_set_formula(slot, formula_usage_based, data);
 * ```
 */
uint32_t formula_usage_based(const struct capability_v2 *cap, void *data);

/**
 * User-based formula: Grant rights based on calling process
 *
 * @param cap Capability being evaluated
 * @param data Pointer to user_based_formula_data_t
 * @return Rights for current user, or default_rights if not in list
 *
 * ALGORITHM:
 * 1. Get current PID from process manager
 * 2. Search user_pids array for match
 * 3. Return corresponding user_rights, or default_rights if no match
 *
 * EXAMPLE:
 * ```c
 * user_based_formula_data_t *data = malloc(...);
 * data->user_pids[0] = 42;  // Root process
 * data->user_rights[0] = CAP_RIGHT_READ | CAP_RIGHT_WRITE;
 * data->user_pids[1] = 100; // Guest process
 * data->user_rights[1] = CAP_RIGHT_READ; // Read-only
 * data->num_policies = 2;
 * data->default_rights = 0; // No access for others
 *
 * capv2_set_formula(slot, formula_user_based, data);
 * ```
 */
uint32_t formula_user_based(const struct capability_v2 *cap, void *data);

/**
 * Quota-based formula: Grant rights while under resource quota
 *
 * @param cap Capability being evaluated (uses cap->consumed)
 * @param data Pointer to quota_based_formula_data_t
 * @return base_rights if under quota, quota_exceeded_rights otherwise
 *
 * ALGORITHM:
 * 1. Compare cap->consumed with max_quota (8D component-wise)
 * 2. If any dimension exceeds quota, return quota_exceeded_rights
 * 3. Otherwise return base_rights
 *
 * PDAC INNOVATION:
 * Uses 8D resource vectors for multi-dimensional quota enforcement.
 * Can limit CPU, memory, I/O, network, GPU, disk, IRQ, capabilities.
 *
 * EXAMPLE:
 * ```c
 * quota_based_formula_data_t *data = malloc(...);
 * data->max_quota.memory = Q16(1024); // 1 MB memory quota
 * data->max_quota.cpu = Q16(0.5);     // 50% CPU quota
 * data->base_rights = CAP_RIGHT_READ | CAP_RIGHT_WRITE;
 * data->quota_exceeded_rights = CAP_RIGHT_READ; // Read-only after quota
 *
 * capv2_set_formula(slot, formula_quota_based, data);
 * ```
 */
uint32_t formula_quota_based(const struct capability_v2 *cap, void *data);

/**
 * Combinator formula: Compose two formulas with Boolean operator
 *
 * @param cap Capability being evaluated
 * @param data Pointer to combinator_formula_data_t
 * @return Combined rights based on combinator type
 *
 * ALGORITHM:
 * 1. Evaluate formula1(cap, data1) -> rights1
 * 2. Evaluate formula2(cap, data2) -> rights2 (skip for NOT)
 * 3. Apply combinator:
 *    - AND: rights1 & rights2
 *    - OR:  rights1 | rights2
 *    - NOT: ~rights1
 *    - XOR: rights1 ^ rights2
 *
 * HIGHER-ORDER PROGRAMMING:
 * This is a higher-order function: it takes functions as arguments
 * and composes them. Enables building complex policies from simple ones.
 *
 * EXAMPLE:
 * ```c
 * // Policy: "Grant READ|WRITE if (time valid) AND (user authorized)"
 *
 * time_based_formula_data_t *time_data = malloc(...);
 * time_data->expiry_time = ...;
 * time_data->base_rights = 0xFFFFFFFF; // All rights
 *
 * user_based_formula_data_t *user_data = malloc(...);
 * user_data->user_pids[0] = 42;
 * user_data->user_rights[0] = CAP_RIGHT_READ | CAP_RIGHT_WRITE;
 *
 * combinator_formula_data_t *comb_data = malloc(...);
 * comb_data->formula1 = formula_time_based;
 * comb_data->data1 = time_data;
 * comb_data->formula2 = formula_user_based;
 * comb_data->data2 = user_data;
 * comb_data->combinator = FORMULA_COMBINATOR_AND;
 *
 * capv2_set_formula(slot, formula_combinator, comb_data);
 * ```
 */
uint32_t formula_combinator(const struct capability_v2 *cap, void *data);

/**
 * Static formula: Always return fixed rights (for testing)
 *
 * @param cap Capability being evaluated (unused)
 * @param data Pointer to uint32_t containing static rights
 * @return Static rights value
 *
 * USE CASE: Testing, debugging, simple policies
 */
uint32_t formula_static(const struct capability_v2 *cap, void *data);

/*******************************************************************************
 * FORMULA COMPOSITION API
 ******************************************************************************/

/**
 * Create a combinator formula (higher-order function)
 *
 * @param f1 First formula
 * @param d1 Data for first formula
 * @param f2 Second formula (NULL for NOT)
 * @param d2 Data for second formula
 * @param combinator Combinator type (AND/OR/NOT/XOR)
 * @return Combinator data structure (caller must free)
 *
 * USAGE:
 * ```c
 * combinator_formula_data_t *and_formula =
 *     create_combinator(formula_time_based, time_data,
 *                       formula_user_based, user_data,
 *                       FORMULA_COMBINATOR_AND);
 *
 * capv2_set_formula(slot, formula_combinator, and_formula);
 * ```
 */
combinator_formula_data_t *create_combinator(
    cap_formula_t f1, void *d1,
    cap_formula_t f2, void *d2,
    formula_combinator_t combinator);

/**
 * Free combinator formula data (recursive)
 *
 * @param comb_data Combinator data to free
 *
 * NOTE: This does NOT free child data (data1, data2). Caller must manage
 * child data separately to avoid double-free.
 */
void free_combinator(combinator_formula_data_t *comb_data);

/*******************************************************************************
 * FORMULA HELPERS
 ******************************************************************************/

/**
 * Get current timestamp (milliseconds since boot)
 *
 * @return Current time in milliseconds
 *
 * TODO: Implement using platform timer (TSC, HPET, etc.)
 */
uint64_t formula_get_time(void);

/**
 * Get current process ID
 *
 * @return PID of calling process
 *
 * TODO: Implement using process manager API
 */
uint32_t formula_get_pid(void);

/*******************************************************************************
 * FORMULA EXAMPLES (Pedagogical demonstrations)
 ******************************************************************************/

/**
 * Example: Time-limited read-only access
 *
 * Creates a capability that grants READ for 1 hour, then expires.
 *
 * DEMONSTRATES: Time-based formulas, temporary delegation
 */
void example_time_limited_access(void);

/**
 * Example: Metered access (100 reads, then revoke)
 *
 * Creates a capability that allows 100 reads, then becomes invalid.
 *
 * DEMONSTRATES: Usage-based formulas, quota enforcement
 */
void example_metered_access(void);

/**
 * Example: Role-based access control (RBAC)
 *
 * Creates a capability with different rights for admin vs. guest users.
 *
 * DEMONSTRATES: User-based formulas, multi-user systems
 */
void example_rbac(void);

/**
 * Example: Complex policy composition
 *
 * Creates a capability with policy: "(time valid) AND ((user == admin) OR (usage < 10))"
 *
 * DEMONSTRATES: Combinator formulas, higher-order composition
 */
void example_complex_policy(void);

/**
 * Example: Resource quota enforcement
 *
 * Creates a capability that grants full access until memory quota exceeded,
 * then switches to read-only.
 *
 * DEMONSTRATES: Quota-based formulas, 8D resource vectors
 */
void example_quota_enforcement(void);

#endif /* CAP_FORMULA_H */
