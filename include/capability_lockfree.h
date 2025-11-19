/**
 * @file capability_lockfree.h
 * @brief Lock-Free Capability System (Task 5.5.1)
 *
 * High-performance, lock-free capability table using:
 * - Hash table with lock-free chaining
 * - Hazard pointers for memory safety
 * - RCU for read-side performance
 * - Atomic permission operations
 *
 * Expected Benefits:
 * - 10-100x faster permission checks
 * - Zero lock contention
 * - Lock-free lookup/insert/revoke
 * - Safe concurrent delegation
 */

#pragma once

#include <stdint.h>
#include <stdatomic.h>
#include <stdbool.h>
#include "hazard_pointer.h"
#include "rcu_pdac.h"

#ifdef __cplusplus
extern "C" {
#endif

/*******************************************************************************
 * CONFIGURATION
 ******************************************************************************/

#define CAPABILITY_TABLE_SIZE     256    /**< Hash table size (power of 2) */
#define CAPABILITY_TABLE_MASK     (CAPABILITY_TABLE_SIZE - 1)
#define MAX_CAPABILITY_ID         UINT32_MAX

/*******************************************************************************
 * CAPABILITY TYPES
 ******************************************************************************/

/** Capability identifier (unique per capability) */
typedef uint32_t cap_id_t;

/** Capability state (atomic) */
typedef enum {
    CAP_STATE_INVALID = 0,     /**< Uninitialized */
    CAP_STATE_ACTIVE = 1,      /**< Active and usable */
    CAP_STATE_REVOKED = 2,     /**< Revoked, pending cleanup */
    CAP_STATE_DELETED = 3      /**< Deleted, in grace period */
} cap_state_t;

/** Permission bits (64-bit mask) */
typedef enum {
    CAP_PERM_NONE        = 0x0000000000000000ULL,
    CAP_PERM_READ        = 0x0000000000000001ULL,
    CAP_PERM_WRITE       = 0x0000000000000002ULL,
    CAP_PERM_EXECUTE     = 0x0000000000000004ULL,
    CAP_PERM_DELETE      = 0x0000000000000008ULL,
    CAP_PERM_DELEGATE    = 0x0000000000000010ULL,
    CAP_PERM_REVOKE      = 0x0000000000000020ULL,
    CAP_PERM_TRANSFER    = 0x0000000000000040ULL,
    CAP_PERM_UPGRADE     = 0x0000000000000080ULL,
    CAP_PERM_ALL         = 0xFFFFFFFFFFFFFFFFULL
} cap_perm_t;

/*******************************************************************************
 * CORE DATA STRUCTURES
 ******************************************************************************/

/**
 * @brief Lock-free capability structure
 *
 * All fields are either atomic or RCU-protected for lock-free access.
 */
typedef struct capability {
    cap_id_t id;                          /**< Unique identifier */

    /* Atomic fields (lock-free access) */
    _Atomic uint64_t permissions;         /**< Permission bitmask */
    _Atomic cap_state_t state;            /**< Current state */
    _Atomic uint64_t ref_count;           /**< Reference count */

    /* RCU-protected fields */
    _Atomic(struct capability *) parent;  /**< Parent capability (delegation) */
    _Atomic(struct capability *) children;/**< First child (delegation) */
    _Atomic(struct capability *) sibling; /**< Next sibling */

    /* Resource accounting (atomic) */
    _Atomic uint64_t gas_balance;         /**< Gas for DoS prevention */
    _Atomic uint64_t access_count;        /**< Usage statistics */

    /* Metadata */
    uint64_t create_time;                 /**< Creation timestamp */
    uint32_t owner_pid;                   /**< Owning process */

    /* RCU reclamation */
    rcu_head_t rcu_head;                  /**< RCU callback */
} capability_t;

/**
 * @brief Capability hash table node (lock-free chaining)
 */
typedef struct capability_node {
    capability_t cap;                     /**< Capability data */
    _Atomic(struct capability_node *) next; /**< Next in chain */
} capability_node_t;

/**
 * @brief Lock-free capability table
 *
 * Uses:
 * - Lock-free hash table with chaining
 * - Hazard pointers for ABA safety
 * - RCU for read-side performance
 */
typedef struct capability_table {
    /* Hash table buckets (lock-free) */
    _Atomic(capability_node_t *) buckets[CAPABILITY_TABLE_SIZE];

    /* Hazard pointer domain */
    hp_domain_t hp;

    /* RCU state */
    rcu_state_t rcu;

    /* Statistics (atomic) */
    _Atomic uint64_t version;             /**< Version counter */
    _Atomic uint64_t num_capabilities;    /**< Total capabilities */
    _Atomic uint64_t num_lookups;         /**< Lookup count */
    _Atomic uint64_t num_inserts;         /**< Insert count */
    _Atomic uint64_t num_revokes;         /**< Revoke count */

    /* Configuration */
    uint8_t num_cpus;                     /**< Number of CPUs */
} capability_table_t;

/*******************************************************************************
 * TABLE MANAGEMENT
 ******************************************************************************/

/**
 * @brief Initialize capability table
 *
 * @param table     Capability table to initialize
 * @param num_cpus  Number of CPUs (for RCU/HP)
 * @return 0 on success, negative on error
 */
int capability_table_init(capability_table_t *table, uint8_t num_cpus);

/**
 * @brief Destroy capability table
 *
 * WARNING: All capabilities must be revoked before destroying table.
 *
 * @param table  Capability table to destroy
 */
void capability_table_destroy(capability_table_t *table);

/*******************************************************************************
 * CAPABILITY OPERATIONS (LOCK-FREE)
 ******************************************************************************/

/**
 * @brief Create new capability
 *
 * @param table       Capability table
 * @param id          Capability ID (must be unique)
 * @param permissions Initial permissions
 * @param owner_pid   Owning process ID
 * @return 0 on success, negative on error
 *
 * Performance: O(1) lock-free with CAS retry loop
 */
int capability_create(capability_table_t *table, cap_id_t id,
                     uint64_t permissions, uint32_t owner_pid);

/**
 * @brief Lookup capability by ID (lock-free)
 *
 * Returns pointer to capability (valid until release).
 * Caller must call capability_release() when done.
 *
 * @param table  Capability table
 * @param id     Capability ID to find
 * @param cpu_id Current CPU (for hazard pointers)
 * @return Pointer to capability, or NULL if not found
 *
 * Performance: O(1) average, lock-free with hazard pointers
 */
capability_t *capability_lookup(capability_table_t *table, cap_id_t id,
                               uint8_t cpu_id);

/**
 * @brief Release capability reference
 *
 * Must be called after capability_lookup() when done.
 *
 * @param table  Capability table
 * @param cap    Capability to release
 * @param cpu_id Current CPU (for hazard pointers)
 */
void capability_release(capability_table_t *table, capability_t *cap,
                       uint8_t cpu_id);

/**
 * @brief Revoke capability (lock-free)
 *
 * Marks capability as revoked and defers deletion until grace period.
 *
 * @param table  Capability table
 * @param id     Capability ID to revoke
 * @param cpu_id Current CPU (for RCU)
 * @return 0 on success, negative if not found
 *
 * Performance: O(1) average, lock-free
 */
int capability_revoke(capability_table_t *table, cap_id_t id, uint8_t cpu_id);

/**
 * @brief Delete capability (physical removal)
 *
 * Removes capability from hash table. Uses RCU for safe deferred deletion.
 *
 * @param table  Capability table
 * @param id     Capability ID to delete
 * @param cpu_id Current CPU (for RCU)
 * @return 0 on success, negative if not found
 *
 * Performance: O(n) where n = chain length, lock-free
 */
int capability_delete(capability_table_t *table, cap_id_t id, uint8_t cpu_id);

/*******************************************************************************
 * PERMISSION OPERATIONS (ATOMIC)
 ******************************************************************************/

/**
 * @brief Check if capability has permission (atomic read)
 *
 * @param cap  Capability to check
 * @param perm Permission bits to test
 * @return true if has permission and active, false otherwise
 *
 * Performance: ~1-5ns (single atomic load)
 */
static inline bool capability_has_permission(capability_t *cap, uint64_t perm)
{
    /* Check state first (fast rejection) */
    cap_state_t state = atomic_load_explicit(&cap->state, memory_order_acquire);
    if (state != CAP_STATE_ACTIVE) {
        return false;
    }

    /* Check permissions (atomic load) */
    uint64_t perms = atomic_load_explicit(&cap->permissions, memory_order_acquire);
    return (perms & perm) == perm;
}

/**
 * @brief Grant permissions (atomic OR)
 *
 * @param cap  Capability to modify
 * @param perm Permissions to grant
 *
 * Performance: ~5-10ns (atomic fetch_or)
 */
static inline void capability_grant(capability_t *cap, uint64_t perm)
{
    atomic_fetch_or_explicit(&cap->permissions, perm, memory_order_acq_rel);
}

/**
 * @brief Revoke permissions (atomic AND-NOT)
 *
 * @param cap  Capability to modify
 * @param perm Permissions to revoke
 *
 * Performance: ~5-10ns (atomic fetch_and)
 */
static inline void capability_revoke_permission(capability_t *cap, uint64_t perm)
{
    atomic_fetch_and_explicit(&cap->permissions, ~perm, memory_order_acq_rel);
}

/**
 * @brief Get all permissions (atomic read)
 *
 * @param cap  Capability to read
 * @return Permission bitmask
 */
static inline uint64_t capability_get_permissions(capability_t *cap)
{
    return atomic_load_explicit(&cap->permissions, memory_order_acquire);
}

/*******************************************************************************
 * DELEGATION (RCU-PROTECTED)
 ******************************************************************************/

/**
 * @brief Delegate capability (create child with subset of permissions)
 *
 * Child capability inherits subset of parent permissions.
 * Uses RCU to maintain parent/child relationships.
 *
 * @param table       Capability table
 * @param parent_id   Parent capability ID
 * @param child_id    New child capability ID
 * @param child_perms Permissions for child (must be subset of parent)
 * @param owner_pid   Owner of child capability
 * @param cpu_id      Current CPU
 * @return 0 on success, negative on error
 *
 * Performance: O(1) average, lock-free
 */
int capability_delegate(capability_table_t *table, cap_id_t parent_id,
                       cap_id_t child_id, uint64_t child_perms,
                       uint32_t owner_pid, uint8_t cpu_id);

/**
 * @brief Check if cap1 dominates cap2 (transitive delegation check)
 *
 * Returns true if cap1 is ancestor of cap2 in delegation tree.
 * Uses RCU for safe traversal.
 *
 * @param cap1   Potential ancestor
 * @param cap2   Potential descendant
 * @param rcu    RCU state
 * @param cpu_id Current CPU
 * @return true if cap1 dominates cap2
 *
 * Performance: O(depth) where depth = delegation depth
 */
bool capability_dominates(capability_t *cap1, capability_t *cap2,
                         rcu_state_t *rcu, uint8_t cpu_id);

/*******************************************************************************
 * STATISTICS
 ******************************************************************************/

/**
 * @brief Get capability table statistics
 */
typedef struct {
    uint64_t num_capabilities;    /**< Total capabilities */
    uint64_t num_lookups;         /**< Lookup operations */
    uint64_t num_inserts;         /**< Insert operations */
    uint64_t num_revokes;         /**< Revoke operations */
    uint64_t version;             /**< Table version */
} capability_stats_t;

/**
 * @brief Get statistics (atomic reads)
 *
 * @param table  Capability table
 * @param stats  Output statistics
 */
void capability_get_stats(const capability_table_t *table,
                         capability_stats_t *stats);

/*******************************************************************************
 * UTILITIES
 ******************************************************************************/

/**
 * @brief Hash capability ID
 *
 * Simple hash function for capability IDs.
 *
 * @param id  Capability ID
 * @return Hash value (0 to CAPABILITY_TABLE_SIZE-1)
 */
static inline uint32_t capability_hash(cap_id_t id)
{
    /* Simple multiplicative hash */
    return (id * 2654435761U) & CAPABILITY_TABLE_MASK;
}

/**
 * @brief Print capability info (debugging)
 *
 * @param cap  Capability to print
 */
void capability_print(const capability_t *cap);

/**
 * @brief Print table statistics (debugging)
 *
 * @param table  Capability table
 */
void capability_table_print_stats(const capability_table_t *table);

#ifdef __cplusplus
}
#endif
