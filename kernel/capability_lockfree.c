/**
 * @file capability_lockfree.c
 * @brief Lock-Free Capability System Implementation (Task 5.5.1)
 *
 * High-performance lock-free capability table with:
 * - Hash table with CAS-based insertion
 * - Hazard pointers for safe memory reclamation
 * - RCU for read-side performance
 * - Atomic permission operations
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "capability_lockfree.h"

/*******************************************************************************
 * INTERNAL HELPERS
 ******************************************************************************/

/**
 * @brief Allocate capability node
 */
static capability_node_t *cap_node_alloc(cap_id_t id, uint64_t permissions,
                                        uint32_t owner_pid)
{
    capability_node_t *node = calloc(1, sizeof(capability_node_t));
    if (!node) return NULL;

    node->cap.id = id;
    atomic_store(&node->cap.permissions, permissions);
    atomic_store(&node->cap.state, CAP_STATE_ACTIVE);
    atomic_store(&node->cap.ref_count, 0);
    atomic_store(&node->cap.parent, NULL);
    atomic_store(&node->cap.children, NULL);
    atomic_store(&node->cap.sibling, NULL);
    atomic_store(&node->cap.gas_balance, 1000000);  /* Initial gas */
    atomic_store(&node->cap.access_count, 0);
    node->cap.create_time = (uint64_t)time(NULL);
    node->cap.owner_pid = owner_pid;
    atomic_store(&node->next, NULL);

    return node;
}

/**
 * @brief Free capability node (RCU callback)
 */
static void cap_node_free_rcu(rcu_head_t *head, uint8_t cpu_id)
{
    (void)cpu_id;
    capability_node_t *node = container_of(head, capability_node_t, cap.rcu_head);
    free(node);
}

/*******************************************************************************
 * TABLE MANAGEMENT
 ******************************************************************************/

int capability_table_init(capability_table_t *table, uint8_t num_cpus)
{
    if (!table || num_cpus == 0) return -1;

    /* Initialize buckets */
    for (uint32_t i = 0; i < CAPABILITY_TABLE_SIZE; i++) {
        atomic_store(&table->buckets[i], NULL);
    }

    /* Initialize hazard pointer domain */
    hp_domain_init(&table->hp, num_cpus);

    /* Initialize RCU */
    rcu_init(&table->rcu, num_cpus);

    /* Initialize statistics */
    atomic_store(&table->version, 0);
    atomic_store(&table->num_capabilities, 0);
    atomic_store(&table->num_lookups, 0);
    atomic_store(&table->num_inserts, 0);
    atomic_store(&table->num_revokes, 0);

    table->num_cpus = num_cpus;

    return 0;
}

void capability_table_destroy(capability_table_t *table)
{
    if (!table) return;

    /* Free all capability nodes */
    for (uint32_t i = 0; i < CAPABILITY_TABLE_SIZE; i++) {
        capability_node_t *node = atomic_load(&table->buckets[i]);
        while (node) {
            capability_node_t *next = atomic_load(&node->next);
            free(node);
            node = next;
        }
    }

    /* Cleanup hazard pointers and RCU */
    hp_domain_destroy(&table->hp);
    rcu_destroy(&table->rcu);
}

/*******************************************************************************
 * CAPABILITY OPERATIONS
 ******************************************************************************/

int capability_create(capability_table_t *table, cap_id_t id,
                     uint64_t permissions, uint32_t owner_pid)
{
    if (!table) return -1;

    uint32_t hash = capability_hash(id);

    /* Allocate new node */
    capability_node_t *new_node = cap_node_alloc(id, permissions, owner_pid);
    if (!new_node) return -1;

    /* CAS loop to insert at head of chain */
    while (1) {
        capability_node_t *old_head = atomic_load(&table->buckets[hash]);

        /* Check for duplicate ID (traverse chain) */
        capability_node_t *curr = old_head;
        while (curr) {
            if (curr->cap.id == id) {
                /* Duplicate ID */
                free(new_node);
                return -2;
            }
            curr = atomic_load(&curr->next);
        }

        /* Link new node */
        atomic_store(&new_node->next, old_head);

        /* Try to CAS */
        if (atomic_compare_exchange_strong(&table->buckets[hash],
                                          &old_head, new_node)) {
            /* Success */
            atomic_fetch_add(&table->num_capabilities, 1);
            atomic_fetch_add(&table->num_inserts, 1);
            atomic_fetch_add(&table->version, 1);
            return 0;
        }

        /* CAS failed, retry */
    }
}

capability_t *capability_lookup(capability_table_t *table, cap_id_t id,
                               uint8_t cpu_id)
{
    if (!table) return NULL;

    uint32_t hash = capability_hash(id);

    atomic_fetch_add(&table->num_lookups, 1);

    /* Hazard pointer protection */
    capability_node_t *node = hp_protect(&table->hp, cpu_id, 0,
                                        (void **)&table->buckets[hash]);

    /* Traverse chain */
    while (node) {
        if (node->cap.id == id) {
            /* Found it */
            cap_state_t state = atomic_load(&node->cap.state);
            if (state == CAP_STATE_ACTIVE) {
                atomic_fetch_add(&node->cap.ref_count, 1);
                atomic_fetch_add(&node->cap.access_count, 1);
                return &node->cap;
            }
            /* Found but not active */
            hp_clear(&table->hp, cpu_id, 0);
            return NULL;
        }

        /* Move to next (with hazard pointer protection) */
        node = hp_protect(&table->hp, cpu_id, 0, (void **)&node->next);
    }

    /* Not found */
    hp_clear(&table->hp, cpu_id, 0);
    return NULL;
}

void capability_release(capability_table_t *table, capability_t *cap,
                       uint8_t cpu_id)
{
    if (!table || !cap) return;

    atomic_fetch_sub(&cap->ref_count, 1);
    hp_clear(&table->hp, cpu_id, 0);
}

int capability_revoke(capability_table_t *table, cap_id_t id, uint8_t cpu_id)
{
    if (!table) return -1;

    /* Lookup capability */
    capability_t *cap = capability_lookup(table, id, cpu_id);
    if (!cap) return -2;  /* Not found */

    /* Mark as revoked (atomic) */
    cap_state_t expected = CAP_STATE_ACTIVE;
    if (!atomic_compare_exchange_strong(&cap->state, &expected,
                                       CAP_STATE_REVOKED)) {
        /* Already revoked or deleted */
        capability_release(table, cap, cpu_id);
        return -3;
    }

    /* Clear all permissions */
    atomic_store(&cap->permissions, 0);

    /* Revoke all children (recursive) */
    rcu_read_lock(&table->rcu, cpu_id);
    capability_t *child = atomic_load(&cap->children);
    while (child) {
        capability_revoke(table, child->id, cpu_id);
        child = atomic_load(&child->sibling);
    }
    rcu_read_unlock(&table->rcu, cpu_id);

    atomic_fetch_add(&table->num_revokes, 1);
    capability_release(table, cap, cpu_id);
    return 0;
}

int capability_delete(capability_table_t *table, cap_id_t id, uint8_t cpu_id)
{
    if (!table) return -1;

    uint32_t hash = capability_hash(id);

    rcu_read_lock(&table->rcu, cpu_id);

    /* Find node in chain */
    capability_node_t **prev_ptr = (capability_node_t **)&table->buckets[hash];
    capability_node_t *prev = NULL;
    capability_node_t *curr = atomic_load(&table->buckets[hash]);

    while (curr) {
        if (curr->cap.id == id) {
            /* Found it - mark as deleted */
            cap_state_t state = atomic_load(&curr->cap.state);
            if (state != CAP_STATE_REVOKED) {
                rcu_read_unlock(&table->rcu, cpu_id);
                return -2;  /* Must revoke before delete */
            }

            atomic_store(&curr->cap.state, CAP_STATE_DELETED);

            /* Unlink from chain (CAS) */
            capability_node_t *next = atomic_load(&curr->next);
            if (prev) {
                if (atomic_compare_exchange_strong(&prev->next, &curr, next)) {
                    /* Success - defer free via RCU */
                    call_rcu(&table->rcu, &curr->cap.rcu_head,
                            cap_node_free_rcu, cpu_id);
                    atomic_fetch_sub(&table->num_capabilities, 1);
                    rcu_read_unlock(&table->rcu, cpu_id);
                    return 0;
                }
            } else {
                if (atomic_compare_exchange_strong(prev_ptr, &curr, next)) {
                    /* Success - defer free via RCU */
                    call_rcu(&table->rcu, &curr->cap.rcu_head,
                            cap_node_free_rcu, cpu_id);
                    atomic_fetch_sub(&table->num_capabilities, 1);
                    rcu_read_unlock(&table->rcu, cpu_id);
                    return 0;
                }
            }

            /* CAS failed */
            rcu_read_unlock(&table->rcu, cpu_id);
            return -3;
        }

        prev = curr;
        prev_ptr = (capability_node_t **)&curr->next;
        curr = atomic_load(&curr->next);
    }

    rcu_read_unlock(&table->rcu, cpu_id);
    return -4;  /* Not found */
}

/*******************************************************************************
 * DELEGATION
 ******************************************************************************/

int capability_delegate(capability_table_t *table, cap_id_t parent_id,
                       cap_id_t child_id, uint64_t child_perms,
                       uint32_t owner_pid, uint8_t cpu_id)
{
    if (!table) return -1;

    /* Lookup parent */
    capability_t *parent = capability_lookup(table, parent_id, cpu_id);
    if (!parent) return -2;  /* Parent not found */

    /* Check parent has delegation permission */
    if (!capability_has_permission(parent, CAP_PERM_DELEGATE)) {
        capability_release(table, parent, cpu_id);
        return -3;  /* No delegation permission */
    }

    /* Check child permissions are subset of parent */
    uint64_t parent_perms = atomic_load(&parent->permissions);
    if ((child_perms & ~parent_perms) != 0) {
        capability_release(table, parent, cpu_id);
        return -4;  /* Child has permissions parent doesn't have */
    }

    /* Create child capability */
    int ret = capability_create(table, child_id, child_perms, owner_pid);
    if (ret < 0) {
        capability_release(table, parent, cpu_id);
        return ret;
    }

    /* Lookup newly created child */
    capability_t *child = capability_lookup(table, child_id, cpu_id);
    if (!child) {
        capability_release(table, parent, cpu_id);
        return -5;  /* Child creation failed */
    }

    /* Link parent-child relationship (RCU-protected) */
    rcu_read_lock(&table->rcu, cpu_id);

    atomic_store(&child->parent, parent);

    /* Add child to parent's children list */
    capability_t *old_children = atomic_load(&parent->children);
    atomic_store(&child->sibling, old_children);
    atomic_store(&parent->children, child);

    rcu_read_unlock(&table->rcu, cpu_id);

    capability_release(table, child, cpu_id);
    capability_release(table, parent, cpu_id);
    return 0;
}

bool capability_dominates(capability_t *cap1, capability_t *cap2,
                         rcu_state_t *rcu, uint8_t cpu_id)
{
    if (!cap1 || !cap2) return false;

    rcu_read_lock(rcu, cpu_id);

    /* Walk up cap2's parent chain */
    capability_t *curr = cap2;
    while (curr) {
        if (curr->id == cap1->id) {
            rcu_read_unlock(rcu, cpu_id);
            return true;  /* cap1 is ancestor of cap2 */
        }
        curr = atomic_load(&curr->parent);
    }

    rcu_read_unlock(rcu, cpu_id);
    return false;
}

/*******************************************************************************
 * STATISTICS
 ******************************************************************************/

void capability_get_stats(const capability_table_t *table,
                         capability_stats_t *stats)
{
    if (!table || !stats) return;

    stats->num_capabilities = atomic_load(&table->num_capabilities);
    stats->num_lookups = atomic_load(&table->num_lookups);
    stats->num_inserts = atomic_load(&table->num_inserts);
    stats->num_revokes = atomic_load(&table->num_revokes);
    stats->version = atomic_load(&table->version);
}

/*******************************************************************************
 * UTILITIES
 ******************************************************************************/

void capability_print(const capability_t *cap)
{
    if (!cap) return;

    printf("Capability ID: %u\n", cap->id);
    printf("  Permissions: 0x%016lx\n",
           atomic_load(((_Atomic uint64_t *)&cap->permissions)));
    printf("  State: %d\n", atomic_load(((_Atomic cap_state_t *)&cap->state)));
    printf("  Ref Count: %lu\n",
           atomic_load(((_Atomic uint64_t *)&cap->ref_count)));
    printf("  Access Count: %lu\n",
           atomic_load(((_Atomic uint64_t *)&cap->access_count)));
    printf("  Gas Balance: %lu\n",
           atomic_load(((_Atomic uint64_t *)&cap->gas_balance)));
    printf("  Owner PID: %u\n", cap->owner_pid);
    printf("  Create Time: %lu\n", cap->create_time);
}

void capability_table_print_stats(const capability_table_t *table)
{
    if (!table) return;

    capability_stats_t stats;
    capability_get_stats(table, &stats);

    printf("Capability Table Statistics:\n");
    printf("  Total Capabilities: %lu\n", stats.num_capabilities);
    printf("  Lookups: %lu\n", stats.num_lookups);
    printf("  Inserts: %lu\n", stats.num_inserts);
    printf("  Revokes: %lu\n", stats.num_revokes);
    printf("  Version: %lu\n", stats.version);

    /* Calculate load factor */
    double load_factor = (double)stats.num_capabilities / CAPABILITY_TABLE_SIZE;
    printf("  Load Factor: %.2f\n", load_factor);
}
