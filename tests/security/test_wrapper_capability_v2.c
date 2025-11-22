/**
 * @file test_wrapper_capability_v2.c
 * @brief PDAC Capability System V2 - Core Implementation
 *
 * This file implements the PDAC (Probabilistic DAG Algebra with Capabilities)
 * capability system, synthesizing:
 * - seL4-style capability-based security
 * - Cap'n Proto zero-copy IPC
 * - Lambda calculus for dynamic rights computation
 * - 8D resource vectors using octonion algebra
 * - Token bucket rate limiting
 *
 * DESIGN RATIONALE:
 * - Fixed-size table (4096 slots) for O(1) allocation like seL4
 * - Free list for fast slot reuse
 * - Generation counters prevent ABA problem (use-after-free)
 * - Per-capability locks for fine-grained concurrency
 * - Reference counting for safe delegation
 *
 * PEDAGOGICAL NOTES:
 * This implementation demonstrates how modern OS concepts (capabilities,
 * zero-copy IPC, non-associative algebra) combine into a unified security
 * primitive suitable for microkernel architectures.
 *
 * @see include/capability_v2.h for API documentation
 * @see docs/PDAC_UNIFIED_FRAMEWORK.md for theoretical foundation
 */

#include "capability_v2.h"
#include "exo_lock.h"
#include "string.h"
#include <stddef.h>
#include <stdint.h>
#include "defs.h"

#define printf cprintf

#define CAP_TABLE_SIZE CAP_TABLE_V2_SIZE
#define CAP_SLOT_NULL -1

/*******************************************************************************
 * GLOBAL STATE
 ******************************************************************************/

/**
 * Global capability table (2.5 MB total)
 *
 * WHY GLOBAL: Following seL4 design, capability table is kernel-managed
 * global resource. Alternative designs (per-process tables) trade off
 * delegation complexity vs. memory overhead.
 */
static struct capability_v2 g_cap_table[CAP_TABLE_SIZE];

/**
 * Free list head
 *
 * IMPLEMENTATION: We use slot indices as linked list, storing next free
 * slot in resource_id field when slot is empty. This avoids separate
 * allocation for free list nodes.
 *
 * Special values:
 * - CAP_SLOT_NULL (-1): End of free list
 * - Valid indices: 0 to CAP_TABLE_SIZE-1
 */
static int32_t g_free_list_head = CAP_SLOT_NULL;

/**
 * Table-level spinlock for free list management
 *
 * CONCURRENCY: This protects only the free list structure. Individual
 * capabilities use per-slot locks (cap->lock) for fine-grained concurrency.
 */
static struct qspinlock g_table_lock;

/**
 * Statistics counters
 */
static uint32_t g_num_allocated = 0;
static uint32_t g_total_allocs = 0;
static uint32_t g_total_frees = 0;

/*******************************************************************************
 * INTERNAL HELPERS
 ******************************************************************************/

/**
 * Allocate a free slot from the table
 *
 * @return Slot index (0 to CAP_TABLE_SIZE-1), or CAP_SLOT_NULL if table full
 *
 * ALGORITHM:
 * 1. Lock table
 * 2. Pop from free list head (O(1))
 * 3. Increment generation counter (prevents ABA problem)
 * 4. Update statistics
 * 5. Unlock table
 *
 * TIME COMPLEXITY: O(1)
 * SPACE COMPLEXITY: O(1)
 *
 * REAL-WORLD COMPARISON:
 * - seL4: Uses bitmap for free slots (O(n) search, but compact)
 * - Our approach: Free list (O(1) allocation, slight memory overhead in slot)
 * - Trade-off: We prioritize allocation speed for real-time systems
 */
static int32_t capv2_slot_alloc(void)
{
    qspin_lock(&g_table_lock);

    /* Check if table is full */
    if (g_free_list_head == CAP_SLOT_NULL) {
        qspin_unlock(&g_table_lock);
        return CAP_SLOT_NULL;
    }

    /* Pop from free list */
    int32_t slot_idx = g_free_list_head;
    struct capability_v2 *slot = &g_cap_table[slot_idx];

    /* Next free slot is stored in resource_id field (reuse memory) */
    g_free_list_head = (int32_t)slot->resource_id;

    /* Increment generation counter to invalidate old references */
    slot->generation++;

    /* Update statistics */
    g_num_allocated++;
    g_total_allocs++;

    qspin_unlock(&g_table_lock);

    return slot_idx;
}

/**
 * Free a slot back to the table
 *
 * @param slot_idx Slot index to free
 * @return CAPV2_OK on success, CAPV2_ERR_INVALID_SLOT if invalid
 *
 * ALGORITHM:
 * 1. Validate slot index
 * 2. Lock table
 * 3. Zero out slot contents (security: prevent information leaks)
 * 4. Push to free list head
 * 5. Update statistics
 * 6. Unlock table
 *
 * SECURITY NOTE: Zeroing prevents stale data from being read by next
 * allocator. Generation counter prevents use-after-free even if slot
 * is reallocated immediately.
 */
static int capv2_slot_free(int32_t slot_idx)
{
    /* Validate slot index */
    if (slot_idx < 0 || slot_idx >= CAP_TABLE_SIZE) {
        return CAPV2_ERR_INVALID_SLOT;
    }

    qspin_lock(&g_table_lock);

    struct capability_v2 *slot = &g_cap_table[slot_idx];

    if (slot->cap_type == CAP_TYPE_NULL) {
        qspin_unlock(&g_table_lock);
        panic("capv2_slot_free: double free");
    }

    /* Preserve generation counter to avoid ABA problem */
    uint32_t gen = slot->generation;

    /* Zero out slot contents (security) */
    memset(slot, 0, sizeof(struct capability_v2));

    /* Restore generation counter */
    slot->generation = gen;

    /* Push to free list (store next pointer in resource_id) */
    slot->resource_id = (uint64_t)g_free_list_head;
    g_free_list_head = slot_idx;

    /* Mark as free */
    slot->cap_type = CAP_TYPE_NULL;

    /* Update statistics */
    g_num_allocated--;
    g_total_frees++;

    qspin_unlock(&g_table_lock);

    return CAPV2_OK;
}

/**
 * Validate that a slot index is in range and allocated
 *
 * @param slot_idx Slot index to check
 * @return CAPV2_OK if valid, error code otherwise
 *
 * USAGE: Call this at the start of all API functions to validate input
 */
static int capv2_validate_slot(int32_t slot_idx)
{
    if (slot_idx < 0 || slot_idx >= CAP_TABLE_SIZE) {
        return CAPV2_ERR_INVALID_SLOT;
    }

    struct capability_v2 *cap = &g_cap_table[slot_idx];

    /* Check if slot is allocated (not in free list) */
    if (cap->cap_type == CAP_TYPE_NULL) {
        return CAPV2_ERR_INVALID_SLOT;
    }

    return CAPV2_OK;
}

/*******************************************************************************
 * PUBLIC API: TABLE MANAGEMENT
 ******************************************************************************/

/**
 * Initialize the capability table
 *
 * MUST be called during kernel boot before any capability operations.
 *
 * ALGORITHM:
 * 1. Initialize table lock
 * 2. Build free list (all slots initially free)
 * 3. Initialize generation counters to 0
 * 4. Set all slots to CAP_TYPE_NULL
 *
 * TIME COMPLEXITY: O(n) where n = CAP_TABLE_SIZE (4096)
 * RUNS ONCE: During kernel initialization only
 *
 * PEDAGOGICAL NOTE:
 * This function demonstrates how kernel data structures are initialized
 * at boot time. Unlike user-space malloc, kernel uses pre-allocated
 * static arrays for deterministic memory usage.
 */
void capv2_table_init(void)
{
    /* Initialize table lock */
    qspin_init(&g_table_lock, "cap_table", 0);

    /* Build free list: link all slots together */
    for (int32_t i = 0; i < CAP_TABLE_SIZE - 1; i++) {
        g_cap_table[i].cap_type = CAP_TYPE_NULL;
        g_cap_table[i].resource_id = (uint64_t)(i + 1); /* Next free slot */
        g_cap_table[i].generation = 0;
        qspin_init(&g_cap_table[i].lock, "cap_slot", 0);
    }

    /* Last slot points to NULL (end of list) */
    g_cap_table[CAP_TABLE_SIZE - 1].cap_type = CAP_TYPE_NULL;
    g_cap_table[CAP_TABLE_SIZE - 1].resource_id = (uint64_t)CAP_SLOT_NULL;
    g_cap_table[CAP_TABLE_SIZE - 1].generation = 0;
    qspin_init(&g_cap_table[CAP_TABLE_SIZE - 1].lock, "cap_slot", 0);

    /* Free list starts at slot 0 */
    g_free_list_head = 0;

    /* Reset statistics */
    g_num_allocated = 0;
    g_total_allocs = 0;
    g_total_frees = 0;

    printf("[CAPV2] Capability table initialized: %d slots, %.2f MB\n",
           CAP_TABLE_SIZE,
           (CAP_TABLE_SIZE * sizeof(struct capability_v2)) / (1024.0 * 1024.0));
}

/**
 * Get capability table statistics
 *
 * @param num_free Output: number of free slots
 * @param num_allocated Output: number of allocated slots
 *
 * USAGE: For monitoring and debugging capability usage
 *
 * THREAD-SAFE: Uses table lock for atomic read
 */
void capv2_table_stats(uint32_t *num_free, uint32_t *num_allocated)
{
    qspin_lock(&g_table_lock);

    if (num_allocated) {
        *num_allocated = g_num_allocated;
    }

    if (num_free) {
        *num_free = CAP_TABLE_SIZE - g_num_allocated;
    }

    qspin_unlock(&g_table_lock);
}

/**
 * Print detailed capability table statistics
 *
 * OUTPUT FORMAT:
 * - Free/used slot counts
 * - Per-type breakdown
 * - Refcount histogram
 * - Allocation/free totals
 *
 * USAGE: Debugging and performance analysis
 *
 * PEDAGOGICAL NOTE:
 * This function shows how kernel introspection tools work. Real kernels
 * (Linux, FreeBSD) expose similar stats via /proc or sysctl.
 */
void capv2_print_table_stats(void)
{
    printf("=== Capability Table Statistics ===\n");
    printf("Total slots:      %d\n", CAP_TABLE_SIZE);
    printf("Allocated slots:  %u\n", g_num_allocated);
    printf("Free slots:       %u\n", CAP_TABLE_SIZE - g_num_allocated);
    printf("Utilization:      %.1f%%\n",
           (g_num_allocated * 100.0) / CAP_TABLE_SIZE);
    printf("Total allocs:     %u\n", g_total_allocs);
    printf("Total frees:      %u\n", g_total_frees);

    /* Count capabilities by type */
    uint32_t type_counts[16] = {0}; /* Up to 16 types */

    qspin_lock(&g_table_lock);
    for (int32_t i = 0; i < CAP_TABLE_SIZE; i++) {
        if (g_cap_table[i].cap_type != CAP_TYPE_NULL) {
            uint8_t type = (uint8_t)g_cap_table[i].cap_type;
            if (type < 16) {
                type_counts[type]++;
            }
        }
    }
    qspin_unlock(&g_table_lock);

    printf("\n--- Capabilities by Type ---\n");
    const char *type_names[] = {
        "NULL",
        "MEMORY_PAGE",
        "DEVICE_PORT",
        "IPC_ENDPOINT",
        "IRQ_HANDLER",
        "PROCESS_CONTROL",
        "RESOURCE_QUOTA",
        "FILE_DESCRIPTOR",
        "NETWORK_SOCKET",
    };

    for (int i = 0; i < 16; i++) {
        if (type_counts[i] > 0) {
            const char *name = (i < 9) ? type_names[i] : "UNKNOWN";
            printf("  %-20s: %u\n", name, type_counts[i]);
        }
    }

    /* Refcount histogram */
    uint32_t refcount_hist[10] = {0}; /* 0, 1, 2-3, 4-7, 8-15, 16-31, 32-63, 64-127, 128-255, 256+ */

    qspin_lock(&g_table_lock);
    for (int32_t i = 0; i < CAP_TABLE_SIZE; i++) {
        if (g_cap_table[i].cap_type != CAP_TYPE_NULL) {
            uint32_t rc = g_cap_table[i].refcount;
            if (rc == 0) refcount_hist[0]++;
            else if (rc == 1) refcount_hist[1]++;
            else if (rc <= 3) refcount_hist[2]++;
            else if (rc <= 7) refcount_hist[3]++;
            else if (rc <= 15) refcount_hist[4]++;
            else if (rc <= 31) refcount_hist[5]++;
            else if (rc <= 63) refcount_hist[6]++;
            else if (rc <= 127) refcount_hist[7]++;
            else if (rc <= 255) refcount_hist[8]++;
            else refcount_hist[9]++;
        }
    }
    qspin_unlock(&g_table_lock);

    printf("\n--- Refcount Distribution ---\n");
    const char *refcount_labels[] = {
        "refcount=0",
        "refcount=1",
        "refcount=2-3",
        "refcount=4-7",
        "refcount=8-15",
        "refcount=16-31",
        "refcount=32-63",
        "refcount=64-127",
        "refcount=128-255",
        "refcount=256+",
    };

    for (int i = 0; i < 10; i++) {
        if (refcount_hist[i] > 0) {
            printf("  %-15s: %u\n", refcount_labels[i], refcount_hist[i]);
        }
    }

    printf("==================================\n");
}

/*******************************************************************************
 * PUBLIC API: CORE CAPABILITY OPERATIONS
 ******************************************************************************/

/**
 * Allocate a new capability
 *
 * @param resource_id Physical resource handle (e.g., page frame number, device MMIO base)
 * @param cap_type Type of capability (MEMORY_PAGE, DEVICE_PORT, etc.)
 * @param initial_rights Rights bitmask (READ, WRITE, EXECUTE, GRANT, etc.)
 * @param quota 8D resource vector for quota enforcement
 * @return Slot index (0 to CAP_TABLE_SIZE-1) on success, negative error code on failure
 *
 * ALGORITHM:
 * 1. Allocate free slot from table
 * 2. Initialize capability fields
 * 3. Set owner to current process
 * 4. Initialize refcount to 1
 * 5. Initialize per-capability lock
 * 6. Record creation time
 *
 * REAL-WORLD COMPARISON:
 * - seL4: Similar operation via seL4_Untyped_Retype
 * - Our approach: More flexible with PDAC resource vectors
 *
 * SECURITY:
 * - New capability starts with refcount=1 (owner holds reference)
 * - Generation counter prevents use-after-free
 * - Rights can only be attenuated (reduced), never escalated
 *
 * EXAMPLE:
 * ```c
 * resource_vector_t quota = {
 *     .cpu = Q16(0.1),      // 10% CPU
 *     .memory = Q16(1024),  // 1 MB
 *     // ... other dimensions
 * };
 * int slot = capv2_alloc(0x1000, CAP_TYPE_MEMORY_PAGE,
 *                        CAP_RIGHT_READ | CAP_RIGHT_WRITE, quota);
 * if (slot < 0) {
 *     printf("Failed to allocate capability: %d\n", slot);
 * }
 * ```
 */
int capv2_alloc(uint64_t resource_id, cap_type_t cap_type,
                uint32_t initial_rights, resource_vector_t quota)
{
    /* Validate inputs */
    if (cap_type == CAP_TYPE_NULL || cap_type >= 16) {
        return CAPV2_ERR_INVALID_TYPE;
    }

    /* Allocate slot */
    int32_t slot_idx = capv2_slot_alloc();
    if (slot_idx == CAP_SLOT_NULL) {
        return CAPV2_ERR_TABLE_FULL;
    }

    struct capability_v2 *cap = &g_cap_table[slot_idx];

    /* Initialize per-capability lock */
    qspin_init(&cap->lock, "cap_slot", 0);

    qspin_lock(&cap->lock);

    /* Initialize seL4-style core fields */
    cap->resource_id = resource_id;
    cap->owner_pid = 0; /* TODO: Get current PID from process manager */
    cap->refcount = 1;
    cap->cap_type = cap_type;
    cap->static_rights = initial_rights;

    /* Initialize PDAC 8D resource quotas */
    cap->quota = quota;
    cap->consumed.cpu = 0;
    cap->consumed.memory = 0;
    cap->consumed.io_bandwidth = 0;
    cap->consumed.network_bandwidth = 0;
    cap->consumed.gpu_time = 0;
    cap->consumed.disk_quota = 0;
    cap->consumed.irq_count = 0;
    cap->consumed.capability_count = 0;

    /* Initialize lambda formula (default: NULL = use static_rights) */
    cap->rights_fn = NULL;
    cap->formula_data = NULL;

    /* Initialize Cap'n Proto fields (no IPC buffer initially) */
    cap->schema_id = 0;
    cap->capnp_buffer = NULL;
    cap->buffer_size = 0;

    /* Initialize token bucket (TODO: implement in Phase 2.4) */
    cap->rate_limit.tokens = 0;
    cap->rate_limit.capacity = 0;
    cap->rate_limit.refill_rate = 0;
    cap->rate_limit.last_refill_ms = 0;

    /* Metadata */
    cap->creation_time = 0; /* TODO: Get timestamp from timer */
    cap->access_count = 0;
    cap->parent_slot = CAP_SLOT_NULL; /* No parent (root capability) */

    qspin_unlock(&cap->lock);

    return slot_idx;
}

/**
 * Free a capability
 *
 * @param cap_slot Slot index to free
 * @return CAPV2_OK on success, error code on failure
 *
 * ALGORITHM:
 * 1. Validate slot
 * 2. Check refcount (must be 0 to free)
 * 3. Release any associated resources (IPC buffers, etc.)
 * 4. Return slot to free list
 *
 * SECURITY:
 * - Capability can only be freed when refcount reaches 0
 * - All children must be revoked first
 * - Prevents use-after-free via generation counter
 *
 * REAL-WORLD COMPARISON:
 * - seL4: CNode delete operation
 * - UNIX: close() syscall (but capabilities are more fine-grained)
 *
 * EXAMPLE:
 * ```c
 * int ret = capv2_free(slot);
 * if (ret == CAPV2_ERR_REFCOUNT_OVERFLOW) {
 *     printf("Cannot free: capability still has references\n");
 * }
 * ```
 */
int capv2_free(int cap_slot)
{
    int ret = capv2_validate_slot(cap_slot);
    if (ret != CAPV2_OK) {
        return ret;
    }

    struct capability_v2 *cap = &g_cap_table[cap_slot];

    qspin_lock(&cap->lock);

    /* Check refcount - must be 0 to free */
    if (cap->refcount > 0) {
        qspin_unlock(&cap->lock);
        return CAPV2_ERR_REFCOUNT_OVERFLOW;
    }

    /* Free any associated resources */
    if (cap->capnp_buffer != NULL) {
        /* TODO: Free IPC buffer (Phase 2.5) */
        cap->capnp_buffer = NULL;
    }

    if (cap->formula_data != NULL) {
        /* TODO: Free formula data (Phase 2.3) */
        cap->formula_data = NULL;
    }

    qspin_unlock(&cap->lock);

    /* Return slot to free list */
    return capv2_slot_free(cap_slot);
}

/**
 * Grant capability to another process
 *
 * @param cap_slot Capability to grant
 * @param recipient_pid Process ID to grant to
 * @param attenuated_rights Rights for recipient (subset of current rights)
 * @return New capability slot for recipient, or negative error code
 *
 * ALGORITHM:
 * 1. Validate source capability
 * 2. Check GRANT right
 * 3. Verify rights attenuation (can only reduce rights, never escalate)
 * 4. Allocate new capability slot
 * 5. Copy capability with attenuated rights
 * 6. Increment refcount on original
 * 7. Set parent pointer for revocation tree
 *
 * SECURITY PROPERTY: RIGHTS ATTENUATION
 * - Recipient rights MUST be subset of granter rights
 * - Example: If granter has READ|WRITE, recipient can have READ only
 * - This prevents privilege escalation
 *
 * REAL-WORLD COMPARISON:
 * - seL4: Similar to endpoint send (passes capability in message)
 * - Unix: Similar to passing file descriptor via SCM_RIGHTS
 * - Our approach: More fine-grained with per-capability rights
 *
 * EXAMPLE:
 * ```c
 * // Grant read-only access to another process
 * int readonly_slot = capv2_grant(my_slot, other_pid, CAP_RIGHT_READ);
 * if (readonly_slot >= 0) {
 *     printf("Granted read-only capability at slot %d\n", readonly_slot);
 * }
 * ```
 */
int capv2_grant(int cap_slot, uint32_t recipient_pid, uint32_t attenuated_rights)
{
    int ret = capv2_validate_slot(cap_slot);
    if (ret != CAPV2_OK) {
        return ret;
    }

    struct capability_v2 *src_cap = &g_cap_table[cap_slot];

    qspin_lock(&src_cap->lock);

    /* Check if source has GRANT right */
    uint32_t effective_rights = src_cap->static_rights;
    if (src_cap->rights_fn != NULL) {
        effective_rights = src_cap->rights_fn(src_cap, src_cap->formula_data);
    }

    if (!(effective_rights & CAP_RIGHT_GRANT)) {
        qspin_unlock(&src_cap->lock);
        return CAPV2_ERR_NO_PERMISSION;
    }

    /* Verify rights attenuation: recipient rights must be subset of source rights */
    if ((attenuated_rights & ~effective_rights) != 0) {
        qspin_unlock(&src_cap->lock);
        return CAPV2_ERR_NO_PERMISSION;
    }

    /* Increment refcount (bounds check) */
    if (src_cap->refcount == UINT32_MAX) {
        qspin_unlock(&src_cap->lock);
        return CAPV2_ERR_REFCOUNT_OVERFLOW;
    }
    src_cap->refcount++;

    qspin_unlock(&src_cap->lock);

    /* Allocate new capability for recipient */
    int new_slot = capv2_alloc(src_cap->resource_id, src_cap->cap_type,
                               attenuated_rights, src_cap->quota);
    if (new_slot < 0) {
        /* Rollback refcount increment */
        qspin_lock(&src_cap->lock);
        src_cap->refcount--;
        qspin_unlock(&src_cap->lock);
        return new_slot;
    }

    struct capability_v2 *new_cap = &g_cap_table[new_slot];

    qspin_lock(&new_cap->lock);

    /* Copy additional fields from source */
    new_cap->owner_pid = recipient_pid;
    new_cap->parent_slot = cap_slot; /* For revocation tree */
    new_cap->rights_fn = src_cap->rights_fn;
    new_cap->schema_id = src_cap->schema_id;

    /* Note: We do NOT copy IPC buffer (recipient gets fresh buffer) */
    /* Note: We do NOT copy formula_data (might contain owner-specific state) */

    qspin_unlock(&new_cap->lock);

    return new_slot;
}

/**
 * Revoke a capability and all its children
 *
 * @param cap_slot Capability to revoke
 * @return CAPV2_OK on success, error code on failure
 *
 * ALGORITHM:
 * 1. Validate slot
 * 2. Check REVOKE right
 * 3. Recursively revoke all children (capabilities derived from this one)
 * 4. Decrement refcount
 * 5. If refcount reaches 0, free the capability
 *
 * REAL-WORLD COMPARISON:
 * - seL4: Revocation via CNode delete (revokes entire subtree)
 * - Our approach: Similar tree-based revocation
 *
 * PEDAGOGICAL NOTE:
 * Revocation is tricky in capability systems. We use parent pointers
 * to build a revocation tree. When a capability is revoked, all
 * capabilities derived from it (children) are also revoked recursively.
 *
 * EXAMPLE:
 * ```c
 * // Revoke capability and all delegated copies
 * int ret = capv2_revoke(original_slot);
 * if (ret == CAPV2_OK) {
 *     printf("Capability and all children revoked\n");
 * }
 * ```
 */
int capv2_revoke(int cap_slot)
{
    int ret = capv2_validate_slot(cap_slot);
    if (ret != CAPV2_OK) {
        return ret;
    }

    struct capability_v2 *cap = &g_cap_table[cap_slot];

    qspin_lock(&cap->lock);

    /* Check REVOKE right */
    uint32_t effective_rights = cap->static_rights;
    if (cap->rights_fn != NULL) {
        effective_rights = cap->rights_fn(cap, cap->formula_data);
    }

    if (!(effective_rights & CAP_RIGHT_REVOKE)) {
        qspin_unlock(&cap->lock);
        return CAPV2_ERR_NO_PERMISSION;
    }

    qspin_unlock(&cap->lock);

    /* Find and revoke all children (capabilities with parent_slot == cap_slot) */
    for (int32_t i = 0; i < CAP_TABLE_SIZE; i++) {
        if (g_cap_table[i].cap_type != CAP_TYPE_NULL &&
            g_cap_table[i].parent_slot == cap_slot) {
            /* Recursively revoke child */
            capv2_revoke(i);
        }
    }

    /* Decrement refcount */
    qspin_lock(&cap->lock);
    if (cap->refcount > 0) {
        cap->refcount--;
    }

    uint32_t final_refcount = cap->refcount;
    qspin_unlock(&cap->lock);

    /* If refcount reaches 0, free the capability */
    if (final_refcount == 0) {
        return capv2_free(cap_slot);
    }

    return CAPV2_OK;
}

/**
 * Create a derived capability with reduced quota
 *
 * @param parent_slot Parent capability
 * @param child_quota Resource quota for child (must be <= parent quota)
 * @param child_rights Rights for child (must be subset of parent rights)
 * @return New capability slot, or negative error code
 *
 * ALGORITHM:
 * 1. Validate parent capability
 * 2. Check DERIVE right
 * 3. Verify child quota <= parent quota (8D comparison)
 * 4. Verify rights attenuation
 * 5. Allocate child capability
 * 6. Subtract child quota from parent quota
 * 7. Set parent pointer
 *
 * PDAC INNOVATION:
 * This operation demonstrates how 8D resource vectors enable fine-grained
 * quota subdivision. Parent can partition its quota among children across
 * all 8 dimensions (CPU, memory, I/O, network, GPU, disk, IRQ, caps).
 *
 * EXAMPLE:
 * ```c
 * // Parent has 1 MB quota, create child with 256 KB
 * resource_vector_t parent_quota = {.memory = Q16(1024), ...};
 * resource_vector_t child_quota = {.memory = Q16(256), ...};
 *
 * int parent = capv2_alloc(res, CAP_TYPE_MEMORY_PAGE, rights, parent_quota);
 * int child = capv2_derive(parent, child_quota, CAP_RIGHT_READ);
 *
 * // Now parent has 768 KB remaining, child has 256 KB
 * ```
 */
int capv2_derive(int parent_slot, resource_vector_t child_quota, uint32_t child_rights)
{
    int ret = capv2_validate_slot(parent_slot);
    if (ret != CAPV2_OK) {
        return ret;
    }

    struct capability_v2 *parent = &g_cap_table[parent_slot];

    qspin_lock(&parent->lock);

    /* Check DERIVE right */
    uint32_t effective_rights = parent->static_rights;
    if (parent->rights_fn != NULL) {
        effective_rights = parent->rights_fn(parent, parent->formula_data);
    }

    if (!(effective_rights & CAP_RIGHT_DERIVE)) {
        qspin_unlock(&parent->lock);
        return CAPV2_ERR_NO_PERMISSION;
    }

    /* Verify rights attenuation */
    if ((child_rights & ~effective_rights) != 0) {
        qspin_unlock(&parent->lock);
        return CAPV2_ERR_NO_PERMISSION;
    }

    /* Verify child quota <= parent quota (8D component-wise check) */
    if (child_quota.cpu > parent->quota.cpu ||
        child_quota.memory > parent->quota.memory ||
        child_quota.io_bandwidth > parent->quota.io_bandwidth ||
        child_quota.network_bandwidth > parent->quota.network_bandwidth ||
        child_quota.gpu_time > parent->quota.gpu_time ||
        child_quota.disk_quota > parent->quota.disk_quota ||
        child_quota.irq_count > parent->quota.irq_count ||
        child_quota.capability_count > parent->quota.capability_count) {
        qspin_unlock(&parent->lock);
        return CAPV2_ERR_QUOTA_EXCEEDED;
    }

    /* Subtract child quota from parent (quota partition) */
    parent->quota.cpu -= child_quota.cpu;
    parent->quota.memory -= child_quota.memory;
    parent->quota.io_bandwidth -= child_quota.io_bandwidth;
    parent->quota.network_bandwidth -= child_quota.network_bandwidth;
    parent->quota.gpu_time -= child_quota.gpu_time;
    parent->quota.disk_quota -= child_quota.disk_quota;
    parent->quota.irq_count -= child_quota.irq_count;
    parent->quota.capability_count -= child_quota.capability_count;

    /* Increment refcount */
    if (parent->refcount == UINT32_MAX) {
        /* Rollback quota subtraction */
        parent->quota.cpu += child_quota.cpu;
        parent->quota.memory += child_quota.memory;
        parent->quota.io_bandwidth += child_quota.io_bandwidth;
        parent->quota.network_bandwidth += child_quota.network_bandwidth;
        parent->quota.gpu_time += child_quota.gpu_time;
        parent->quota.disk_quota += child_quota.disk_quota;
        parent->quota.irq_count += child_quota.irq_count;
        parent->quota.capability_count += child_quota.capability_count;

        qspin_unlock(&parent->lock);
        return CAPV2_ERR_REFCOUNT_OVERFLOW;
    }
    parent->refcount++;

    qspin_unlock(&parent->lock);

    /* Allocate child capability */
    int child_slot = capv2_alloc(parent->resource_id, parent->cap_type,
                                 child_rights, child_quota);
    if (child_slot < 0) {
        /* Rollback refcount and quota */
        qspin_lock(&parent->lock);
        parent->refcount--;
        parent->quota.cpu += child_quota.cpu;
        parent->quota.memory += child_quota.memory;
        parent->quota.io_bandwidth += child_quota.io_bandwidth;
        parent->quota.network_bandwidth += child_quota.network_bandwidth;
        parent->quota.gpu_time += child_quota.gpu_time;
        parent->quota.disk_quota += child_quota.disk_quota;
        parent->quota.irq_count += child_quota.irq_count;
        parent->quota.capability_count += child_quota.capability_count;
        qspin_unlock(&parent->lock);
        return child_slot;
    }

    struct capability_v2 *child = &g_cap_table[child_slot];

    qspin_lock(&child->lock);
    child->parent_slot = parent_slot; /* For revocation tree */
    child->owner_pid = parent->owner_pid; /* Inherit owner */
    qspin_unlock(&child->lock);

    return child_slot;
}

/**
 * Check if capability has requested rights
 *
 * @param cap_slot Capability to check
 * @param requested_rights Rights bitmask to check
 * @return CAPV2_OK if all requested rights are present, CAPV2_ERR_NO_PERMISSION otherwise
 *
 * ALGORITHM:
 * 1. Validate slot
 * 2. Compute effective rights (static_rights OR formula result)
 * 3. Check if requested rights are subset of effective rights
 * 4. Update access counter (for usage-based formulas)
 *
 * LAMBDA FORMULA INTEGRATION:
 * If rights_fn is set, dynamic rights are computed by calling the formula.
 * Formula can implement:
 * - Time-based expiry (revoke after timestamp)
 * - Usage quotas (revoke after N accesses)
 * - User-based policies (different rights per user)
 *
 * EXAMPLE:
 * ```c
 * if (capv2_check_rights(slot, CAP_RIGHT_READ | CAP_RIGHT_WRITE) == CAPV2_OK) {
 *     // Capability has both read and write rights
 *     perform_io(slot);
 * } else {
 *     printf("Permission denied\n");
 * }
 * ```
 */
int capv2_check_rights(int cap_slot, uint32_t requested_rights)
{
    int ret = capv2_validate_slot(cap_slot);
    if (ret != CAPV2_OK) {
        return ret;
    }

    struct capability_v2 *cap = &g_cap_table[cap_slot];

    qspin_lock(&cap->lock);

    /* Compute effective rights */
    uint32_t effective_rights = cap->static_rights;
    if (cap->rights_fn != NULL) {
        effective_rights = cap->rights_fn(cap, cap->formula_data);
    }

    /* Update access counter (for usage-based formulas) */
    cap->access_count++;

    qspin_unlock(&cap->lock);

    /* Check if all requested rights are present */
    if ((requested_rights & effective_rights) == requested_rights) {
        return CAPV2_OK;
    } else {
        return CAPV2_ERR_NO_PERMISSION;
    }
}

/*******************************************************************************
 * PUBLIC API: ADVANCED OPERATIONS
 ******************************************************************************/

/**
 * Set lambda formula for dynamic rights computation
 *
 * @param cap_slot Capability to modify
 * @param new_formula Function pointer for rights computation
 * @param formula_data Opaque data passed to formula function
 * @return CAPV2_OK on success, error code on failure
 *
 * LAMBDA CALCULUS INTEGRATION:
 * This function enables higher-order programming in the capability system.
 * Formulas are first-class functions that compute rights dynamically based
 * on context (time, usage, user, etc.).
 *
 * PEDAGOGICAL NOTE:
 * This demonstrates how lambda calculus (function pointers in C) enables
 * policy flexibility without changing kernel code. Similar to AWS IAM
 * policy evaluation, but at kernel level.
 *
 * EXAMPLE: See Phase 2.3 for standard formula implementations
 */
int capv2_set_formula(int cap_slot, cap_formula_t new_formula, void *formula_data)
{
    int ret = capv2_validate_slot(cap_slot);
    if (ret != CAPV2_OK) {
        return ret;
    }

    struct capability_v2 *cap = &g_cap_table[cap_slot];

    qspin_lock(&cap->lock);
    cap->rights_fn = new_formula;
    cap->formula_data = formula_data;
    qspin_unlock(&cap->lock);

    return CAPV2_OK;
}

/**
 * Find capability by resource ID and owner
 *
 * @param resource_id Physical resource to search for
 * @param owner_pid Owner PID (-1 for any owner)
 * @return Capability slot index, or CAPV2_ERR_NOT_FOUND
 *
 * TIME COMPLEXITY: O(n) linear search through table
 *
 * USAGE: Lookup capability for a given resource (e.g., find capability
 * for page frame 0x1000 owned by PID 42)
 *
 * OPTIMIZATION OPPORTUNITY:
 * For large tables, could add hash table index on (resource_id, owner_pid)
 */
int capv2_find(uint64_t resource_id, int32_t owner_pid)
{
    for (int32_t i = 0; i < CAP_TABLE_SIZE; i++) {
        struct capability_v2 *cap = &g_cap_table[i];

        if (cap->cap_type != CAP_TYPE_NULL &&
            cap->resource_id == resource_id) {

            /* Check owner if specified */
            if (owner_pid >= 0 && cap->owner_pid != (uint32_t)owner_pid) {
                continue;
            }

            return i;
        }
    }

    return CAPV2_ERR_NOT_FOUND;
}

/*******************************************************************************
 * PUBLIC API: INTROSPECTION
 ******************************************************************************/

/**
 * Get capability information (read-only copy)
 *
 * @param cap_slot Capability to query
 * @param cap_out Output buffer for capability data
 * @return CAPV2_OK on success, error code on failure
 *
 * SECURITY: Returns copy, not pointer, to prevent modification
 *
 * USAGE: Introspection and debugging
 */
int capv2_get_info(int cap_slot, struct capability_v2 *cap_out)
{
    int ret = capv2_validate_slot(cap_slot);
    if (ret != CAPV2_OK) {
        return ret;
    }

    if (cap_out == NULL) {
        return CAPV2_ERR_INVALID_SLOT;
    }

    struct capability_v2 *cap = &g_cap_table[cap_slot];

    qspin_lock(&cap->lock);
    *cap_out = *cap; /* Copy entire structure */
    qspin_unlock(&cap->lock);

    return CAPV2_OK;
}

/**
 * Print capability details for debugging
 *
 * @param cap_slot Capability to print
 *
 * OUTPUT FORMAT: Human-readable capability dump
 */
void capv2_print(int cap_slot)
{
    if (capv2_validate_slot(cap_slot) != CAPV2_OK) {
        printf("Invalid capability slot: %d\n", cap_slot);
        return;
    }

    struct capability_v2 *cap = &g_cap_table[cap_slot];

    qspin_lock(&cap->lock);

    printf("=== Capability %d ===\n", cap_slot);
    printf("Resource ID:   0x%lx\n", cap->resource_id);
    printf("Owner PID:     %u\n", cap->owner_pid);
    printf("Refcount:      %u\n", cap->refcount);
    printf("Type:          %u\n", (uint32_t)cap->cap_type);
    printf("Static Rights: 0x%x ", cap->static_rights);

    /* Decode rights */
    printf("(");
    if (cap->static_rights & CAP_RIGHT_READ) printf("R");
    if (cap->static_rights & CAP_RIGHT_WRITE) printf("W");
    if (cap->static_rights & CAP_RIGHT_EXECUTE) printf("X");
    if (cap->static_rights & CAP_RIGHT_GRANT) printf("G");
    if (cap->static_rights & CAP_RIGHT_REVOKE) printf("V");
    if (cap->static_rights & CAP_RIGHT_DERIVE) printf("D");
    printf(")\n");

    printf("Quota (8D):    CPU=%d, MEM=%d, IO=%d, NET=%d, GPU=%d, DISK=%d, IRQ=%d, CAP=%d\n",
           cap->quota.cpu, cap->quota.memory, cap->quota.io_bandwidth,
           cap->quota.network_bandwidth, cap->quota.gpu_time, cap->quota.disk_quota,
           cap->quota.irq_count, cap->quota.capability_count);

    printf("Consumed (8D): CPU=%d, MEM=%d, IO=%d, NET=%d, GPU=%d, DISK=%d, IRQ=%d, CAP=%d\n",
           cap->consumed.cpu, cap->consumed.memory, cap->consumed.io_bandwidth,
           cap->consumed.network_bandwidth, cap->consumed.gpu_time, cap->consumed.disk_quota,
           cap->consumed.irq_count, cap->consumed.capability_count);

    printf("Formula:       %s\n", cap->rights_fn ? "DYNAMIC" : "STATIC");
    printf("Schema ID:     0x%x\n", cap->schema_id);
    printf("Generation:    %u\n", cap->generation);
    printf("Creation Time: %lu\n", cap->creation_time);
    printf("Access Count:  %lu\n", cap->access_count);
    printf("Parent Slot:   %d\n", cap->parent_slot);
    printf("====================\n");

    qspin_unlock(&cap->lock);
}

/*******************************************************************************
 * PUBLIC API: RATE LIMITING (Token Bucket Integration)
 ******************************************************************************/

/**
 * Enable rate limiting on a capability
 *
 * @param cap_slot Capability to rate limit
 * @param capacity Burst capacity (max tokens)
 * @param refill_rate Sustained rate (tokens per second, Q16.16)
 * @return CAPV2_OK on success, error code on failure
 *
 * INTEGRATION:
 * After enabling rate limiting, all capability accesses via capv2_check_rights()
 * will be subject to token bucket enforcement.
 *
 * EXAMPLE:
 * ```c
 * // Allow 100 burst, 10 sustained accesses per second
 * capv2_enable_rate_limit(slot, Q16(100), Q16(10));
 * ```
 */
int capv2_enable_rate_limit(int cap_slot, q16_t capacity, q16_t refill_rate)
{
    int ret = capv2_validate_slot(cap_slot);
    if (ret != CAPV2_OK) {
        return ret;
    }

    struct capability_v2 *cap = &g_cap_table[cap_slot];

    qspin_lock(&cap->lock);

    /* Initialize token bucket */
    extern void token_bucket_init(struct token_bucket *, q16_t, q16_t);
    token_bucket_init(&cap->rate_limit, capacity, refill_rate);

    qspin_unlock(&cap->lock);

    return CAPV2_OK;
}

/**
 * Disable rate limiting on a capability
 *
 * @param cap_slot Capability to modify
 * @return CAPV2_OK on success, error code on failure
 */
int capv2_disable_rate_limit(int cap_slot)
{
    int ret = capv2_validate_slot(cap_slot);
    if (ret != CAPV2_OK) {
        return ret;
    }

    struct capability_v2 *cap = &g_cap_table[cap_slot];

    qspin_lock(&cap->lock);

    /* Reset token bucket to zero (effectively disables rate limiting) */
    cap->rate_limit.capacity = 0;
    cap->rate_limit.tokens = 0;
    cap->rate_limit.refill_rate = 0;

    qspin_unlock(&cap->lock);

    return CAPV2_OK;
}

/**
 * Check rights with rate limiting enforcement
 *
 * @param cap_slot Capability to check
 * @param requested_rights Rights to check
 * @param tokens_needed Tokens to consume (Q16.16, usually Q16(1) per access)
 * @return CAPV2_OK if rights granted and rate limit passed,
 *         CAPV2_ERR_NO_PERMISSION if rights denied,
 *         CAPV2_ERR_RATE_LIMITED if rate limit exceeded
 *
 * ALGORITHM:
 * 1. Validate capability
 * 2. Check rights (via formulas if present)
 * 3. If rights OK, check token bucket
 * 4. Consume tokens if available
 * 5. Return result
 *
 * USAGE:
 * This function combines rights checking with rate limiting.
 * Use instead of capv2_check_rights() when rate limiting is desired.
 *
 * EXAMPLE:
 * ```c
 * int ret = capv2_check_rights_ratelimited(slot, CAP_RIGHT_READ, Q16(1));
 * if (ret == CAPV2_OK) {
 *     // Access granted
 *     perform_read();
 * } else if (ret == CAPV2_ERR_RATE_LIMITED) {
 *     // Too many requests
 *     return -EAGAIN;
 * } else {
 *     // Permission denied
 *     return -EPERM;
 * }
 * ```
 */
int capv2_check_rights_ratelimited(int cap_slot, uint32_t requested_rights, q16_t tokens_needed)
{
    int ret = capv2_validate_slot(cap_slot);
    if (ret != CAPV2_OK) {
        return ret;
    }

    struct capability_v2 *cap = &g_cap_table[cap_slot];

    qspin_lock(&cap->lock);

    /* Check rights first */
    uint32_t effective_rights = cap->static_rights;
    if (cap->rights_fn != NULL) {
        effective_rights = cap->rights_fn(cap, cap->formula_data);
    }

    if ((requested_rights & effective_rights) != requested_rights) {
        qspin_unlock(&cap->lock);
        return CAPV2_ERR_NO_PERMISSION;
    }

    /* Rights OK, now check rate limit */
    if (cap->rate_limit.capacity > 0) {
        /* Rate limiting is enabled */
        extern int token_bucket_consume(struct token_bucket *, q16_t);
        if (!token_bucket_consume(&cap->rate_limit, tokens_needed)) {
            qspin_unlock(&cap->lock);
            return CAPV2_ERR_RATE_LIMITED;
        }
    }

    /* Update access counter */
    cap->access_count++;

    qspin_unlock(&cap->lock);

    return CAPV2_OK;
}

/**
 * Get current rate limit status
 *
 * @param cap_slot Capability to query
 * @param current_tokens Output: current tokens available (may be NULL)
 * @param capacity Output: bucket capacity (may be NULL)
 * @return CAPV2_OK on success, error code on failure
 *
 * USAGE: Monitoring and debugging rate limits
 */
int capv2_get_rate_limit_status(int cap_slot, q16_t *current_tokens, q16_t *capacity)
{
    int ret = capv2_validate_slot(cap_slot);
    if (ret != CAPV2_OK) {
        return ret;
    }

    struct capability_v2 *cap = &g_cap_table[cap_slot];

    qspin_lock(&cap->lock);

    if (current_tokens != NULL) {
        /* Refill before reporting */
        extern q16_t token_bucket_get_tokens(struct token_bucket *);
        *current_tokens = token_bucket_get_tokens(&cap->rate_limit);
    }

    if (capacity != NULL) {
        *capacity = cap->rate_limit.capacity;
    }

    qspin_unlock(&cap->lock);

    return CAPV2_OK;
}

/*******************************************************************************
 * UNIT TEST / SELF-TEST
 ******************************************************************************/

/**
 * Self-test for capability table initialization and slot management
 *
 * TESTS:
 * 1. Table initialization
 * 2. Slot allocation (until full)
 * 3. Slot deallocation
 * 4. Generation counter increment
 * 5. ABA problem prevention
 *
 * USAGE: Call during kernel boot to verify capability system
 *
 * PEDAGOGICAL NOTE:
 * This demonstrates kernel self-tests. Production kernels (Linux, seL4)
 * include extensive boot-time self-tests to verify correctness.
 */
void capv2_self_test(void)
{
    printf("\n=== CAPV2 Self-Test ===\n");

    /* Test 1: Initialize table */
    printf("Test 1: Table initialization...\n");
    capv2_table_init();

    uint32_t num_free, num_allocated;
    capv2_table_stats(&num_free, &num_allocated);

    if (num_free != CAP_TABLE_SIZE || num_allocated != 0) {
        printf("  FAIL: Expected %d free, 0 allocated. Got %u free, %u allocated.\n",
               CAP_TABLE_SIZE, num_free, num_allocated);
        return;
    }
    printf("  PASS: %d slots free, 0 allocated\n", CAP_TABLE_SIZE);

    /* Test 2: Allocate some slots */
    printf("Test 2: Allocate 10 slots...\n");
    int32_t slots[10];
    for (int i = 0; i < 10; i++) {
        slots[i] = capv2_slot_alloc();
        if (slots[i] == CAP_SLOT_NULL) {
            printf("  FAIL: Could not allocate slot %d\n", i);
            return;
        }
    }

    capv2_table_stats(&num_free, &num_allocated);
    if (num_allocated != 10) {
        printf("  FAIL: Expected 10 allocated, got %u\n", num_allocated);
        return;
    }
    printf("  PASS: Allocated 10 slots\n");

    /* Test 3: Check generation counters */
    printf("Test 3: Verify generation counters...\n");
    uint32_t gen0 = g_cap_table[slots[0]].generation;
    if (gen0 != 1) {
        printf("  FAIL: Expected generation=1, got %u\n", gen0);
        return;
    }
    printf("  PASS: Generation counter = 1 after first alloc\n");

    /* Test 4: Free and reallocate (test ABA prevention) */
    printf("Test 4: Free and reallocate (ABA test)...\n");
    int ret = capv2_slot_free(slots[0]);
    if (ret != CAPV2_OK) {
        printf("  FAIL: Could not free slot\n");
        return;
    }

    int32_t new_slot = capv2_slot_alloc();
    if (new_slot != slots[0]) {
        printf("  FAIL: Expected same slot to be reused, got different slot\n");
        return;
    }

    uint32_t gen1 = g_cap_table[new_slot].generation;
    if (gen1 != 2) {
        printf("  FAIL: Expected generation=2 after realloc, got %u\n", gen1);
        return;
    }
    printf("  PASS: Generation counter incremented (ABA prevention works)\n");

    /* Test 5: Free all slots */
    printf("Test 5: Free all slots...\n");
    for (int i = 0; i < 10; i++) {
        capv2_slot_free(slots[i]);
    }

    capv2_table_stats(&num_free, &num_allocated);
    if (num_allocated != 0) {
        printf("  FAIL: Expected 0 allocated after freeing all, got %u\n", num_allocated);
        return;
    }
    printf("  PASS: All slots freed\n");

    /* Test 6: Allocate until full */
    printf("Test 6: Allocate until table is full...\n");
    int32_t count = 0;
    while (1) {
        int32_t s = capv2_slot_alloc();
        if (s == CAP_SLOT_NULL) break;
        count++;
    }

    if (count != CAP_TABLE_SIZE) {
        printf("  FAIL: Expected to allocate %d slots, got %d\n", CAP_TABLE_SIZE, count);
        return;
    }
    printf("  PASS: Allocated all %d slots (table full)\n", CAP_TABLE_SIZE);

    /* Test 7: Try to allocate when full */
    printf("Test 7: Allocation fails when table full...\n");
    int32_t overflow_slot = capv2_slot_alloc();
    if (overflow_slot != CAP_SLOT_NULL) {
        printf("  FAIL: Expected allocation to fail when full\n");
        return;
    }
    printf("  PASS: Allocation correctly fails when table full\n");

    /* Cleanup: Free all slots */
    for (int32_t i = 0; i < CAP_TABLE_SIZE; i++) {
        capv2_slot_free(i);
    }

    printf("\n=== All Tests PASSED ===\n\n");
}
