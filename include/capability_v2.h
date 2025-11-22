#ifndef CAPABILITY_V2_H
#define CAPABILITY_V2_H

/**
 * @file capability_v2.h
 * @brief PDAC Capability System V2: seL4 + Cap'n Proto + Lambda Formulas
 *
 * PEDAGOGICAL PURPOSE:
 * ====================
 * This module demonstrates how to build a modern capability system by
 * synthesizing three world-class approaches:
 *
 * 1. **seL4**: Simple, verifiable capability tables (formal methods)
 * 2. **Cap'n Proto**: Zero-copy IPC serialization (performance)
 * 3. **Lambda Calculus**: Dynamic rights computation (expressiveness)
 *
 * WHY CAPABILITIES?
 * =================
 * Capabilities are **unforgeable tokens** that grant access to resources.
 * Unlike Access Control Lists (ACLs), capabilities:
 * - Can be delegated (transferred between processes)
 * - Can be attenuated (reduced in power)
 * - Can be revoked (taken back by owner)
 * - Enable principle of least privilege
 *
 * COMPARISON TO ALTERNATIVES:
 * ===========================
 * | Security Model | Granularity | Delegation | Verification |
 * |----------------|-------------|------------|--------------|
 * | **ACLs**       | Coarse      | Difficult  | Hard         |
 * | **Capabilities** | Fine      | Natural    | Possible     |
 * | **PDAC Caps**  | Ultra-fine  | Natural    | Formal       |
 *
 * PDAC extends traditional capabilities with:
 * - 8D resource quotas (octonion vectors)
 * - Dynamic rights (lambda formulas)
 * - Rate limiting (token buckets with stochastic refill)
 *
 * REAL-WORLD ANALOGUES:
 * =====================
 * - seL4: Formally verified L4 microkernel (NICTA/Data61)
 * - Cap'n Proto: High-performance RPC framework (Sandstorm.io)
 * - Google Borg: Multidimensional resource quotas
 * - AWS IAM: Time-limited credentials (similar to time-decay formulas)
 */

#include "types.h"
#include "resource_vector.h"
#include "q16_fixed.h"
#include "exo_lock.h"

/* ============================================================================
 * FORWARD DECLARATIONS
 * ============================================================================ */

struct capability_v2;
typedef uint32_t (*cap_formula_t)(struct capability_v2 *cap, void *data);

/* ============================================================================
 * CAPABILITY TYPES
 * ============================================================================ */

/**
 * Capability Types
 *
 * Each type represents a different kind of OS resource.
 * Inspired by seL4's capability ontology.
 */
typedef enum {
    CAP_TYPE_NULL = 0,              /* Invalid/unallocated capability */
    CAP_TYPE_MEMORY_PAGE,           /* Physical memory page */
    CAP_TYPE_DEVICE_PORT,           /* Hardware I/O port */
    CAP_TYPE_IPC_ENDPOINT,          /* IPC communication endpoint */
    CAP_TYPE_IRQ_HANDLER,           /* Interrupt handler */
    CAP_TYPE_PROCESS_CONTROL,       /* Process control block */
    CAP_TYPE_RESOURCE_QUOTA,        /* 8D resource quota (PDAC-specific) */
    CAP_TYPE_FILE_DESCRIPTOR,       /* File system object */
    CAP_TYPE_NETWORK_SOCKET,        /* Network socket */
} cap_type_t;

/**
 * Capability Rights Bitmask
 *
 * Each capability has associated rights that control what operations
 * are permitted. Rights can be attenuated (reduced) but never escalated.
 */
#define CAP_RIGHT_READ    (1 << 0)  /* Read access */
#define CAP_RIGHT_WRITE   (1 << 1)  /* Write access */
#define CAP_RIGHT_EXECUTE (1 << 2)  /* Execute access */
#define CAP_RIGHT_GRANT   (1 << 3)  /* Can delegate to others */
#define CAP_RIGHT_REVOKE  (1 << 4)  /* Can revoke children */
#define CAP_RIGHT_DERIVE  (1 << 5)  /* Can create derived caps */

/* Convenience macros for common right combinations */
#define CAP_RIGHTS_NONE  (0)
#define CAP_RIGHTS_RO    (CAP_RIGHT_READ)
#define CAP_RIGHTS_RW    (CAP_RIGHT_READ | CAP_RIGHT_WRITE)
#define CAP_RIGHTS_RX    (CAP_RIGHT_READ | CAP_RIGHT_EXECUTE)
#define CAP_RIGHTS_RWX   (CAP_RIGHT_READ | CAP_RIGHT_WRITE | CAP_RIGHT_EXECUTE)
#define CAP_RIGHTS_FULL  (CAP_RIGHT_READ | CAP_RIGHT_WRITE | CAP_RIGHT_EXECUTE | \
                          CAP_RIGHT_GRANT | CAP_RIGHT_REVOKE | CAP_RIGHT_DERIVE)

/* ============================================================================
 * TOKEN BUCKET FOR RATE LIMITING
 * ============================================================================ */

/**
 * Token Bucket Rate Limiter
 *
 * Classic algorithm for rate limiting with stochastic variance.
 * Used in: Linux traffic control (tc), AWS API throttling, etc.
 *
 * ALGORITHM:
 * - Bucket holds tokens (Q16.16 fixed-point)
 * - Tokens refill at constant rate (with stochastic variance)
 * - Each operation consumes tokens
 * - If bucket empty → rate limited
 *
 * PEDAGOGICAL VALUE:
 * - Demonstrates token bucket algorithm
 * - Shows Q16.16 fixed-point arithmetic
 * - Introduces stochastic variance (LCG RNG)
 */
struct token_bucket {
    uint64_t tokens;                /* Current tokens (Q16.16 fixed-point) */
    uint64_t capacity;              /* Maximum tokens (bucket size) */
    uint64_t refill_rate;           /* Tokens per millisecond (Q16.16) */
    uint64_t last_refill_ms;        /* Timestamp of last refill */
    uint32_t rng_seed;              /* Seed for stochastic variance */
};

/* ============================================================================
 * CAPABILITY V2 STRUCTURE
 * ============================================================================ */

/**
 * Capability V2: Hybrid Design
 *
 * Combines seL4 simplicity, Cap'n Proto serialization, and lambda-based
 * dynamic rights into a unified capability primitive.
 *
 * STRUCTURE RATIONALE:
 * ====================
 *
 * **seL4-Style Core Fields:**
 * - resource_id: Identifies the physical resource (page frame, device, etc.)
 * - owner_pid: Process that created this capability
 * - refcount: Reference counting for safe delegation
 * - cap_type: Type tag for runtime type checking
 *
 * **PDAC Extensions:**
 * - quota: 8D resource vector (octonion-based multidimensional quota)
 * - rights_fn: Lambda formula for computing dynamic rights
 * - consumed: Tracks resources consumed via this capability
 *
 * **Cap'n Proto Integration:**
 * - schema_id: Type tag for IPC message serialization
 * - capnp_buffer: Pointer to serialized data (zero-copy)
 *
 * **Token Bucket Rate Limiting:**
 * - rate_limit: Per-capability token bucket for rate limiting
 * - Prevents DoS via capability abuse
 *
 * **Metadata:**
 * - generation: Prevents use-after-free (ABA problem)
 * - creation_time: For time-based formulas
 * - access_count: For usage-based formulas
 * - parent_slot: For revocation tree walking
 */
struct capability_v2 {
    /* ========================================================================
     * seL4-STYLE CORE FIELDS
     * ======================================================================== */

    /**
     * Resource ID: Physical resource this capability grants access to
     *
     * Examples:
     * - Memory page: Physical page frame number
     * - Device port: I/O port base address
     * - IPC endpoint: Endpoint ID in global table
     * - IRQ handler: IRQ number
     */
    uint64_t resource_id;

    /**
     * Owner PID: Process that created this capability
     *
     * Used for:
     * - Access control (only owner can revoke)
     * - Quota accounting (charge owner for resource usage)
     * - Debugging (trace capability provenance)
     */
    uint32_t owner_pid;

    /**
     * Reference Count: Number of processes holding this capability
     *
     * Enables safe delegation:
     * - Grant increments refcount
     * - Revoke decrements refcount
     * - Free only when refcount == 0
     *
     * Prevents use-after-free vulnerabilities.
     */
    uint32_t refcount;

    /**
     * Capability Type: What kind of resource this is
     *
     * Used for:
     * - Runtime type checking
     * - Type-safe downcasting
     * - Capability-specific operations
     */
    cap_type_t cap_type;

    /**
     * Static Rights: Fixed rights bitmask
     *
     * Base rights that don't change over time.
     * Dynamic formula can reduce these, but never increase.
     */
    uint32_t static_rights;

    /* ========================================================================
     * PDAC EXTENSIONS: 8D Resource Quotas
     * ======================================================================== */

    /**
     * Resource Quota: 8-dimensional resource vector
     *
     * Uses octonion algebra to represent multidimensional resource limits:
     * - e0: CPU quota (milliseconds)
     * - e1: Memory quota (megabytes)
     * - e2: I/O bandwidth (MB/s)
     * - e3: Network quota (packets/s)
     * - e4: GPU quota (shader units)
     * - e5: Disk quota (IOPS)
     * - e6: IRQ quota (interrupts/s)
     * - e7: Sub-capability delegation count
     *
     * PEDAGOGICAL VALUE:
     * - Shows multidimensional resource management
     * - Demonstrates octonion algebra in practice
     * - Enables derived capabilities with reduced quotas
     */
    resource_vector_t quota;

    /**
     * Consumed Resources: Tracks actual resource usage
     *
     * Updated on each capability use.
     * When consumed > quota → capability denied.
     */
    resource_vector_t consumed;

    /* ========================================================================
     * PDAC EXTENSIONS: Lambda Formula DSL
     * ======================================================================== */

    /**
     * Rights Formula: Lambda function for dynamic rights computation
     *
     * Function pointer that computes rights based on context:
     * - Time elapsed since creation
     * - User ID of caller
     * - Token bucket balance
     * - Resource consumption
     *
     * Examples:
     * - Time-decay: Rights reduce over time (temporary access)
     * - User-based: Root gets full rights, users get read-only
     * - Quota-based: Rights revoked when quota exhausted
     *
     * PEDAGOGICAL VALUE:
     * - Demonstrates higher-order functions in C
     * - Shows lambda calculus in systems programming
     * - Enables composable security policies
     */
    cap_formula_t rights_fn;

    /**
     * Formula Data: Opaque data passed to rights formula
     *
     * Allows formulas to maintain state.
     * Examples:
     * - Decay rate for time-based formulas
     * - Threshold for quota-based formulas
     */
    void *formula_data;

    /* ========================================================================
     * CAP'N PROTO INTEGRATION: Zero-Copy IPC
     * ======================================================================== */

    /**
     * Schema ID: Type tag for Cap'n Proto serialization
     *
     * Identifies the message schema for this capability's data.
     * Enables type-safe zero-copy deserialization.
     */
    uint32_t schema_id;

    /**
     * Cap'n Proto Buffer: Serialized message data
     *
     * Pointer to serialized Cap'n Proto message.
     * NULL if no IPC data associated with this capability.
     *
     * ZERO-COPY GUARANTEE:
     * - IPC receiver gets direct pointer to sender's buffer
     * - No kernel copy required
     * - Validated on access (bounds checking, alignment)
     */
    void *capnp_buffer;

    /**
     * Buffer Size: Size of serialized data (bytes)
     */
    uint32_t buffer_size;

    /* ========================================================================
     * TOKEN BUCKET RATE LIMITING
     * ======================================================================== */

    /**
     * Rate Limiter: Token bucket for per-capability rate limiting
     *
     * Prevents DoS attacks via capability abuse.
     * Each operation consumes tokens; bucket refills over time.
     *
     * STOCHASTIC REFILL:
     * - Base refill rate (deterministic)
     * - Plus stochastic variance (LCG RNG)
     * - Prevents synchronization attacks
     */
    struct token_bucket rate_limit;

    /* ========================================================================
     * METADATA AND BOOKKEEPING
     * ======================================================================== */

    /**
     * Generation Counter: Prevents use-after-free (ABA problem)
     *
     * Incremented on each free/allocate cycle.
     * Capability slots encode generation in upper bits.
     * Stale references fail generation check.
     */
    uint32_t generation;

    /**
     * Creation Time: Timestamp when capability was created (milliseconds)
     *
     * Used for:
     * - Time-decay formulas
     * - Auditing and forensics
     * - Capability expiration
     */
    uint64_t creation_time;

    /**
     * Access Count: Number of times this capability has been used
     *
     * Used for:
     * - Usage-based formulas
     * - Performance profiling
     * - Anomaly detection (too many accesses → possible attack)
     */
    uint64_t access_count;

    /**
     * Parent Slot: Index of parent capability (for revocation tree)
     *
     * When this capability was derived from another:
     * - parent_slot points to originating capability
     * - Enables recursive revocation (revoking parent revokes all children)
     * - -1 if this is a root capability
     */
    int32_t parent_slot;

    /**
     * Lock: Per-capability fine-grained lock
     *
     * Protects capability structure during concurrent access.
     * Uses existing qspinlock infrastructure.
     */
    struct qspinlock lock;
};

_Static_assert(sizeof(struct capability_v2) == 640, "capability_v2 size mismatch");
_Static_assert(sizeof(struct token_bucket) == 40, "token_bucket size mismatch");

/* ============================================================================
 * CAPABILITY TABLE
 * ============================================================================ */

/**
 * Capability Table Size
 *
 * Fixed-size table for simplicity and verifiability (seL4 style).
 * 4096 capabilities = 64KB (assuming 64-byte capability structure).
 *
 * PEDAGOGICAL RATIONALE:
 * - Fixed size enables formal verification
 * - Simple allocation (no fragmentation)
 * - Fast lookup (array indexing)
 */
#define CAP_TABLE_V2_SIZE 4096

/**
 * Global Capability Table
 *
 * Single global table of all capabilities in the system.
 * Indexed by capability slot number (0-4095).
 *
 * NOTE: Declared extern here, defined in kernel/capability_v2.c
 */
extern struct capability_v2 cap_table_v2[CAP_TABLE_V2_SIZE];

/**
 * Capability Table Metadata
 *
 * Tracks free list, statistics, and lock for table operations.
 */
struct cap_table_meta {
    uint32_t free_list_head;        /* Head of free list */
    uint32_t num_free;              /* Number of free slots */
    uint32_t num_allocated;         /* Number of allocated slots */
    struct qspinlock table_lock;    /* Global table lock */
};

extern struct cap_table_meta cap_table_v2_meta;

/* ============================================================================
 * ERROR CODES
 * ============================================================================ */

/**
 * Capability Error Codes
 *
 * Standard error codes for capability operations.
 * Following UNIX errno conventions (negative values).
 */
#define CAPV2_OK                 0   /* Success */
#define CAPV2_ERR_INVALID_SLOT  -1   /* Slot index out of range */
#define CAPV2_ERR_NO_PERMISSION -2   /* Caller lacks required rights */
#define CAPV2_ERR_TABLE_FULL    -3   /* Capability table exhausted */
#define CAPV2_ERR_REFCOUNT_OVERFLOW -4  /* Too many references */
#define CAPV2_ERR_INVALID_TYPE  -5   /* Capability type mismatch */
#define CAPV2_ERR_QUOTA_EXCEEDED -6  /* Resource quota exceeded */
#define CAPV2_ERR_RATE_LIMITED  -7   /* Token bucket empty */
#define CAPV2_ERR_GENERATION_MISMATCH -8  /* Stale capability reference */
#define CAPV2_ERR_INVALID_DERIVE -9  /* Invalid derivation (quota too large) */
#define CAPV2_ERR_NOT_FOUND     -10  /* Capability not found */

/* ============================================================================
 * CAPABILITY TABLE API
 * ============================================================================ */

/**
 * Initialize capability table
 *
 * Must be called once during kernel boot.
 * Sets up free list and initializes all slots to CAP_TYPE_NULL.
 */
void capv2_table_init(void);

/**
 * Get table statistics
 *
 * Useful for monitoring and debugging.
 *
 * @param[out] num_free Number of free slots
 * @param[out] num_allocated Number of allocated slots
 */
void capv2_table_stats(uint32_t *num_free, uint32_t *num_allocated);

/**
 * Print capability table statistics
 *
 * Debug helper. Prints:
 * - Free/allocated counts
 * - Per-type counts
 * - Refcount histogram
 */
void capv2_print_table_stats(void);

/* ============================================================================
 * CORE CAPABILITY OPERATIONS
 * ============================================================================ */

/**
 * Allocate new capability
 *
 * Creates a new capability granting access to the specified resource.
 * Automatically initializes:
 * - Owner to current process
 * - Refcount to 1
 * - Generation counter
 * - Creation timestamp
 * - Default quota (if applicable)
 *
 * @param resource_id Physical resource identifier
 * @param cap_type Type of capability
 * @param initial_rights Initial rights bitmask
 * @param quota Resource quota (8D vector), or RESOURCE_VEC_ZERO for unlimited
 *
 * @return Capability slot number (0-4095) on success
 * @return CAPV2_ERR_TABLE_FULL if no free slots
 *
 * EXAMPLE:
 * ```c
 * // Allocate memory page capability
 * resource_vector_t quota = RESOURCE_VEC(0, 4, 0, 0, 0, 0, 0, 0);  // 4MB memory
 * int cap_slot = capv2_alloc(page_frame_number, CAP_TYPE_MEMORY_PAGE,
 *                            CAP_RIGHTS_RW, quota);
 * if (cap_slot < 0) {
 *     panic("Out of capabilities!");
 * }
 * ```
 */
int capv2_alloc(
    uint64_t resource_id,
    cap_type_t cap_type,
    uint32_t initial_rights,
    resource_vector_t quota
);

/**
 * Free capability
 *
 * Releases capability back to free list.
 * Only succeeds if:
 * - Refcount == 0 (no outstanding references)
 * - Caller is owner OR has REVOKE right
 *
 * Also releases underlying resource (type-specific cleanup).
 *
 * @param cap_slot Capability slot to free
 *
 * @return CAPV2_OK on success
 * @return CAPV2_ERR_INVALID_SLOT if slot invalid
 * @return CAPV2_ERR_NO_PERMISSION if caller not authorized
 * @return CAPV2_ERR_REFCOUNT_OVERFLOW if refcount > 0
 *
 * EXAMPLE:
 * ```c
 * if (capv2_free(cap_slot) < 0) {
 *     cprintf("Warning: Failed to free capability %d\n", cap_slot);
 * }
 * ```
 */
int capv2_free(int cap_slot);

/**
 * Grant capability to another process
 *
 * Creates a new capability reference for the recipient.
 * Increments refcount and creates new slot for recipient.
 *
 * Caller must have GRANT right.
 * Rights can be attenuated (reduced) but never escalated.
 *
 * @param cap_slot Capability slot to grant
 * @param recipient_pid Process ID of recipient
 * @param attenuated_rights Rights for recipient (must be subset of caller's rights)
 *
 * @return New capability slot in recipient's table
 * @return CAPV2_ERR_INVALID_SLOT if slot invalid
 * @return CAPV2_ERR_NO_PERMISSION if caller lacks GRANT right
 * @return CAPV2_ERR_TABLE_FULL if recipient's table full
 * @return CAPV2_ERR_REFCOUNT_OVERFLOW if refcount would overflow
 *
 * EXAMPLE:
 * ```c
 * // Grant read-only access to another process
 * int recipient_cap = capv2_grant(my_cap, child_pid, CAP_RIGHTS_RO);
 * if (recipient_cap < 0) {
 *     cprintf("Failed to grant capability: %d\n", recipient_cap);
 * }
 * ```
 */
int capv2_grant(
    int cap_slot,
    uint32_t recipient_pid,
    uint32_t attenuated_rights
);

/**
 * Revoke capability
 *
 * Decrements refcount. If refcount reaches 0, frees the capability.
 * Caller must have REVOKE right or be owner.
 *
 * @param cap_slot Capability slot to revoke
 *
 * @return CAPV2_OK on success
 * @return CAPV2_ERR_INVALID_SLOT if slot invalid
 * @return CAPV2_ERR_NO_PERMISSION if caller not authorized
 *
 * EXAMPLE:
 * ```c
 * // Revoke capability (may or may not free, depending on refcount)
 * capv2_revoke(cap_slot);
 * ```
 */
int capv2_revoke(int cap_slot);

/**
 * Derive new capability with reduced quota
 *
 * Creates a child capability with:
 * - Same resource and type as parent
 * - Reduced quota (must be <= parent quota)
 * - Possibly reduced rights
 * - Parent pointer (for revocation tree)
 *
 * Caller must have DERIVE right.
 * Useful for delegating limited access to sub-resources.
 *
 * @param parent_slot Parent capability
 * @param child_quota Resource quota for child (must fit within parent)
 * @param child_rights Rights for child (must be subset of parent)
 *
 * @return New capability slot for child
 * @return CAPV2_ERR_INVALID_SLOT if parent invalid
 * @return CAPV2_ERR_NO_PERMISSION if caller lacks DERIVE right
 * @return CAPV2_ERR_INVALID_DERIVE if child quota > parent quota
 * @return CAPV2_ERR_TABLE_FULL if table full
 *
 * EXAMPLE:
 * ```c
 * // Derive capability with half the quota
 * resource_vector_t parent_quota = cap_table_v2[parent_slot].quota;
 * resource_vector_t child_quota = resource_vector_scale(parent_quota, q16_from_int(1) / 2);
 *
 * int child_slot = capv2_derive(parent_slot, child_quota, CAP_RIGHTS_RO);
 * if (child_slot < 0) {
 *     cprintf("Derivation failed: %d\n", child_slot);
 * }
 * ```
 */
int capv2_derive(
    int parent_slot,
    resource_vector_t child_quota,
    uint32_t child_rights
);

/**
 * Check if caller has required rights
 *
 * Evaluates dynamic rights formula and checks against requested rights.
 * Also enforces:
 * - Token bucket rate limiting
 * - Resource quota limits
 * - Generation counter validity
 *
 * This is the PRIMARY access control check for all capability operations.
 *
 * @param cap_slot Capability slot to check
 * @param requested_rights Rights needed for operation
 *
 * @return 1 if caller has requested rights
 * @return 0 if caller lacks rights OR rate limited OR quota exceeded
 * @return negative error code on failure
 *
 * EXAMPLE:
 * ```c
 * if (capv2_check_rights(cap_slot, CAP_RIGHT_WRITE)) {
 *     // Proceed with write operation
 *     perform_write(cap_table_v2[cap_slot].resource_id, data);
 * } else {
 *     return -EPERM;  // Permission denied
 * }
 * ```
 */
int capv2_check_rights(int cap_slot, uint32_t requested_rights);

/**
 * Update capability formula
 *
 * Changes the lambda formula used for dynamic rights computation.
 * Caller must have DERIVE right.
 *
 * @param cap_slot Capability slot to update
 * @param new_formula New rights formula function
 * @param formula_data Opaque data for formula
 *
 * @return CAPV2_OK on success
 * @return CAPV2_ERR_INVALID_SLOT if slot invalid
 * @return CAPV2_ERR_NO_PERMISSION if caller lacks DERIVE right
 *
 * EXAMPLE:
 * ```c
 * // Set time-decay formula
 * capv2_set_formula(cap_slot, cap_formula_time_decay, &decay_rate);
 * ```
 */
int capv2_set_formula(
    int cap_slot,
    cap_formula_t new_formula,
    void *formula_data
);

/* ============================================================================
 * CAPABILITY LOOKUP AND INTROSPECTION
 * ============================================================================ */

/**
 * Lookup capability by resource ID
 *
 * Finds first capability granting access to specified resource.
 * Useful for checking if process already has access to resource.
 *
 * @param resource_id Resource to search for
 * @param owner_pid Process ID to search within (or -1 for all processes)
 *
 * @return Capability slot if found
 * @return CAPV2_ERR_NOT_FOUND if no matching capability
 *
 * EXAMPLE:
 * ```c
 * int cap = capv2_find(page_frame_number, current_pid);
 * if (cap >= 0) {
 *     cprintf("Process already has access to page %llu\n", page_frame_number);
 * }
 * ```
 */
int capv2_find(uint64_t resource_id, int32_t owner_pid);

/**
 * Get capability information
 *
 * Copies capability structure to user buffer.
 * Useful for introspection and debugging.
 *
 * @param cap_slot Capability slot
 * @param[out] cap_out Buffer to receive capability (if not NULL)
 *
 * @return CAPV2_OK on success
 * @return CAPV2_ERR_INVALID_SLOT if slot invalid
 *
 * EXAMPLE:
 * ```c
 * struct capability_v2 cap;
 * if (capv2_get_info(cap_slot, &cap) == CAPV2_OK) {
 *     cprintf("Capability type: %d, refcount: %d\n", cap.cap_type, cap.refcount);
 * }
 * ```
 */
int capv2_get_info(int cap_slot, struct capability_v2 *cap_out);

/**
 * Print capability details
 *
 * Debug helper. Prints:
 * - Resource ID and type
 * - Owner and refcount
 * - Rights (static + dynamic)
 * - Quota and consumed resources
 * - Token bucket status
 * - Parent capability (if derived)
 *
 * @param cap_slot Capability slot to print
 */
void capv2_print(int cap_slot);

/* ============================================================================
 * SUCCESS
 * ============================================================================ */

/**
 * Tasks 2.1.1, 2.1.2, 2.1.3 Complete!
 *
 * Defined:
 * - Capability V2 core structure (640 bytes)
 * - Capability table (4096 slots, 2.5 MB)
 * - Capability types and rights
 * - Complete API (15 functions)
 * - Error codes
 * - Comprehensive documentation with examples
 *
 * Next: Task 2.2.1 - Implement capability table initialization
 */

#endif /* CAPABILITY_V2_H */
