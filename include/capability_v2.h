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

struct cap_formula_context;
typedef uint32_t (*cap_formula_t)(struct cap_formula_context *ctx);

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
 * SUCCESS
 * ============================================================================ */

/**
 * Task 2.1.1 Complete!
 *
 * Defined capability_v2 core structure with:
 * - seL4-style core fields (resource_id, owner, refcount, type)
 * - PDAC extensions (8D resource vectors, lambda formulas)
 * - Cap'n Proto metadata (schema_id, buffer)
 * - Token bucket rate limiting
 * - Comprehensive documentation
 *
 * Next: Task 2.1.2 - Define capability table and access API
 */

#endif /* CAPABILITY_V2_H */
