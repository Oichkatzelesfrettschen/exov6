#pragma once

/**
 * @file resource_vector.h
 * @brief 8D Resource Vectors using Octonion Algebra (PDAC Framework)
 *
 * PEDAGOGICAL PURPOSE:
 * ====================
 * This module demonstrates how exotic mathematics (octonions) can be
 * applied to practical OS problems (multidimensional resource management).
 *
 * WHY OCTONIONS FOR RESOURCES?
 * =============================
 * 1. **8 Dimensions**: Perfect for 8 resource types (CPU, memory, I/O, etc.)
 * 2. **Non-Associativity**: Models path-dependent resource allocation in DAGs
 * 3. **Zero Divisors**: Detects resource deadlocks (orthogonal requirements)
 * 4. **Norm Function**: Provides scalar priority from vector (for scheduling)
 *
 * COMPARISON TO ALTERNATIVES:
 * ===========================
 * - **Arrays**: No algebraic structure, manual composition logic
 * - **Complex Numbers**: Only 2D, insufficient for modern resources
 * - **Quaternions**: Only 4D, still insufficient
 * - **Octonions**: 8D with rich algebraic properties
 *
 * REAL-WORLD ANALOGUES:
 * =====================
 * - Google Borg: Multidimensional resource vectors (custom algebra)
 * - Kubernetes: Resource quotas (CPU + memory, limited to 2D)
 * - Mesos: Dominant Resource Fairness (DRF) - scalar approximation
 *
 * PDAC extends these to full 8D with formal algebraic guarantees.
 */

#include "q16_fixed.h"
#include "q16_octonion.h"

/* ============================================================================
 * 8D RESOURCE VECTOR TYPE DEFINITIONS
 * ============================================================================ */

/**
 * Resource Vector: 8-dimensional resource quotas
 *
 * Implementation uses q16_octonion_t (Q16.16 fixed-point octonion)
 * Each component represents a different OS resource type.
 */
typedef q16_octonion_t resource_vector_t;

/**
 * Resource Type Enumeration
 */
typedef enum {
    RESOURCE_TYPE_CPU = 0,        /* e0: CPU time (milliseconds) */
    RESOURCE_TYPE_MEMORY = 1,     /* e1: Memory (megabytes) */
    RESOURCE_TYPE_IO = 2,         /* e2: I/O bandwidth (MB/s) */
    RESOURCE_TYPE_NETWORK = 3,    /* e3: Network (packets/s) */
    RESOURCE_TYPE_GPU = 4,        /* e4: GPU shader units */
    RESOURCE_TYPE_DISK = 5,       /* e5: Disk I/O (IOPS) */
    RESOURCE_TYPE_IRQ = 6,        /* e6: Interrupt budget (IRQs/s) */
    RESOURCE_TYPE_CAPS = 7,       /* e7: Capability delegation count */
} resource_type_t;

/* ============================================================================
 * RESOURCE VECTOR CREATION MACROS
 * ============================================================================ */

/**
 * Create resource component from integer
 * (Converts to Q16.16 fixed-point)
 */
#define RESOURCE_COMPONENT(x) Q16_FROM_INT(x)

/**
 * Create resource vector with all 8 dimensions
 *
 * Example:
 *   resource_vector_t web_server = RESOURCE_VEC(
 *       100,  // 100ms CPU
 *       512,  // 512MB RAM
 *       10,   // 10 MB/s I/O
 *       1000, // 1000 packets/s network
 *       0,    // No GPU
 *       100,  // 100 IOPS disk
 *       50,   // 50 IRQs/s
 *       10    // 10 delegated capabilities
 *   );
 */
#define RESOURCE_VEC(cpu, mem, io, net, gpu, disk, irq, caps) \
    ((resource_vector_t){ \
        .e0 = RESOURCE_COMPONENT(cpu), \
        .e1 = RESOURCE_COMPONENT(mem), \
        .e2 = RESOURCE_COMPONENT(io), \
        .e3 = RESOURCE_COMPONENT(net), \
        .e4 = RESOURCE_COMPONENT(gpu), \
        .e5 = RESOURCE_COMPONENT(disk), \
        .e6 = RESOURCE_COMPONENT(irq), \
        .e7 = RESOURCE_COMPONENT(caps) \
    })

/**
 * Predefined resource vector templates
 */
#define RESOURCE_VEC_ZERO  RESOURCE_VEC(0, 0, 0, 0, 0, 0, 0, 0)
#define RESOURCE_VEC_CPU_INTENSIVE  RESOURCE_VEC(1000, 64, 0, 0, 0, 0, 0, 0)
#define RESOURCE_VEC_MEMORY_INTENSIVE  RESOURCE_VEC(10, 4096, 0, 0, 0, 0, 0, 0)
#define RESOURCE_VEC_IO_INTENSIVE  RESOURCE_VEC(10, 64, 1000, 0, 0, 1000, 0, 0)
#define RESOURCE_VEC_NETWORK_INTENSIVE  RESOURCE_VEC(10, 64, 100, 10000, 0, 0, 100, 0)
#define RESOURCE_VEC_BALANCED  RESOURCE_VEC(100, 512, 50, 1000, 0, 100, 50, 10)

/* ============================================================================
 * RESOURCE VECTOR OPERATIONS
 * ============================================================================ */

/**
 * Add two resource vectors (component-wise)
 *
 * Use case: Combine resource requirements from multiple tasks
 */
static inline resource_vector_t resource_vector_add(
    resource_vector_t a,
    resource_vector_t b
) {
    return q16_octonion_add(a, b);
}

/**
 * Subtract resource vectors (component-wise)
 *
 * Use case: Compute remaining quota after allocation
 */
static inline resource_vector_t resource_vector_sub(
    resource_vector_t a,
    resource_vector_t b
) {
    return q16_octonion_sub(a, b);
}

/**
 * Compose resource vectors using octonion multiplication
 *
 * **NON-ASSOCIATIVE**: (a * b) * c ≠ a * (b * c)
 *
 * Use case: Model path-dependent resource allocation in DAG scheduling
 *
 * Example:
 *   Task A → Task B → Task C
 *   vs.
 *   Task A → (Task B → Task C)
 *
 *   Different orderings may have different resource implications!
 */
static inline resource_vector_t resource_vector_compose(
    resource_vector_t a,
    resource_vector_t b
) {
    return q16_octonion_mul(a, b);
}

/**
 * Get total resource pressure (scalar)
 *
 * Returns: Euclidean norm in 8D space
 *
 * Use case: Scheduler priority (higher norm = higher priority)
 */
static inline q16_t resource_vector_norm(resource_vector_t v) {
    return q16_octonion_norm(v);
}

/**
 * Get squared norm (faster, no square root)
 *
 * Use case: Relative comparisons (order preserved)
 */
static inline q16_t resource_vector_norm_squared(resource_vector_t v) {
    return q16_octonion_norm_squared(v);
}

/**
 * Check if resource vectors are orthogonal (DEADLOCK DETECTION)
 *
 * Returns: 1 if vectors are orthogonal (potential deadlock), 0 otherwise
 *
 * **ZERO DIVISOR PROPERTY**:
 * In octonions, non-zero elements can multiply to zero.
 * This detects resource conflicts!
 *
 * Example:
 *   Task A needs: CPU only (high CPU, zero memory)
 *   Task B needs: Memory only (zero CPU, high memory)
 *   Composition result ≈ zero → DEADLOCK (waiting for exclusive resources)
 */
static inline int resource_vector_is_orthogonal(
    resource_vector_t a,
    resource_vector_t b
) {
    resource_vector_t product = resource_vector_compose(a, b);
    q16_t norm = resource_vector_norm(product);

    /* Threshold: norm < 0.01 in Q16.16 = 655 */
    #define ORTHOGONAL_THRESHOLD (Q16_ONE / 100)

    return (norm < ORTHOGONAL_THRESHOLD) ? 1 : 0;
}

/**
 * Scale resource vector by scalar
 *
 * Use case: Multiply quota by percentage (e.g., 50% of quota)
 */
static inline resource_vector_t resource_vector_scale(
    resource_vector_t v,
    q16_t scalar
) {
    return q16_octonion_scale(v, scalar);
}

/**
 * Compare resource vectors (component-wise ≤)
 *
 * Returns: 1 if a ≤ b for all components, 0 otherwise
 *
 * Use case: Check if task requirements fit within quota
 */
static inline int resource_vector_fits(
    resource_vector_t required,
    resource_vector_t available
) {
    /* Check each component */
    return (required.e0 <= available.e0 &&
            required.e1 <= available.e1 &&
            required.e2 <= available.e2 &&
            required.e3 <= available.e3 &&
            required.e4 <= available.e4 &&
            required.e5 <= available.e5 &&
            required.e6 <= available.e6 &&
            required.e7 <= available.e7);
}

/* ============================================================================
 * RESOURCE ACCOUNTING FUNCTIONS
 * ============================================================================ */

/**
 * Allocate resources from quota
 *
 * Returns: 1 if allocation succeeds, 0 if insufficient resources
 *
 * Updates quota by subtracting required resources
 */
static inline int resource_vector_allocate(
    resource_vector_t *quota,
    resource_vector_t required
) {
    if (!resource_vector_fits(required, *quota)) {
        return 0;  /* Allocation failed: insufficient resources */
    }

    *quota = resource_vector_sub(*quota, required);
    return 1;  /* Success */
}

/**
 * Release resources back to quota
 *
 * Use case: Task completion, resource cleanup
 */
static inline void resource_vector_release(
    resource_vector_t *quota,
    resource_vector_t released
) {
    *quota = resource_vector_add(*quota, released);
}

/* ============================================================================
 * DEBUGGING AND VISUALIZATION
 * ============================================================================ */

/**
 * Convert resource vector to human-readable string
 *
 * Format: "[CPU:100ms MEM:512MB IO:10MB/s NET:1000pps GPU:0 DISK:100iops IRQ:50/s CAPS:10]"
 */
const char* resource_vector_to_string(resource_vector_t v);

/**
 * Print resource vector to console (for debugging)
 */
void resource_vector_print(resource_vector_t v, const char *label);

/**
 * Get single component from resource vector
 */
static inline q16_t resource_vector_get(
    resource_vector_t v,
    resource_type_t type
) {
    switch (type) {
        case RESOURCE_TYPE_CPU:     return v.e0;
        case RESOURCE_TYPE_MEMORY:  return v.e1;
        case RESOURCE_TYPE_IO:      return v.e2;
        case RESOURCE_TYPE_NETWORK: return v.e3;
        case RESOURCE_TYPE_GPU:     return v.e4;
        case RESOURCE_TYPE_DISK:    return v.e5;
        case RESOURCE_TYPE_IRQ:     return v.e6;
        case RESOURCE_TYPE_CAPS:    return v.e7;
        default:                    return 0;
    }
}

/**
 * Set single component in resource vector
 */
static inline void resource_vector_set(
    resource_vector_t *v,
    resource_type_t type,
    q16_t value
) {
    switch (type) {
        case RESOURCE_TYPE_CPU:     v->e0 = value; break;
        case RESOURCE_TYPE_MEMORY:  v->e1 = value; break;
        case RESOURCE_TYPE_IO:      v->e2 = value; break;
        case RESOURCE_TYPE_NETWORK: v->e3 = value; break;
        case RESOURCE_TYPE_GPU:     v->e4 = value; break;
        case RESOURCE_TYPE_DISK:    v->e5 = value; break;
        case RESOURCE_TYPE_IRQ:     v->e6 = value; break;
        case RESOURCE_TYPE_CAPS:    v->e7 = value; break;
    }
}

/* ============================================================================
 * PEDAGOGICAL EXAMPLES
 * ============================================================================ */

#ifdef RESOURCE_VECTOR_EXAMPLES

/**
 * Example 1: Detect resource deadlock using zero divisors
 */
void example_deadlock_detection(void) {
    /* Task A: CPU-intensive (high CPU, low everything else) */
    resource_vector_t task_a = RESOURCE_VEC(1000, 10, 0, 0, 0, 0, 0, 0);

    /* Task B: Memory-intensive (low CPU, high memory) */
    resource_vector_t task_b = RESOURCE_VEC(10, 4096, 0, 0, 0, 0, 0, 0);

    /* Check for deadlock */
    if (resource_vector_is_orthogonal(task_a, task_b)) {
        cprintf("WARNING: Tasks have orthogonal resources - potential deadlock!\n");
    }
}

/**
 * Example 2: Non-associative path composition
 */
void example_path_dependence(void) {
    resource_vector_t task_a = RESOURCE_VEC(100, 512, 10, 100, 0, 10, 5, 1);
    resource_vector_t task_b = RESOURCE_VEC(200, 256, 20, 200, 0, 20, 10, 2);
    resource_vector_t task_c = RESOURCE_VEC(150, 384, 15, 150, 0, 15, 7, 1);

    /* Path 1: (A → B) → C */
    resource_vector_t path1 = resource_vector_compose(
        resource_vector_compose(task_a, task_b),
        task_c
    );

    /* Path 2: A → (B → C) */
    resource_vector_t path2 = resource_vector_compose(
        task_a,
        resource_vector_compose(task_b, task_c)
    );

    /* Compare norms (path-dependent!) */
    q16_t norm1 = resource_vector_norm(path1);
    q16_t norm2 = resource_vector_norm(path2);

    cprintf("Path 1 norm: %d.%04d\n", Q16_INT_PART(norm1), Q16_FRAC_PART(norm1));
    cprintf("Path 2 norm: %d.%04d\n", Q16_INT_PART(norm2), Q16_FRAC_PART(norm2));

    if (norm1 != norm2) {
        cprintf("Non-associative! Execution order affects resource usage.\n");
    }
}

/**
 * Example 3: Resource quota management
 */
void example_quota_management(void) {
    /* System quota */
    resource_vector_t system_quota = RESOURCE_VEC(10000, 16384, 1000, 100000, 0, 10000, 1000, 100);

    /* Task requirements */
    resource_vector_t web_server = RESOURCE_VEC_BALANCED;
    resource_vector_t database = RESOURCE_VEC(500, 8192, 500, 1000, 0, 5000, 100, 5);

    /* Try to allocate web server */
    if (resource_vector_allocate(&system_quota, web_server)) {
        cprintf("Web server allocated successfully\n");
    }

    /* Try to allocate database */
    if (resource_vector_allocate(&system_quota, database)) {
        cprintf("Database allocated successfully\n");
    } else {
        cprintf("Database allocation failed: insufficient resources\n");
    }

    /* Release web server resources */
    resource_vector_release(&system_quota, web_server);
    cprintf("Web server resources released\n");
}

#endif /* RESOURCE_VECTOR_EXAMPLES */
