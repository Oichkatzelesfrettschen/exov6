#pragma once

/**
 * @file dag_pdac.h
 * @brief PDAC DAG: Directed Acyclic Graph Scheduler with Resource Vectors
 *
 * PEDAGOGICAL PURPOSE:
 * ====================
 * This module demonstrates how non-associative algebra (octonions) naturally
 * models path-dependent task scheduling in operating systems.
 *
 * KEY INSIGHT:
 * ============
 * In DAG scheduling, execution order matters:
 *   (Task A → Task B) → Task C  ≠  Task A → (Task B → Task C)
 *
 * Why? Because intermediate tasks consume resources, affecting what's available
 * for subsequent tasks. This is NON-ASSOCIATIVE composition!
 *
 * REAL-WORLD ANALOGUES:
 * =====================
 * - Google's Borg scheduler: DAG-based task dependencies
 * - Apache Spark: DAG execution plans
 * - Kubernetes Jobs: Dependency chains
 * - Build systems (Make, Bazel): DAG of compilation steps
 *
 * PDAC extends these with:
 * - Formal algebraic guarantees (octonion algebra)
 * - Deadlock detection via zero divisors
 * - Multidimensional resource optimization
 */

#include "types.h"
#include "resource_vector.h"
#include <stdatomic.h>

/* ============================================================================
 * DAG NODE AND EDGE STRUCTURES
 * ============================================================================ */

/**
 * Maximum tasks in DAG (fixed-size for kernel simplicity)
 */
#define DAG_MAX_TASKS 64

/**
 * Maximum dependencies per task
 */
#define DAG_MAX_DEPS 8

/**
 * Task state (atomic for concurrent access)
 */
typedef enum {
    TASK_STATE_PENDING,       /* Not yet runnable (dependencies unsatisfied) */
    TASK_STATE_READY,         /* Ready to run (all dependencies satisfied) */
    TASK_STATE_RUNNING,       /* Currently executing */
    TASK_STATE_COMPLETED,     /* Finished execution */
    TASK_STATE_FAILED,        /* Failed (e.g., deadlock detected) */
} task_state_t;

/**
 * DAG Task Node
 *
 * Represents a single task with:
 * - Resource requirements (8D vector)
 * - Dependencies on other tasks
 * - Current execution state
 */
typedef struct dag_task {
    /* Task identification */
    uint16_t id;                           /* Unique task ID */
    char name[32];                         /* Human-readable name */

    /* Resource requirements */
    resource_vector_t resources;           /* 8D resource vector */

    /* Dependencies */
    uint16_t deps[DAG_MAX_DEPS];           /* Task IDs this task depends on */
    uint8_t num_deps;                      /* Number of dependencies */

    /* State (atomic for concurrent access via RCU) */
    _Atomic task_state_t state;            /* Current execution state */

    /* Scheduling metadata */
    uint8_t policy;                        /* Scheduling policy (0=NORMAL, 1=FIFO, 2=RR) */
    q16_t priority;                        /* Priority (computed from norm) */
    uint64_t start_time;                   /* Start time (ticks) */
    uint64_t end_time;                     /* End time (ticks) */

    /* Telemetry */
    struct {
        uint64_t schedule_count;               /* Number of times scheduled */
        uint64_t run_time_ticks;               /* Total CPU time consumed */
        uint64_t last_runnable_time;           /* Timestamp when became READY */
        uint64_t total_latency_ticks;          /* Cumulative scheduling latency */
    } stats;
} dag_task_t;

/**
 * PDAC DAG Structure
 *
 * Represents entire task dependency graph with resource management
 */
typedef struct dag_pdac {
    dag_task_t tasks[DAG_MAX_TASKS];       /* Array of tasks */
    uint16_t num_tasks;                    /* Number of tasks in DAG */

    /* Resource accounting */
    resource_vector_t system_quota;        /* Total system resources */
    resource_vector_t available;           /* Currently available resources */
} dag_pdac_t;

/* ============================================================================
 * DAG CONSTRUCTION API
 * ============================================================================ */

/**
 * Initialize empty PDAC DAG
 */
void pdac_dag_init(dag_pdac_t *dag, resource_vector_t system_quota);

/**
 * Add task to PDAC DAG
 *
 * Returns: Task ID on success, -1 on failure (DAG full)
 */
int pdac_dag_add_task(
    dag_pdac_t *dag,
    const char *name,
    resource_vector_t resources
);

/**
 * Add dependency: task_id depends on dep_id
 *
 * Ensures DAG property (no cycles)
 * Returns: 0 on success, -1 on failure (cycle detected or max deps exceeded)
 */
int pdac_dag_add_dependency(
    dag_pdac_t *dag,
    uint16_t task_id,
    uint16_t dep_id
);

/* ============================================================================
 * DAG PATH COMPOSITION
 * ============================================================================ */

/**
 * Compose path through DAG using octonion multiplication
 *
 * Given a sequence of task IDs, compute the composed resource vector:
 *   result = tasks[0] * tasks[1] * ... * tasks[n-1]
 *
 * **NON-ASSOCIATIVE**: Different evaluation orders yield different results!
 *
 * This models real OS behavior:
 * - Left-associative: Sequential execution with resource depletion
 * - Right-associative: Speculative resource reservation
 *
 * Returns: Composed resource vector
 */
resource_vector_t pdac_dag_compose_path(
    dag_pdac_t *dag,
    uint16_t *path,          /* Array of task IDs */
    uint16_t path_len        /* Number of tasks in path */
);

/**
 * Demonstrate non-associativity of path composition
 *
 * Computes two evaluation orders for path [A, B, C]:
 * - Left-associative:  (A * B) * C
 * - Right-associative: A * (B * C)
 *
 * Returns: 1 if results differ (non-associative), 0 if same
 */
int pdac_dag_demonstrate_nonassociativity(
    dag_pdac_t *dag,
    uint16_t task_a,
    uint16_t task_b,
    uint16_t task_c,
    resource_vector_t *out_left,   /* Output: left-associative result */
    resource_vector_t *out_right   /* Output: right-associative result */
);

/* ============================================================================
 * DEADLOCK DETECTION
 * ============================================================================ */

/**
 * Deadlock detection result
 */
typedef struct deadlock_info {
    int detected;                    /* 1 if deadlock detected, 0 otherwise */
    uint16_t task1;                  /* First conflicting task */
    uint16_t task2;                  /* Second conflicting task */
    char reason[128];                /* Human-readable explanation */
} deadlock_info_t;

/**
 * Detect resource deadlocks using zero divisor property
 *
 * Checks all pairs of tasks for orthogonal resource requirements.
 * If two tasks have orthogonal resources (composition ≈ 0), they may deadlock.
 *
 * Example deadlock scenario:
 *   Task A: High CPU, zero memory
 *   Task B: Zero CPU, high memory
 *   → Composition ≈ 0 (zero divisor) → DEADLOCK
 *
 * Returns: deadlock_info_t with details
 */
deadlock_info_t pdac_dag_detect_deadlock(dag_pdac_t *dag);

/**
 * Check if specific task pair is orthogonal (potential deadlock)
 *
 * Returns: 1 if orthogonal (deadlock risk), 0 otherwise
 */
int pdac_dag_check_task_orthogonality(
    dag_pdac_t *dag,
    uint16_t task1,
    uint16_t task2
);

/* ============================================================================
 * DAG SCHEDULING
 * ============================================================================ */

/**
 * Find next ready task to execute
 *
 * Selects highest-priority task where:
 * 1. All dependencies are satisfied (state = COMPLETED)
 * 2. Resource requirements fit within available quota
 *
 * Priority = norm(resource_vector) (higher norm = higher priority)
 *
 * Returns: Task ID, or -1 if no task is ready
 */
int pdac_dag_get_next_ready_task(dag_pdac_t *dag);

/**
 * Mark task as running and allocate resources
 *
 * Returns: 0 on success, -1 on failure (insufficient resources)
 */
int pdac_dag_start_task(dag_pdac_t *dag, uint16_t task_id);

/**
 * Mark task as completed and release resources
 */
void pdac_dag_complete_task(dag_pdac_t *dag, uint16_t task_id);

/**
 * Check if DAG is fully completed
 *
 * Returns: 1 if all tasks are COMPLETED, 0 otherwise
 */
int pdac_dag_is_complete(dag_pdac_t *dag);

/* ============================================================================
 * DEBUGGING AND VISUALIZATION
 * ============================================================================ */

/**
 * Print PDAC DAG task graph
 */
void pdac_dag_print(dag_pdac_t *dag, const char *label);

/**
 * Print task details
 */
void pdac_dag_print_task(dag_pdac_t *dag, uint16_t task_id);

/**
 * Print path composition result
 */
void pdac_dag_print_path_composition(
    dag_pdac_t *dag,
    uint16_t *path,
    uint16_t path_len,
    resource_vector_t result
);

/* ============================================================================
 * PEDAGOGICAL EXAMPLES
 * ============================================================================ */

#ifdef DEBUG

/**
 * Example 1: Path-dependent scheduling
 *
 * Demonstrates that (A → B) → C ≠ A → (B → C) in resource allocation
 */
void pdac_example_dag_path_dependence(void);

/**
 * Example 2: Deadlock detection via zero divisors
 *
 * Shows how orthogonal tasks (CPU-only vs. memory-only) can deadlock
 */
void pdac_example_dag_deadlock_detection(void);

/**
 * Example 3: DAG scheduler simulation
 *
 * Runs complete DAG with 5 tasks, showing resource allocation over time
 */
void pdac_example_dag_scheduler(void);

/**
 * Run all PDAC DAG pedagogical examples
 */
void pdac_dag_run_examples(void);

#endif /* DEBUG */
