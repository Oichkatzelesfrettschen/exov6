#pragma once

/**
 * @file dag_executor.h
 * @brief Complete DAG Execution Engine
 *
 * PEDAGOGICAL PURPOSE:
 * ====================
 * Demonstrates end-to-end execution of directed acyclic graphs with:
 * - Dependency tracking and resolution
 * - Multi-core parallel execution
 * - Admission control integration
 * - Real-time telemetry
 *
 * This is the "conductor" that orchestrates all Phase 1-4 components.
 *
 * KEY CONCEPTS:
 * =============
 * **DAG Execution**: Run tasks in dependency order
 * **Parallelism**: Execute independent tasks concurrently
 * **Resource Management**: Admission control + capability enforcement
 * **Monitoring**: Real-time performance telemetry
 *
 * EXECUTION ALGORITHM:
 * ====================
 * 1. **Initialization**:
 *    - Validate DAG (no cycles, connected)
 *    - Initialize dispatcher, admission, telemetry
 *
 * 2. **Main Loop** (until all tasks complete):
 *    a. Find tasks with satisfied dependencies → mark READY
 *    b. Try admission control for READY tasks
 *    c. Assign admitted tasks to CPUs
 *    d. Each CPU: select next task (hybrid scheduler)
 *    e. Execute tasks for quantum
 *    f. Update dependencies when tasks complete
 *    g. Periodic load balancing
 *    h. Update telemetry
 *
 * 3. **Completion**:
 *    - All tasks in COMPLETED or FAILED state
 *    - Print performance statistics
 *
 * REAL-WORLD ANALOGUES:
 * =====================
 * - **Apache Spark**: DAG execution engine for data processing
 * - **TensorFlow**: Computation graph execution
 * - **Make/Bazel**: Build DAG execution
 * - **AWS Step Functions**: Workflow DAG execution
 */

#include "types.h"
#include "dag_pdac.h"
#include "percpu_sched.h"
#include "sched_admission.h"
#include "sched_telemetry.h"
#include "task_exec.h"
#include "rcu_pdac.h"
#include "work_stealing.h"

/*******************************************************************************
 * DAG EXECUTOR STATE
 ******************************************************************************/

/**
 * DAG executor configuration
 */
typedef struct dag_executor_config {
    /* Multi-core settings */
    uint8_t num_cpus;                       /* Number of CPUs to use */

    /* Admission control settings */
    resource_vector_t refill_rate;          /* Token bucket refill rate */
    resource_vector_t burst_size;           /* Token bucket burst size */

    /* Execution settings */
    bool enable_load_balancing;             /* Enable periodic load balancing */
    bool enable_admission_control;          /* Enable admission control */
    bool enable_telemetry;                  /* Enable performance monitoring */
    bool enable_work_stealing;              /* Enable work-stealing scheduler */

    /* Work-stealing settings */
    ws_victim_strategy_t victim_strategy;   /* Victim selection strategy */

    /* Timing */
    uint64_t max_runtime_us;                /* Maximum execution time (0 = unlimited) */
} dag_executor_config_t;

/**
 * DAG executor state
 */
typedef struct dag_executor {
    /* DAG to execute */
    dag_pdac_t *dag;

    /* Configuration */
    dag_executor_config_t config;

    /* Execution components */
    multicore_dispatcher_t dispatcher;      /* Multi-core scheduler */
    admission_control_t admission;          /* Admission control */
    sched_telemetry_t telemetry;            /* Performance monitoring */
    lcg_state_t rng;                        /* Random number generator */
    rcu_state_t rcu;                        /* RCU for concurrent DAG access */
    ws_scheduler_t ws_scheduler;            /* Work-stealing scheduler (Phase 5.3) */

    /* Execution state */
    bool running;                           /* True if executing */
    uint64_t start_time_us;                 /* When execution started */
    uint64_t end_time_us;                   /* When execution ended */
    uint64_t current_time_us;               /* Current virtual time */

    /* Task contexts */
    task_context_t contexts[DAG_MAX_TASKS]; /* Execution contexts */

    /* Dependency tracking */
    uint16_t tasks_ready;                   /* Tasks with deps satisfied */
    uint16_t tasks_running;                 /* Tasks currently executing */
    uint16_t tasks_completed;               /* Tasks finished */
    uint16_t tasks_failed;                  /* Tasks failed */
} dag_executor_t;

/*******************************************************************************
 * EXECUTOR LIFECYCLE
 ******************************************************************************/

/**
 * Initialize DAG executor with default configuration
 *
 * @param exec     Executor to initialize
 * @param dag      DAG to execute
 * @param num_cpus Number of CPUs
 */
void dag_executor_init(dag_executor_t *exec,
                       dag_pdac_t *dag,
                       uint8_t num_cpus);

/**
 * Initialize with custom configuration
 *
 * @param exec    Executor to initialize
 * @param dag     DAG to execute
 * @param config  Configuration
 */
void dag_executor_init_with_config(dag_executor_t *exec,
                                    dag_pdac_t *dag,
                                    const dag_executor_config_t *config);

/**
 * Validate DAG before execution
 *
 * Checks:
 * - No cycles (topological sort possible)
 * - All dependencies valid
 * - At least one task
 *
 * @param exec  Executor
 * @return      0 on success, -1 if invalid
 */
int dag_executor_validate(dag_executor_t *exec);

/*******************************************************************************
 * EXECUTION CONTROL
 ******************************************************************************/

/**
 * Start DAG execution
 *
 * Begins executing tasks. Returns immediately if async, blocks if sync.
 *
 * @param exec  Executor
 */
void dag_executor_start(dag_executor_t *exec);

/**
 * Execute one scheduling step
 *
 * Processes one quantum of execution:
 * - Update dependencies
 * - Admit ready tasks
 * - Schedule and execute
 * - Update telemetry
 *
 * @param exec  Executor
 * @return      True if work remains, false if complete
 */
bool dag_executor_step(dag_executor_t *exec);

/**
 * Run DAG to completion (synchronous)
 *
 * Executes until all tasks complete or timeout.
 *
 * @param exec  Executor
 * @return      0 on success, -1 on timeout/failure
 */
int dag_executor_run_sync(dag_executor_t *exec);

/**
 * Stop execution
 *
 * @param exec  Executor
 */
void dag_executor_stop(dag_executor_t *exec);

/**
 * Check if execution is complete
 *
 * @param exec  Executor
 * @return      True if all tasks done
 */
bool dag_executor_is_complete(const dag_executor_t *exec);

/*******************************************************************************
 * WORK-STEALING INTEGRATION (Phase 5.3.4)
 ******************************************************************************/

/**
 * Submit ready tasks to work-stealing scheduler
 *
 * Enqueues all READY tasks to the work-stealing scheduler for parallel execution.
 * Uses RCU protection for safe concurrent access.
 *
 * @param exec  Executor
 * @return      Number of tasks submitted
 */
uint16_t dag_executor_submit_ready_tasks(dag_executor_t *exec);

/**
 * Execute tasks using work-stealing across CPUs
 *
 * Each CPU:
 * 1. Gets task from work-stealing scheduler (local or stolen)
 * 2. Executes task under RCU protection
 * 3. Marks task as completed
 * 4. Updates dependencies
 *
 * @param exec     Executor
 * @param cpu_id   CPU executing this function
 * @return         Number of tasks executed by this CPU
 */
uint16_t dag_executor_execute_ws(dag_executor_t *exec, uint8_t cpu_id);

/**
 * Get work-stealing scheduler statistics
 *
 * @param exec   Executor
 * @param stats  Output statistics
 */
void dag_executor_get_ws_stats(const dag_executor_t *exec, ws_stats_t *stats);

/*******************************************************************************
 * DEPENDENCY MANAGEMENT
 ******************************************************************************/

/**
 * Check if task's dependencies are satisfied
 *
 * @param exec     Executor
 * @param task_id  Task to check
 * @return         True if all dependencies complete
 */
bool dag_executor_deps_satisfied(const dag_executor_t *exec,
                                  uint16_t task_id);

/**
 * Update task states based on dependencies
 *
 * Transitions tasks from PENDING → READY when deps satisfied.
 *
 * @param exec  Executor
 */
void dag_executor_update_dependencies(dag_executor_t *exec);

/**
 * Mark dependents as ready when task completes
 *
 * @param exec     Executor
 * @param task_id  Completed task
 */
void dag_executor_notify_completion(dag_executor_t *exec,
                                     uint16_t task_id);

/*******************************************************************************
 * STATISTICS & REPORTING
 ******************************************************************************/

/**
 * Get execution duration
 *
 * @param exec  Executor
 * @return      Duration in microseconds
 */
uint64_t dag_executor_get_duration(const dag_executor_t *exec);

/**
 * Get makespan (critical path length)
 *
 * Longest path from start to end in DAG.
 *
 * @param exec  Executor
 * @return      Makespan in microseconds
 */
uint64_t dag_executor_get_makespan(const dag_executor_t *exec);

/**
 * Compute speedup vs. sequential execution
 *
 * Speedup = sequential_time / parallel_time
 *
 * @param exec  Executor
 * @return      Speedup factor (Q16 fixed-point)
 */
q16_t dag_executor_compute_speedup(const dag_executor_t *exec);

/**
 * Compute parallel efficiency
 *
 * Efficiency = speedup / num_cpus
 *
 * @param exec  Executor
 * @return      Efficiency (Q16 fixed-point, 0.0-1.0)
 */
q16_t dag_executor_compute_efficiency(const dag_executor_t *exec);

/**
 * Print execution statistics
 *
 * @param exec  Executor
 */
void dag_executor_print_stats(const dag_executor_t *exec);

/**
 * Print comprehensive report
 *
 * Includes telemetry, dispatcher stats, and DAG metrics.
 *
 * @param exec  Executor
 */
void dag_executor_print_report(const dag_executor_t *exec);

/*******************************************************************************
 * UTILITY FUNCTIONS
 ******************************************************************************/

/**
 * Create default executor configuration
 *
 * @param num_cpus  Number of CPUs
 * @return          Default config
 */
dag_executor_config_t dag_executor_default_config(uint8_t num_cpus);

/**
 * Estimate sequential execution time
 *
 * Sum of all task work estimates (no parallelism).
 *
 * @param exec  Executor
 * @return      Estimated time (microseconds)
 */
uint64_t dag_executor_estimate_sequential_time(const dag_executor_t *exec);

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Simple pipeline execution
 */
void example_dag_executor_pipeline(void);

/**
 * Example: Diamond DAG with parallelism
 */
void example_dag_executor_diamond(void);

/**
 * Example: Multi-core scaling analysis
 */
void example_dag_executor_scaling(void);
