#pragma once

/**
 * @file percpu_sched.h
 * @brief Per-CPU Run Queues and Multi-Core Dispatcher
 *
 * PEDAGOGICAL PURPOSE:
 * ====================
 * Demonstrates how modern multi-core schedulers work:
 * - **Per-CPU run queues**: Each CPU has its own ready queue (reduces contention)
 * - **Load balancing**: Periodically redistribute tasks across CPUs
 * - **CPU affinity**: Tasks prefer to stay on same CPU (cache locality)
 *
 * KEY CONCEPTS:
 * =============
 * **Scalability Problem**:
 * Single global queue → lock contention on multi-core
 * Solution: Per-CPU queues with occasional load balancing
 *
 * **Cache Locality**:
 * Task running on CPU 0 → CPU 0's cache has task's data
 * If migrated to CPU 1 → cache miss penalty
 * Solution: CPU affinity (prefer same CPU)
 *
 * **Load Imbalance**:
 * CPU 0: 10 tasks
 * CPU 1: 1 task
 * Solution: Periodic load balancing (migrate tasks)
 *
 * REAL-WORLD ANALOGUES:
 * =====================
 * - **Linux CFS**: Per-CPU run queues + load_balance()
 * - **FreeBSD ULE**: Per-CPU queues + steal_thread()
 * - **Windows**: Per-processor ready queues + work stealing
 * - **Xen**: Per-PCPU run queues with credit scheduler
 *
 * DESIGN TRADE-OFFS:
 * ==================
 * **Per-CPU queues**:
 * + Scalability (no lock contention)
 * + Cache locality (tasks stay on same CPU)
 * - Load imbalance (some CPUs idle, others busy)
 * - Complexity (load balancing needed)
 *
 * **Global queue**:
 * + Perfect load balance
 * + Simple implementation
 * - Lock contention (doesn't scale)
 * - Poor cache locality
 */

#include "types.h"
#include "dag_pdac.h"
#include "sched_hybrid.h"
#include "task_exec.h"

/*******************************************************************************
 * CONFIGURATION
 ******************************************************************************/

/**
 * Maximum tasks per CPU ready queue
 */
#define PERCPU_MAX_READY_TASKS 64

/**
 * Load balancing interval (milliseconds)
 *
 * Linux: ~4ms (HZ=250) to 10ms (HZ=100)
 * PDAC: 100ms (less aggressive, simpler)
 */
#define LOAD_BALANCE_INTERVAL_MS 100

/**
 * Load imbalance threshold
 *
 * Migrate tasks if: max_load - min_load > THRESHOLD
 */
#define LOAD_IMBALANCE_THRESHOLD Q16(2.0)  /* 2.0 = significant imbalance */

/*******************************************************************************
 * PER-CPU SCHEDULER
 ******************************************************************************/

/**
 * Per-CPU scheduler state
 *
 * Each CPU has its own instance with independent run queue.
 */
typedef struct percpu_scheduler {
    /* CPU identification */
    uint8_t cpu_id;                         /* CPU identifier (0 to MAX_CPUS-1) */

    /* Hybrid scheduler (from Phase 3) */
    hybrid_scheduler_t sched;               /* Per-CPU scheduler instance */
    lcg_state_t rng;                        /* Per-CPU RNG state */

    /* Run queue */
    dag_task_t *ready_queue[PERCPU_MAX_READY_TASKS]; /* Ready tasks */
    uint16_t num_ready;                     /* Count of ready tasks */

    /* Currently executing */
    dag_task_t *current_task;               /* Task running on this CPU */
    task_context_t *current_context;        /* Execution context */

    /* Statistics */
    uint64_t total_tasks_run;               /* Tasks executed */
    uint64_t total_idle_time_us;            /* CPU idle cycles */
    uint64_t total_busy_time_us;            /* CPU busy cycles */
    uint64_t last_activity_us;              /* Last time CPU did something */
} percpu_scheduler_t;

/*******************************************************************************
 * MULTI-CORE DISPATCHER
 ******************************************************************************/

/**
 * Multi-core dispatcher
 *
 * Coordinates scheduling across multiple CPUs.
 */
typedef struct multicore_dispatcher {
    /* Per-CPU schedulers */
    percpu_scheduler_t cpus[MAX_CPUS];      /* Per-CPU scheduler array */
    uint8_t num_cpus;                       /* Number of CPUs */

    /* Global DAG */
    dag_pdac_t *dag;                        /* Shared task graph */

    /* Load balancing */
    uint64_t last_balance_time_us;          /* Last load balance time */
    uint32_t balance_interval_us;           /* Balance interval */
    uint64_t total_migrations;              /* Total task migrations */

    /* Global statistics */
    uint64_t total_tasks_completed;         /* Tasks finished */
    uint64_t total_context_switches;        /* All CPUs combined */
} multicore_dispatcher_t;

/*******************************************************************************
 * PER-CPU SCHEDULER API
 ******************************************************************************/

/**
 * Initialize per-CPU scheduler
 *
 * @param cpu      Per-CPU scheduler to initialize
 * @param cpu_id   CPU identifier (0 to MAX_CPUS-1)
 * @param seed     RNG seed (should be different per CPU)
 */
void percpu_sched_init(percpu_scheduler_t *cpu, uint8_t cpu_id, uint32_t seed);

/**
 * Add task to CPU's ready queue
 *
 * @param cpu    Per-CPU scheduler
 * @param task   Task to add
 * @return       0 on success, -1 if queue full
 */
int percpu_sched_add_task(percpu_scheduler_t *cpu, dag_task_t *task);

/**
 * Remove task from CPU's ready queue
 *
 * @param cpu    Per-CPU scheduler
 * @param task   Task to remove
 * @return       0 on success, -1 if not found
 */
int percpu_sched_remove_task(percpu_scheduler_t *cpu, dag_task_t *task);

/**
 * Select next task to run on this CPU
 *
 * Uses hybrid scheduler (lottery + Beatty).
 *
 * @param cpu    Per-CPU scheduler
 * @return       Next task to run, or NULL if none ready
 */
dag_task_t *percpu_sched_select_next(percpu_scheduler_t *cpu);

/**
 * Execute current task for one quantum
 *
 * @param cpu       Per-CPU scheduler
 * @param now_us    Current time (microseconds)
 * @return          True if task completed, false otherwise
 */
bool percpu_sched_run_current(percpu_scheduler_t *cpu, uint64_t now_us);

/**
 * Compute CPU load (ready + running tasks)
 *
 * @param cpu    Per-CPU scheduler
 * @return       Load value (Q16 fixed-point)
 */
q16_t percpu_sched_compute_load(const percpu_scheduler_t *cpu);

/**
 * Get CPU utilization (busy_time / total_time)
 *
 * @param cpu    Per-CPU scheduler
 * @return       Utilization (Q16 fixed-point, 0.0-1.0)
 */
q16_t percpu_sched_get_utilization(const percpu_scheduler_t *cpu);

/*******************************************************************************
 * MULTI-CORE DISPATCHER API
 ******************************************************************************/

/**
 * Initialize multi-core dispatcher
 *
 * @param dispatch  Dispatcher to initialize
 * @param dag       DAG to schedule
 * @param num_cpus  Number of CPUs (1 to MAX_CPUS)
 */
void multicore_dispatch_init(multicore_dispatcher_t *dispatch,
                              dag_pdac_t *dag,
                              uint8_t num_cpus);

/**
 * Assign task to a CPU
 *
 * Strategy: Assign to CPU with lowest load.
 *
 * @param dispatch  Dispatcher
 * @param task      Task to assign
 * @return          CPU ID assigned to, or -1 on failure
 */
int multicore_dispatch_assign_task(multicore_dispatcher_t *dispatch,
                                   dag_task_t *task);

/**
 * Perform load balancing across CPUs
 *
 * Algorithm:
 * 1. Find most loaded CPU
 * 2. Find least loaded CPU
 * 3. If imbalance > threshold: migrate task
 *
 * @param dispatch  Dispatcher
 * @param now_us    Current time (microseconds)
 */
void multicore_dispatch_balance(multicore_dispatcher_t *dispatch,
                                uint64_t now_us);

/**
 * Migrate task from one CPU to another
 *
 * @param dispatch   Dispatcher
 * @param task       Task to migrate
 * @param from_cpu   Source CPU ID
 * @param to_cpu     Destination CPU ID
 * @return           0 on success, -1 on failure
 */
int multicore_dispatch_migrate_task(multicore_dispatcher_t *dispatch,
                                    dag_task_t *task,
                                    uint8_t from_cpu,
                                    uint8_t to_cpu);

/**
 * Execute one scheduling step on all CPUs
 *
 * Each CPU:
 * 1. Select next task (if idle)
 * 2. Run current task for quantum
 * 3. Check for completion/preemption
 *
 * @param dispatch  Dispatcher
 * @param now_us    Current time (microseconds)
 */
void multicore_dispatch_step(multicore_dispatcher_t *dispatch,
                             uint64_t now_us);

/**
 * Check if all CPUs are idle (no work left)
 *
 * @param dispatch  Dispatcher
 * @return          True if all CPUs idle
 */
bool multicore_dispatch_all_idle(const multicore_dispatcher_t *dispatch);

/*******************************************************************************
 * STATISTICS & INTROSPECTION
 ******************************************************************************/

/**
 * Get total number of task migrations
 *
 * @param dispatch  Dispatcher
 * @return          Migration count
 */
uint64_t multicore_dispatch_get_migrations(const multicore_dispatcher_t *dispatch);

/**
 * Compute average CPU load across all CPUs
 *
 * @param dispatch  Dispatcher
 * @return          Average load (Q16 fixed-point)
 */
q16_t multicore_dispatch_get_avg_load(const multicore_dispatcher_t *dispatch);

/**
 * Get load imbalance (max_load - min_load)
 *
 * @param dispatch  Dispatcher
 * @return          Imbalance (Q16 fixed-point)
 */
q16_t multicore_dispatch_get_load_imbalance(const multicore_dispatcher_t *dispatch);

/**
 * Print per-CPU statistics
 *
 * @param dispatch  Dispatcher
 */
void multicore_dispatch_print_stats(const multicore_dispatcher_t *dispatch);

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Single CPU vs. multi-CPU speedup
 */
void example_multicore_speedup(void);

/**
 * Example: Load balancing demonstration
 */
void example_load_balancing(void);

/**
 * Example: CPU affinity and cache locality
 */
void example_cpu_affinity(void);
