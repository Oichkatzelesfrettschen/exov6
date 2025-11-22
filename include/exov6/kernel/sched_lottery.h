#pragma once

/**
 * @file sched_lottery.h
 * @brief Lottery Scheduler with Resource-Weighted Tickets
 *
 * PEDAGOGICAL PURPOSE:
 * ====================
 * Demonstrates Carl Waldspurger's lottery scheduling algorithm, extended with
 * multidimensional resource weighting using octonion norms.
 *
 * KEY INNOVATION:
 * ===============
 * Classical lottery scheduling uses single-dimensional priorities (nice values).
 * PDAC lottery scheduling uses 8D resource vectors, where:
 *   tickets = octonion_norm(task->resources) * BASE_TICKETS
 *
 * This naturally weights CPU-bound, I/O-bound, and mixed workloads fairly.
 *
 * REAL-WORLD ANALOGUES:
 * =====================
 * - VMware ESXi: Shares-based scheduling (lottery scheduling variant)
 * - Xen hypervisor: Credit-based scheduling (inspired by lottery)
 * - Original lottery scheduler: Waldspurger & Weihl, 1994
 *
 * FAIRNESS GUARANTEE:
 * ===================
 * If task A has n_A tickets and task B has n_B tickets, then:
 *   Expected CPU time for A / Expected CPU time for B = n_A / n_B
 *
 * This is a **probabilistic guarantee** (holds in expectation).
 *
 * EXAMPLE:
 * ========
 * Task A: CPU=1.0, MEM=0.5 → norm ≈ 1.12 → 112 tickets
 * Task B: CPU=2.0, MEM=1.0 → norm ≈ 2.24 → 224 tickets
 * Task C: CPU=0.5, MEM=0.5 → norm ≈ 0.71 →  71 tickets
 * Total: 407 tickets
 *
 * Random = 250:
 *   250 - 112 = 138  (skip A)
 *   138 - 224 < 0    (select B!)
 *
 * Expected CPU time: A=27.5%, B=55.0%, C=17.5%
 */

#include "types.h"
#include "dag_pdac.h"
#include "lcg.h"

/*******************************************************************************
 * CONFIGURATION
 ******************************************************************************/

/**
 * Base tickets per unit of resource norm
 *
 * A task with norm=1.0 gets 100 tickets.
 * This multiplier provides enough granularity for fair distribution.
 */
#define LOTTERY_BASE_TICKETS 100

/**
 * Minimum tickets per task
 *
 * Prevents starvation: even tasks with tiny resource requirements get tickets.
 */
#define LOTTERY_MIN_TICKETS 1

/**
 * Maximum tickets per task
 *
 * Prevents one task from dominating the lottery.
 */
#define LOTTERY_MAX_TICKETS 10000

/*******************************************************************************
 * LOTTERY SCHEDULER STATE
 ******************************************************************************/

/**
 * Lottery scheduler state
 *
 * Maintains per-task ticket counts and RNG state.
 */
typedef struct lottery_scheduler {
    /* Random number generator */
    lcg_state_t *rng;                         /* LCG state for ticket selection */

    /* Ticket accounting */
    uint32_t tickets[DAG_MAX_TASKS];          /* Tickets per task */
    uint32_t total_tickets;                   /* Sum of all ready task tickets */

    /* Statistics */
    uint64_t selections[DAG_MAX_TASKS];       /* Times each task was selected */
    uint64_t total_selections;                /* Total selections */
} lottery_scheduler_t;

/*******************************************************************************
 * CORE API
 ******************************************************************************/

/**
 * Initialize lottery scheduler
 *
 * @param sched   Scheduler state to initialize
 * @param rng     Random number generator (must be initialized)
 */
void lottery_init(lottery_scheduler_t *sched, lcg_state_t *rng);

/**
 * Update tickets for a task based on its resource vector
 *
 * Ticket formula:
 *   norm = octonion_norm(task->resources)
 *   tickets = norm * BASE_TICKETS
 *   tickets = clamp(tickets, MIN_TICKETS, MAX_TICKETS)
 *
 * @param sched    Scheduler state
 * @param task_id  Task ID (index in DAG)
 * @param task     Task structure (contains resource vector)
 */
void lottery_update_tickets(
    lottery_scheduler_t *sched,
    uint16_t task_id,
    const dag_task_t *task
);

/**
 * Recompute all tickets for tasks in DAG
 *
 * Called when task resources change or new tasks are added.
 *
 * @param sched  Scheduler state
 * @param dag    DAG containing tasks
 */
void lottery_recompute_all_tickets(
    lottery_scheduler_t *sched,
    const dag_pdac_t *dag
);

/**
 * Select next task to run using lottery scheduling
 *
 * Algorithm:
 * 1. Sum tickets of all READY tasks
 * 2. Generate random number in [0, total_tickets)
 * 3. Walk through ready tasks, subtracting tickets
 * 4. When random number reaches 0, select that task
 *
 * @param sched  Scheduler state
 * @param dag    DAG containing tasks
 * @return       Pointer to selected task, or NULL if no tasks ready
 */
dag_task_t *lottery_select(
    lottery_scheduler_t *sched,
    dag_pdac_t *dag
);

/*******************************************************************************
 * STATISTICS & INTROSPECTION
 ******************************************************************************/

/**
 * Get ticket count for a task
 *
 * @param sched    Scheduler state
 * @param task_id  Task ID
 * @return         Number of tickets, or 0 if invalid task_id
 */
uint32_t lottery_get_tickets(
    const lottery_scheduler_t *sched,
    uint16_t task_id
);

/**
 * Get total tickets across all ready tasks
 *
 * @param sched  Scheduler state
 * @return       Total tickets
 */
uint32_t lottery_get_total_tickets(const lottery_scheduler_t *sched);

/**
 * Get selection count for a task (how many times it won the lottery)
 *
 * @param sched    Scheduler state
 * @param task_id  Task ID
 * @return         Selection count
 */
uint64_t lottery_get_selection_count(
    const lottery_scheduler_t *sched,
    uint16_t task_id
);

/**
 * Compute fairness metric (actual vs. expected CPU time)
 *
 * For a task with T tickets out of TOTAL tickets:
 *   Expected selections = T / TOTAL * total_selections
 *   Actual selections = selections[task_id]
 *   Fairness ratio = Actual / Expected
 *
 * Ideal fairness ratio = 1.0 (actual matches expected)
 *
 * @param sched    Scheduler state
 * @param task_id  Task ID
 * @return         Fairness ratio (Q16 fixed-point)
 */
q16_t lottery_compute_fairness(
    const lottery_scheduler_t *sched,
    uint16_t task_id
);

/**
 * Print lottery scheduler statistics
 *
 * Shows ticket distribution and selection counts for all tasks.
 *
 * @param sched  Scheduler state
 * @param dag    DAG containing task names
 */
void lottery_print_stats(
    const lottery_scheduler_t *sched,
    const dag_pdac_t *dag
);

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Compare lottery vs. round-robin fairness
 *
 * Demonstrates that lottery scheduling achieves proportional fairness.
 */
void example_lottery_fairness(void);

/**
 * Example: Effect of ticket ratios on CPU time
 *
 * Shows how ticket ratios translate to CPU time ratios.
 */
void example_lottery_ratios(void);

/**
 * Example: Lottery scheduling with DAG dependencies
 *
 * Demonstrates lottery scheduling respects DAG constraints.
 */
void example_lottery_dag(void);
