#pragma once

/**
 * @file sched_beatty.h
 * @brief Beatty Sequence Scheduler
 *
 * PEDAGOGICAL PURPOSE:
 * ====================
 * Demonstrates how pure mathematics (irrational numbers) solves practical
 * systems problems (task distribution). This is a beautiful example of
 * "unreasonable effectiveness of mathematics" in computer science.
 *
 * MATHEMATICAL BACKGROUND:
 * ========================
 * A **Beatty sequence** for an irrational number α is:
 *   B_α(n) = floor(n * α)
 *
 * Example with golden ratio φ = (1 + √5) / 2 ≈ 1.618:
 *   B_φ(1) = floor(1 * 1.618) = 1
 *   B_φ(2) = floor(2 * 1.618) = 3
 *   B_φ(3) = floor(3 * 1.618) = 4
 *   B_φ(4) = floor(4 * 1.618) = 6
 *   B_φ(5) = floor(5 * 1.618) = 8
 *   ...
 *
 * KEY PROPERTY:
 * =============
 * Gaps between consecutive Beatty numbers are **deterministically distributed**:
 *   Gap sequence: 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, ... (never clusters)
 *
 * This is due to the **three-distance theorem** (Steinhaus theorem):
 * When you partition [0,1) using multiples of an irrational number,
 * you get at most 3 distinct gap sizes, and they're evenly distributed.
 *
 * WHY THIS MATTERS FOR SCHEDULING:
 * =================================
 * Traditional round-robin: deterministic but can cause starvation
 * Random selection: fair but bursty
 * Beatty sequences: **deterministic AND evenly distributed**
 *
 * REAL-WORLD ANALOGUES:
 * =====================
 * - Fibonacci hashing: Uses golden ratio for hash table probing
 * - Phyllotaxis: Plants use golden angle (222.5°) for optimal leaf spacing
 * - Quasicrystals: Non-periodic but deterministic structures
 * - Computer graphics: Low-discrepancy sequences for sampling
 *
 * SCHEDULING APPLICATION:
 * =======================
 * Instead of picking tasks randomly or round-robin, we use:
 *   task_index = B_φ(counter) mod num_ready_tasks
 *
 * This ensures:
 * 1. **Deterministic**: Same inputs → same schedule (reproducible)
 * 2. **Non-clustering**: Tasks evenly spaced (no starvation)
 * 3. **Low-priority tasks run**: Eventually every task gets scheduled
 *
 * EXAMPLE:
 * ========
 * 5 ready tasks, counter = 0, 1, 2, 3, 4, 5, ...
 * B_φ(n) = [1, 3, 4, 6, 8, 9, 11, 12, 14, 16, ...]
 * mod 5:   [1, 3, 4, 1, 3, 4,  1,  2,  4,  1, ...]
 *
 * Task selection: B, D, E, B, D, E, B, C, E, B, ...
 * Notice: All tasks eventually selected, no long gaps!
 */

#include "types.h"
#include "dag_pdac.h"

/*******************************************************************************
 * MATHEMATICAL CONSTANTS
 ******************************************************************************/

/**
 * Golden ratio φ = (1 + √5) / 2 ≈ 1.618033988749895
 *
 * Represented in Q16.16 fixed-point:
 *   φ * 2^16 = 106039 (approximately)
 */
#define BEATTY_GOLDEN_RATIO Q16(1.618033988749895)

/**
 * Alternative: Silver ratio δ_s = 1 + √2 ≈ 2.414213562373095
 *
 * Also produces good spacing properties.
 */
#define BEATTY_SILVER_RATIO Q16(2.414213562373095)

/*******************************************************************************
 * BEATTY SCHEDULER STATE
 ******************************************************************************/

/**
 * Beatty scheduler state
 *
 * Maintains counter for sequence generation and task priorities.
 */
typedef struct beatty_scheduler {
    /* Beatty sequence state */
    uint64_t counter;                         /* Sequence counter (n in B_φ(n)) */
    q16_t alpha;                              /* Irrational multiplier (φ) */

    /* Task priorities (for sorting) */
    q16_t priorities[DAG_MAX_TASKS];          /* Priority = octonion norm */

    /* Statistics */
    uint64_t selections[DAG_MAX_TASKS];       /* Times each task was selected */
    uint64_t total_selections;                /* Total selections */
} beatty_scheduler_t;

/*******************************************************************************
 * CORE API
 ******************************************************************************/

/**
 * Initialize Beatty scheduler
 *
 * @param sched  Scheduler state to initialize
 * @param alpha  Irrational multiplier (use BEATTY_GOLDEN_RATIO)
 */
void beatty_init(beatty_scheduler_t *sched, q16_t alpha);

/**
 * Update priority for a task based on its resource vector
 *
 * Priority = octonion_norm(task->resources)
 *
 * Tasks are sorted by priority (high priority first) before Beatty selection.
 *
 * @param sched    Scheduler state
 * @param task_id  Task ID (index in DAG)
 * @param task     Task structure (contains resource vector)
 */
void beatty_update_priority(
    beatty_scheduler_t *sched,
    uint16_t task_id,
    const dag_task_t *task
);

/**
 * Recompute all priorities for tasks in DAG
 *
 * Called when task resources change or new tasks are added.
 *
 * @param sched  Scheduler state
 * @param dag    DAG containing tasks
 */
void beatty_recompute_all_priorities(
    beatty_scheduler_t *sched,
    const dag_pdac_t *dag
);

/**
 * Select next task to run using Beatty sequence
 *
 * Algorithm:
 * 1. Collect all READY tasks
 * 2. Sort by priority (octonion norm, descending)
 * 3. Compute Beatty number: B_φ(counter) = floor(counter * φ)
 * 4. Select task at position: B_φ(counter) mod num_ready_tasks
 * 5. Increment counter
 *
 * **DETERMINISTIC**: Same DAG state → same selection
 * **NO CLUSTERING**: Tasks evenly spaced over time
 *
 * @param sched  Scheduler state
 * @param dag    DAG containing tasks
 * @return       Pointer to selected task, or NULL if no tasks ready
 */
dag_task_t *beatty_select(
    beatty_scheduler_t *sched,
    dag_pdac_t *dag
);

/**
 * Reset Beatty counter (for repeatable experiments)
 *
 * @param sched  Scheduler state
 */
void beatty_reset_counter(beatty_scheduler_t *sched);

/*******************************************************************************
 * STATISTICS & INTROSPECTION
 ******************************************************************************/

/**
 * Get current Beatty counter value
 *
 * @param sched  Scheduler state
 * @return       Current counter
 */
uint64_t beatty_get_counter(const beatty_scheduler_t *sched);

/**
 * Compute next Beatty number: B_α(counter)
 *
 * Formula: floor(counter * α)
 *
 * @param sched  Scheduler state
 * @return       Next Beatty number
 */
uint64_t beatty_compute_next(const beatty_scheduler_t *sched);

/**
 * Get selection count for a task
 *
 * @param sched    Scheduler state
 * @param task_id  Task ID
 * @return         Selection count
 */
uint64_t beatty_get_selection_count(
    const beatty_scheduler_t *sched,
    uint16_t task_id
);

/**
 * Analyze gap distribution in Beatty sequence
 *
 * Computes gaps between consecutive Beatty numbers over N steps.
 * Useful for verifying three-distance theorem.
 *
 * @param sched     Scheduler state
 * @param num_steps Number of steps to analyze
 * @param gaps_out  Output array (size >= num_steps)
 */
void beatty_analyze_gaps(
    beatty_scheduler_t *sched,
    uint32_t num_steps,
    uint32_t *gaps_out
);

/**
 * Print Beatty scheduler statistics
 *
 * Shows priority distribution and selection counts for all tasks.
 *
 * @param sched  Scheduler state
 * @param dag    DAG containing task names
 */
void beatty_print_stats(
    const beatty_scheduler_t *sched,
    const dag_pdac_t *dag
);

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Demonstrate three-distance theorem
 *
 * Shows that Beatty sequence gaps have at most 3 distinct values.
 */
void example_beatty_three_distance(void);

/**
 * Example: Compare Beatty vs. round-robin spacing
 *
 * Demonstrates superior distribution of Beatty sequences.
 */
void example_beatty_vs_roundrobin(void);

/**
 * Example: Deterministic scheduling (reproducibility)
 *
 * Shows that same DAG state produces same schedule.
 */
void example_beatty_determinism(void);

/**
 * Example: Beatty with priority-sorted tasks
 *
 * Demonstrates how priorities affect selection frequency.
 */
void example_beatty_priorities(void);

/**
 * Run all Beatty examples
 */
void beatty_run_all_examples(void);
