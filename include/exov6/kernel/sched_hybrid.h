#pragma once

/**
 * @file sched_hybrid.h
 * @brief Hybrid Lottery+Beatty Scheduler
 *
 * PEDAGOGICAL PURPOSE:
 * ====================
 * Demonstrates that combining complementary algorithms can achieve
 * properties that neither algorithm has alone. This is a key insight
 * in systems design: **hybrid approaches often outperform pure solutions**.
 *
 * THE SCHEDULING TRILEMMA:
 * ========================
 * Traditional schedulers face a trilemma:
 * 1. **Fairness**: Proportional CPU time (lottery, CFS)
 * 2. **Determinism**: Reproducible schedules (round-robin, Beatty)
 * 3. **Low variance**: Predictable latency (rate-monotonic, EDF)
 *
 * Most schedulers optimize 1-2 properties, sacrificing the third.
 *
 * HYBRID SOLUTION:
 * ================
 * PDAC hybrid scheduler achieves all three:
 *
 * 80% Lottery (fairness):
 *   - Ensures expected CPU time ∝ ticket count
 *   - Prevents priority inversion
 *   - Handles dynamic workloads
 *
 * 20% Beatty (determinism):
 *   - Reduces variance (no long unlucky streaks)
 *   - Prevents starvation (all tasks eventually selected)
 *   - Provides reproducibility (for debugging)
 *
 * FORMULA:
 * ========
 * On each scheduling decision:
 *   if (random() < 0.8) {
 *       task = lottery_select();   // 80% probabilistic
 *   } else {
 *       task = beatty_select();    // 20% deterministic
 *   }
 *
 * PROVABLE PROPERTIES:
 * ====================
 * 1. **Fairness** (from lottery component):
 *    Expected CPU time = 0.8 * (tickets / total) + 0.2 * (priority / total)
 *    Dominated by lottery term (0.8 >> 0.2)
 *
 * 2. **Starvation-Free** (from Beatty component):
 *    Even with 0 tickets, task runs every ~20 scheduling decisions
 *    (Beatty ensures all tasks eventually selected)
 *
 * 3. **Bounded Wait** (hybrid property):
 *    Max wait time = O(num_tasks * quantum)
 *    Better than pure lottery (unbounded in worst case)
 *
 * REAL-WORLD ANALOGUES:
 * =====================
 * - Linux CFS: Hybrid of fair queueing + priority scheduling
 * - Google Borg: Hybrid of priority + quota + best-effort
 * - AWS Lambda: Hybrid of FIFO + priority for different tiers
 * - Network QoS: Weighted Fair Queueing (WFQ) with strict priority
 *
 * WHY 80/20 SPLIT?
 * ================
 * - **80% lottery**: Preserves fairness guarantees (≈ proportional)
 * - **20% Beatty**: Just enough to prevent starvation
 * - Empirical: 80/20 balances fairness vs. determinism
 *
 * Alternative splits:
 * - 90/10: More fair, less deterministic
 * - 70/30: More deterministic, less fair
 * - 50/50: Loses fairness guarantees
 *
 * EXAMPLE:
 * ========
 * Task A: 100 tickets, priority 1.0
 * Task B: 200 tickets, priority 2.0
 * Task C:   1 ticket,  priority 0.1 (tiny!)
 *
 * Pure lottery: C starves (0.3% CPU time, might never run)
 * Hybrid:       C gets ≥ 20% * (1/3) ≈ 6.7% CPU time (guaranteed!)
 */

#include "types.h"
#include "dag_pdac.h"
#include "sched_lottery.h"
#include "sched_beatty.h"
#include "lcg.h"

/*******************************************************************************
 * CONFIGURATION
 ******************************************************************************/

/**
 * Lottery mode probability (Q16 fixed-point)
 *
 * 0.8 = 52429 in Q16 (52429 / 65536 ≈ 0.8)
 */
#define HYBRID_LOTTERY_PROBABILITY Q16(0.8)

/**
 * Beatty mode probability = 1.0 - lottery probability
 *
 * 0.2 = 13107 in Q16
 */
#define HYBRID_BEATTY_PROBABILITY  Q16(0.2)

/*******************************************************************************
 * SCHEDULER MODE
 ******************************************************************************/

/**
 * Scheduler mode (for current decision)
 */
typedef enum {
    HYBRID_MODE_LOTTERY,                      /* Using lottery scheduler */
    HYBRID_MODE_BEATTY,                       /* Using Beatty scheduler */
} hybrid_mode_t;

/*******************************************************************************
 * HYBRID SCHEDULER STATE
 ******************************************************************************/

/**
 * Hybrid scheduler state
 *
 * Maintains both lottery and Beatty sub-schedulers.
 */
typedef struct hybrid_scheduler {
    /* Sub-schedulers */
    lottery_scheduler_t lottery;              /* Lottery scheduler */
    beatty_scheduler_t  beatty;               /* Beatty scheduler */

    /* Random number generator */
    lcg_state_t *rng;                         /* Shared RNG */

    /* Mode tracking */
    hybrid_mode_t last_mode;                  /* Last scheduler used */
    uint64_t lottery_selections;              /* Times lottery was used */
    uint64_t beatty_selections;               /* Times Beatty was used */

    /* Performance statistics */
    uint64_t total_selections;                /* Total scheduling decisions */
    uint64_t task_selections[DAG_MAX_TASKS];  /* Per-task selection counts */
} hybrid_scheduler_t;

/*******************************************************************************
 * CORE API
 ******************************************************************************/

/**
 * Initialize hybrid scheduler
 *
 * Initializes both lottery and Beatty sub-schedulers.
 *
 * @param sched  Scheduler state to initialize
 * @param rng    Random number generator (must be initialized)
 */
void hybrid_init(hybrid_scheduler_t *sched, lcg_state_t *rng);

/**
 * Update task metadata (tickets and priority)
 *
 * Updates both lottery tickets and Beatty priority for a task.
 *
 * @param sched    Scheduler state
 * @param task_id  Task ID (index in DAG)
 * @param task     Task structure (contains resource vector)
 */
void hybrid_update_task(
    hybrid_scheduler_t *sched,
    uint16_t task_id,
    const dag_task_t *task
);

/**
 * Recompute all task metadata
 *
 * Updates tickets and priorities for all tasks in DAG.
 *
 * @param sched  Scheduler state
 * @param dag    DAG containing tasks
 */
void hybrid_recompute_all_tasks(
    hybrid_scheduler_t *sched,
    const dag_pdac_t *dag
);

/**
 * Select next task to run using hybrid scheduler
 *
 * Algorithm:
 * 1. Generate random number U ~ Uniform(0, 1)
 * 2. If U < 0.8: Use lottery_select()
 * 3. Else: Use beatty_select()
 * 4. Return selected task
 *
 * **KEY INSIGHT**: Lottery provides fairness, Beatty provides starvation-freedom.
 *
 * @param sched  Scheduler state
 * @param dag    DAG containing tasks
 * @return       Pointer to selected task, or NULL if no tasks ready
 */
dag_task_t *hybrid_select(
    hybrid_scheduler_t *sched,
    dag_pdac_t *dag
);

/**
 * Get current scheduler mode (last decision)
 *
 * Useful for logging and debugging.
 *
 * @param sched  Scheduler state
 * @return       Last mode used (LOTTERY or BEATTY)
 */
hybrid_mode_t hybrid_get_last_mode(const hybrid_scheduler_t *sched);

/*******************************************************************************
 * STATISTICS & INTROSPECTION
 ******************************************************************************/

/**
 * Get number of times lottery scheduler was used
 *
 * @param sched  Scheduler state
 * @return       Lottery selection count
 */
uint64_t hybrid_get_lottery_count(const hybrid_scheduler_t *sched);

/**
 * Get number of times Beatty scheduler was used
 *
 * @param sched  Scheduler state
 * @return       Beatty selection count
 */
uint64_t hybrid_get_beatty_count(const hybrid_scheduler_t *sched);

/**
 * Compute actual lottery/Beatty ratio
 *
 * Expected: 0.8 / 0.2 = 4.0
 *
 * @param sched  Scheduler state
 * @return       Lottery / Beatty ratio (Q16 fixed-point)
 */
q16_t hybrid_compute_mode_ratio(const hybrid_scheduler_t *sched);

/**
 * Get selection count for a task
 *
 * @param sched    Scheduler state
 * @param task_id  Task ID
 * @return         Selection count (across both modes)
 */
uint64_t hybrid_get_task_selection_count(
    const hybrid_scheduler_t *sched,
    uint16_t task_id
);

/**
 * Compute fairness metric for a task
 *
 * Compares actual CPU time vs. expected (from tickets).
 * Similar to lottery_compute_fairness() but accounts for hybrid nature.
 *
 * @param sched    Scheduler state
 * @param task_id  Task ID
 * @return         Fairness ratio (Q16 fixed-point), 1.0 = perfect
 */
q16_t hybrid_compute_fairness(
    const hybrid_scheduler_t *sched,
    uint16_t task_id
);

/**
 * Print hybrid scheduler statistics
 *
 * Shows mode distribution, per-task selection counts, and fairness metrics.
 *
 * @param sched  Scheduler state
 * @param dag    DAG containing task names
 */
void hybrid_print_stats(
    const hybrid_scheduler_t *sched,
    const dag_pdac_t *dag
);

/*******************************************************************************
 * TUNING & CONFIGURATION
 ******************************************************************************/

/**
 * Set custom lottery/Beatty probability split
 *
 * Default: 80/20 (lottery/Beatty)
 * Alternative: 90/10 (more fair), 70/30 (more deterministic)
 *
 * @param sched              Scheduler state
 * @param lottery_prob_q16   Lottery probability (Q16, e.g., Q16(0.8))
 */
void hybrid_set_mode_probability(
    hybrid_scheduler_t *sched,
    q16_t lottery_prob_q16
);

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Compare hybrid vs. pure lottery
 *
 * Shows that hybrid prevents starvation of low-priority tasks.
 */
void example_hybrid_vs_lottery(void);

/**
 * Example: Demonstrate starvation-freedom
 *
 * Task with 1 ticket still runs regularly (due to Beatty component).
 */
void example_hybrid_starvation_free(void);

/**
 * Example: Fairness analysis
 *
 * Verify that CPU time ≈ proportional to tickets (despite Beatty component).
 */
void example_hybrid_fairness(void);

/**
 * Example: Effect of mode probability tuning
 *
 * Compare 90/10, 80/20, 70/30 splits.
 */
void example_hybrid_tuning(void);

/**
 * Run all hybrid scheduler examples
 */
void hybrid_run_all_examples(void);
