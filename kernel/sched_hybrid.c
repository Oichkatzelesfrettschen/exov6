/**
 * @file sched_hybrid.c
 * @brief Hybrid Lottery+Beatty Scheduler Implementation
 *
 * @see include/sched_hybrid.h for API documentation
 */

#include "sched_hybrid.h"
#include "printf.h"
#include <stdint.h>
#include <string.h>

/*******************************************************************************
 * CORE API IMPLEMENTATION
 ******************************************************************************/

/**
 * Initialize hybrid scheduler
 */
void hybrid_init(hybrid_scheduler_t *sched, lcg_state_t *rng)
{
    if (sched == NULL || rng == NULL) {
        return;
    }

    /* Initialize RNG */
    sched->rng = rng;

    /* Initialize sub-schedulers */
    lottery_init(&sched->lottery, rng);
    beatty_init(&sched->beatty, BEATTY_GOLDEN_RATIO);

    /* Reset statistics */
    sched->last_mode = HYBRID_MODE_LOTTERY;
    sched->lottery_selections = 0;
    sched->beatty_selections = 0;
    sched->total_selections = 0;

    memset(sched->task_selections, 0, sizeof(sched->task_selections));
}

/**
 * Update task metadata (tickets and priority)
 */
void hybrid_update_task(
    hybrid_scheduler_t *sched,
    uint16_t task_id,
    const dag_task_t *task)
{
    if (sched == NULL || task == NULL || task_id >= DAG_MAX_TASKS) {
        return;
    }

    /* Update lottery tickets */
    lottery_update_tickets(&sched->lottery, task_id, task);

    /* Update Beatty priority */
    beatty_update_priority(&sched->beatty, task_id, task);
}

/**
 * Recompute all task metadata
 */
void hybrid_recompute_all_tasks(
    hybrid_scheduler_t *sched,
    const dag_pdac_t *dag)
{
    if (sched == NULL || dag == NULL) {
        return;
    }

    /* Update both sub-schedulers */
    lottery_recompute_all_tickets(&sched->lottery, dag);
    beatty_recompute_all_priorities(&sched->beatty, dag);
}

/**
 * Select next task to run using hybrid scheduler
 *
 * ALGORITHM WALKTHROUGH:
 * ======================
 * Example scheduling decision:
 *
 * 1. Generate random: U = 0.65 (from LCG)
 * 2. Compare: 0.65 < 0.8? YES
 * 3. Use lottery_select()
 * 4. Task B wins lottery (200 tickets out of 350 total)
 * 5. Return Task B
 *
 * Next decision:
 * 1. U = 0.91
 * 2. 0.91 < 0.8? NO
 * 3. Use beatty_select()
 * 4. Beatty picks Task C (deterministic based on counter)
 * 5. Return Task C
 *
 * Over 1000 decisions: ~800 lottery, ~200 Beatty
 */
dag_task_t *hybrid_select(
    hybrid_scheduler_t *sched,
    dag_pdac_t *dag)
{
    if (sched == NULL || dag == NULL) {
        return NULL;
    }

    /* Step 1: Generate random decision */
    double u = lcg_uniform(sched->rng);

    /* Step 2: Choose mode based on probability */
    dag_task_t *selected;

    if (u < 0.8) {
        /* 80% probability: Use lottery scheduler */
        sched->last_mode = HYBRID_MODE_LOTTERY;
        sched->lottery_selections++;
        selected = lottery_select(&sched->lottery, dag);
    } else {
        /* 20% probability: Use Beatty scheduler */
        sched->last_mode = HYBRID_MODE_BEATTY;
        sched->beatty_selections++;
        selected = beatty_select(&sched->beatty, dag);
    }

    /* Update statistics */
    if (selected != NULL) {
        sched->task_selections[selected->id]++;
        sched->total_selections++;
    }

    return selected;
}

/**
 * Get current scheduler mode
 */
hybrid_mode_t hybrid_get_last_mode(const hybrid_scheduler_t *sched)
{
    return sched ? sched->last_mode : HYBRID_MODE_LOTTERY;
}

/*******************************************************************************
 * STATISTICS & INTROSPECTION
 ******************************************************************************/

uint64_t hybrid_get_lottery_count(const hybrid_scheduler_t *sched)
{
    return sched ? sched->lottery_selections : 0;
}

uint64_t hybrid_get_beatty_count(const hybrid_scheduler_t *sched)
{
    return sched ? sched->beatty_selections : 0;
}

/**
 * Compute actual lottery/Beatty ratio
 */
q16_t hybrid_compute_mode_ratio(const hybrid_scheduler_t *sched)
{
    if (sched == NULL || sched->beatty_selections == 0) {
        return Q16(4.0); /* Default: 80/20 = 4.0 */
    }

    /* Ratio = lottery_count / beatty_count */
    uint64_t ratio_scaled = (sched->lottery_selections << 16) /
                            sched->beatty_selections;

    return (q16_t)ratio_scaled;
}

uint64_t hybrid_get_task_selection_count(
    const hybrid_scheduler_t *sched,
    uint16_t task_id)
{
    if (sched == NULL || task_id >= DAG_MAX_TASKS) {
        return 0;
    }
    return sched->task_selections[task_id];
}

/**
 * Compute fairness metric for a task
 *
 * Expected selections = 0.8 * (tickets / total_tickets) * total +
 *                       0.2 * (1 / num_ready) * total
 *
 * For simplicity, we use lottery fairness (dominated by 0.8 term).
 */
q16_t hybrid_compute_fairness(
    const hybrid_scheduler_t *sched,
    uint16_t task_id)
{
    if (sched == NULL || task_id >= DAG_MAX_TASKS) {
        return 0;
    }

    /* Approximate using lottery fairness (80% component dominates) */
    return lottery_compute_fairness(&sched->lottery, task_id);
}

/**
 * Print hybrid scheduler statistics
 */
void hybrid_print_stats(
    const hybrid_scheduler_t *sched,
    const dag_pdac_t *dag)
{
    if (sched == NULL || dag == NULL) {
        return;
    }

    printf("\n=== Hybrid Scheduler Statistics ===\n");
    printf("Total selections: %llu\n", sched->total_selections);
    printf("Lottery selections: %llu (%.1f%%)\n",
           sched->lottery_selections,
           (sched->lottery_selections * 100.0) / sched->total_selections);
    printf("Beatty selections: %llu (%.1f%%)\n",
           sched->beatty_selections,
           (sched->beatty_selections * 100.0) / sched->total_selections);

    q16_t ratio = hybrid_compute_mode_ratio(sched);
    printf("Lottery/Beatty ratio: %.2f (expected: 4.0)\n\n",
           (double)ratio / 65536.0);

    printf("%-4s %-20s %-8s %-10s %-12s %-10s\n",
           "ID", "Name", "Tickets", "Priority", "Selections", "Fairness");
    printf("----------------------------------------------------------------------\n");

    for (uint16_t i = 0; i < dag->num_tasks; i++) {
        uint64_t selections = sched->task_selections[i];

        if (selections == 0) {
            continue; /* Skip tasks with no selections */
        }

        uint32_t tickets = lottery_get_tickets(&sched->lottery, i);
        q16_t priority = sched->beatty.priorities[i];
        q16_t fairness = hybrid_compute_fairness(sched, i);

        double percentage = (selections * 100.0) / sched->total_selections;

        printf("%-4u %-20s %-8u %-10.2f %-12llu %.2f (%.1f%%)\n",
               i,
               dag->tasks[i].name,
               tickets,
               (double)priority / 65536.0,
               selections,
               (double)fairness / 65536.0,
               percentage);
    }

    printf("\n");
}

/*******************************************************************************
 * TUNING & CONFIGURATION
 ******************************************************************************/

/**
 * Set custom lottery/Beatty probability split
 *
 * NOTE: This is a placeholder - full implementation would modify
 * the threshold in hybrid_select(). For now, 80/20 is hardcoded.
 */
void hybrid_set_mode_probability(
    hybrid_scheduler_t *sched,
    q16_t lottery_prob_q16)
{
    if (sched == NULL) {
        return;
    }

    /* TODO: Store custom probability and use in hybrid_select() */
    (void)lottery_prob_q16; /* Unused for now */

    printf("Note: Custom probability setting not yet implemented.\n");
    printf("      Using default 80/20 split.\n");
}

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Compare hybrid vs. pure lottery
 */
void example_hybrid_vs_lottery(void)
{
    printf("\n=== Example: Hybrid vs. Pure Lottery ===\n");
    printf("3 tasks: High (200 tickets), Med (100 tickets), Low (1 ticket)\n");
    printf("Low-priority task should run more often with hybrid\n\n");

    /* Setup DAG */
    dag_pdac_t dag;
    resource_vector_t quota = {.cpu = Q16(6.0), .memory = Q16(1024.0)};
    pdac_dag_init(&dag, quota);

    resource_vector_t res_high = {.cpu = Q16(2.0), .memory = Q16(400.0)};
    resource_vector_t res_med = {.cpu = Q16(1.0), .memory = Q16(200.0)};
    resource_vector_t res_low = {.cpu = Q16(0.01), .memory = Q16(10.0)};

    int high = pdac_dag_add_task(&dag, "High Priority", res_high);
    int med = pdac_dag_add_task(&dag, "Medium Priority", res_med);
    int low = pdac_dag_add_task(&dag, "Low Priority (tiny!)", res_low);

    dag.tasks[high].state = TASK_STATE_READY;
    dag.tasks[med].state = TASK_STATE_READY;
    dag.tasks[low].state = TASK_STATE_READY;

    /* Test 1: Pure lottery */
    printf("Pure Lottery (1000 selections):\n");
    lcg_state_t rng1;
    lcg_init(&rng1, 42);

    lottery_scheduler_t pure_lottery;
    lottery_init(&pure_lottery, &rng1);
    lottery_recompute_all_tickets(&pure_lottery, &dag);

    for (int i = 0; i < 1000; i++) {
        lottery_select(&pure_lottery, &dag);
    }

    printf("  Low task selected: %llu times (%.1f%%)\n",
           lottery_get_selection_count(&pure_lottery, low),
           (lottery_get_selection_count(&pure_lottery, low) * 100.0) / 1000.0);

    /* Test 2: Hybrid */
    printf("\nHybrid Scheduler (1000 selections):\n");
    lcg_state_t rng2;
    lcg_init(&rng2, 42);

    hybrid_scheduler_t hybrid;
    hybrid_init(&hybrid, &rng2);
    hybrid_recompute_all_tasks(&hybrid, &dag);

    for (int i = 0; i < 1000; i++) {
        hybrid_select(&hybrid, &dag);
    }

    printf("  Low task selected: %llu times (%.1f%%)\n",
           hybrid_get_task_selection_count(&hybrid, low),
           (hybrid_get_task_selection_count(&hybrid, low) * 100.0) / 1000.0);

    printf("\nNote: Hybrid scheduler gives low-priority task more chances\n");
    printf("      (Beatty component prevents starvation)\n");
    printf("=====================================\n\n");
}

/**
 * Example: Demonstrate starvation-freedom
 */
void example_hybrid_starvation_free(void)
{
    printf("\n=== Example: Starvation-Freedom ===\n");
    printf("Task with 0 effective priority still runs regularly\n\n");

    /* Setup DAG with extreme priority imbalance */
    dag_pdac_t dag;
    resource_vector_t quota = {.cpu = Q16(10.0), .memory = Q16(2048.0)};
    pdac_dag_init(&dag, quota);

    resource_vector_t res_giant = {.cpu = Q16(9.0), .memory = Q16(1800.0)};
    resource_vector_t res_tiny = {.cpu = Q16(0.001), .memory = Q16(1.0)};

    int giant = pdac_dag_add_task(&dag, "Giant (99.9% resources)", res_giant);
    int tiny = pdac_dag_add_task(&dag, "Tiny (0.1% resources)", res_tiny);

    dag.tasks[giant].state = TASK_STATE_READY;
    dag.tasks[tiny].state = TASK_STATE_READY;

    /* Run hybrid scheduler */
    lcg_state_t rng;
    lcg_init(&rng, 12345);

    hybrid_scheduler_t sched;
    hybrid_init(&sched, &rng);
    hybrid_recompute_all_tasks(&sched, &dag);

    printf("Running 1000 scheduling decisions...\n");
    for (int i = 0; i < 1000; i++) {
        hybrid_select(&sched, &dag);
    }

    hybrid_print_stats(&sched, &dag);

    printf("Expected: Tiny task runs ~10%% of time (thanks to Beatty)\n");
    printf("          Pure lottery would give it ~0.1%%\n");
    printf("=====================================\n\n");
}

/**
 * Example: Fairness analysis
 */
void example_hybrid_fairness(void)
{
    printf("\n=== Example: Fairness Analysis ===\n");
    printf("Verify that CPU time ≈ proportional to tickets\n\n");

    /* Setup DAG with known ticket ratios */
    dag_pdac_t dag;
    resource_vector_t quota = {.cpu = Q16(6.0), .memory = Q16(1024.0)};
    pdac_dag_init(&dag, quota);

    /* Task A: 1x tickets */
    resource_vector_t res_a = {.cpu = Q16(1.0), .memory = Q16(100.0)};
    int task_a = pdac_dag_add_task(&dag, "Task A (1x)", res_a);
    dag.tasks[task_a].state = TASK_STATE_READY;

    /* Task B: 2x tickets */
    resource_vector_t res_b = {.cpu = Q16(2.0), .memory = Q16(200.0)};
    int task_b = pdac_dag_add_task(&dag, "Task B (2x)", res_b);
    dag.tasks[task_b].state = TASK_STATE_READY;

    /* Task C: 3x tickets */
    resource_vector_t res_c = {.cpu = Q16(3.0), .memory = Q16(300.0)};
    int task_c = pdac_dag_add_task(&dag, "Task C (3x)", res_c);
    dag.tasks[task_c].state = TASK_STATE_READY;

    /* Run hybrid scheduler */
    lcg_state_t rng;
    lcg_init(&rng, 99999);

    hybrid_scheduler_t sched;
    hybrid_init(&sched, &rng);
    hybrid_recompute_all_tasks(&sched, &dag);

    for (int i = 0; i < 1000; i++) {
        hybrid_select(&sched, &dag);
    }

    hybrid_print_stats(&sched, &dag);

    printf("Expected ratios: A:B:C ≈ 1:2:3 (with small variance from Beatty)\n");
    printf("Fairness ratio close to 1.0 = good fairness\n");
    printf("=====================================\n\n");
}

/**
 * Example: Effect of mode probability tuning
 */
void example_hybrid_tuning(void)
{
    printf("\n=== Example: Mode Probability Tuning ===\n");
    printf("Compare different lottery/Beatty splits\n\n");

    /* Setup simple DAG */
    dag_pdac_t dag;
    resource_vector_t quota = {.cpu = Q16(4.0), .memory = Q16(512.0)};
    pdac_dag_init(&dag, quota);

    resource_vector_t res = {.cpu = Q16(1.0), .memory = Q16(128.0)};
    for (int i = 0; i < 4; i++) {
        char name[32];
        snprintf(name, sizeof(name), "Task %d", i);
        int id = pdac_dag_add_task(&dag, name, res);
        dag.tasks[id].state = TASK_STATE_READY;
    }

    /* Test default 80/20 split */
    lcg_state_t rng;
    lcg_init(&rng, 777);

    hybrid_scheduler_t sched;
    hybrid_init(&sched, &rng);
    hybrid_recompute_all_tasks(&sched, &dag);

    for (int i = 0; i < 500; i++) {
        hybrid_select(&sched, &dag);
    }

    printf("Default 80/20 split:\n");
    printf("  Lottery: %llu selections\n", hybrid_get_lottery_count(&sched));
    printf("  Beatty:  %llu selections\n", hybrid_get_beatty_count(&sched));
    printf("  Ratio:   %.2f (expected 4.0)\n\n",
           (double)hybrid_compute_mode_ratio(&sched) / 65536.0);

    printf("Note: Custom probability tuning not yet implemented\n");
    printf("      See hybrid_set_mode_probability() for future work\n");
    printf("=====================================\n\n");
}

/**
 * Run all hybrid scheduler examples
 */
void hybrid_run_all_examples(void)
{
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   HYBRID LOTTERY+BEATTY SCHEDULER - EXAMPLES               ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n");

    example_hybrid_vs_lottery();
    example_hybrid_starvation_free();
    example_hybrid_fairness();
    example_hybrid_tuning();

    printf("All hybrid scheduler examples completed.\n");
    printf("See include/sched_hybrid.h for API documentation.\n\n");
}
