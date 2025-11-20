/**
 * @file sched_lottery.c
 * @brief Lottery Scheduler Implementation
 *
 * @see include/sched_lottery.h for API documentation
 */

#include "sched_lottery.h"
#include "resource_vector.h"
#include "printf.h"
#include <stdint.h>
#include <string.h>

/*******************************************************************************
 * HELPER FUNCTIONS
 ******************************************************************************/

/**
 * Compute ticket count from resource vector norm
 *
 * Formula: tickets = norm * BASE_TICKETS
 * Clamped to [MIN_TICKETS, MAX_TICKETS]
 */
static uint32_t compute_tickets_from_norm(q16_t norm)
{
    /* Convert Q16 norm to tickets */
    uint32_t tickets = (norm * LOTTERY_BASE_TICKETS) >> 16;

    /* Clamp to valid range */
    if (tickets < LOTTERY_MIN_TICKETS) {
        tickets = LOTTERY_MIN_TICKETS;
    }
    if (tickets > LOTTERY_MAX_TICKETS) {
        tickets = LOTTERY_MAX_TICKETS;
    }

    return tickets;
}

/*******************************************************************************
 * CORE API IMPLEMENTATION
 ******************************************************************************/

/**
 * Initialize lottery scheduler
 */
void lottery_init(lottery_scheduler_t *sched, lcg_state_t *rng)
{
    if (sched == NULL || rng == NULL) {
        return;
    }

    sched->rng = rng;
    sched->total_tickets = 0;
    sched->total_selections = 0;

    /* Zero out all ticket and selection counts */
    memset(sched->tickets, 0, sizeof(sched->tickets));
    memset(sched->selections, 0, sizeof(sched->selections));
}

/**
 * Update tickets for a single task
 */
void lottery_update_tickets(
    lottery_scheduler_t *sched,
    uint16_t task_id,
    const dag_task_t *task)
{
    if (sched == NULL || task == NULL || task_id >= DAG_MAX_TASKS) {
        return;
    }

    /* Compute octonion norm of resource vector */
    q16_t norm = resource_vector_norm(task->resources);

    /* Convert norm to ticket count */
    uint32_t tickets = compute_tickets_from_norm(norm);

    /* Update ticket count */
    sched->tickets[task_id] = tickets;
}

/**
 * Recompute all tickets for tasks in DAG
 */
void lottery_recompute_all_tickets(
    lottery_scheduler_t *sched,
    const dag_pdac_t *dag)
{
    if (sched == NULL || dag == NULL) {
        return;
    }

    for (uint16_t i = 0; i < dag->num_tasks; i++) {
        lottery_update_tickets(sched, i, &dag->tasks[i]);
    }
}

/**
 * Select next task to run using lottery scheduling
 *
 * ALGORITHM WALKTHROUGH:
 * =====================
 * Example: 3 ready tasks
 *   Task 0: 100 tickets, state=READY
 *   Task 1: 200 tickets, state=READY
 *   Task 2:  50 tickets, state=RUNNING (skip)
 *   Total ready: 300 tickets
 *
 * 1. Generate random in [0, 300):  random = 175
 * 2. Walk tasks:
 *    - Task 0: 175 - 100 = 75   (skip)
 *    - Task 1: 75 - 200 < 0     (SELECT Task 1!)
 *
 * Task 1 wins the lottery!
 */
dag_task_t *lottery_select(
    lottery_scheduler_t *sched,
    dag_pdac_t *dag)
{
    if (sched == NULL || dag == NULL) {
        return NULL;
    }

    /* Step 1: Count total tickets for READY tasks */
    uint32_t total_tickets = 0;
    for (uint16_t i = 0; i < dag->num_tasks; i++) {
        if (dag->tasks[i].state == TASK_STATE_READY) {
            total_tickets += sched->tickets[i];
        }
    }

    /* No ready tasks? */
    if (total_tickets == 0) {
        return NULL;
    }

    /* Step 2: Generate random ticket number */
    uint32_t winning_ticket = lcg_range(sched->rng, total_tickets);

    /* Step 3: Find winner by walking tasks and subtracting tickets */
    uint32_t accumulated = 0;
    for (uint16_t i = 0; i < dag->num_tasks; i++) {
        if (dag->tasks[i].state != TASK_STATE_READY) {
            continue; /* Skip non-ready tasks */
        }

        accumulated += sched->tickets[i];

        if (winning_ticket < accumulated) {
            /* Found the winner! */
            sched->selections[i]++;
            sched->total_selections++;
            sched->total_tickets = total_tickets; /* Cache for stats */

            return &dag->tasks[i];
        }
    }

    /* Should never reach here (logic error if we do) */
    return NULL;
}

/*******************************************************************************
 * STATISTICS & INTROSPECTION
 ******************************************************************************/

uint32_t lottery_get_tickets(
    const lottery_scheduler_t *sched,
    uint16_t task_id)
{
    if (sched == NULL || task_id >= DAG_MAX_TASKS) {
        return 0;
    }
    return sched->tickets[task_id];
}

uint32_t lottery_get_total_tickets(const lottery_scheduler_t *sched)
{
    return sched ? sched->total_tickets : 0;
}

uint64_t lottery_get_selection_count(
    const lottery_scheduler_t *sched,
    uint16_t task_id)
{
    if (sched == NULL || task_id >= DAG_MAX_TASKS) {
        return 0;
    }
    return sched->selections[task_id];
}

/**
 * Compute fairness ratio
 *
 * Fairness ratio = (actual selections) / (expected selections)
 * Expected selections = (task_tickets / total_tickets) * total_selections
 *
 * Ratio = 1.0 → perfect fairness
 * Ratio < 1.0 → task underserved
 * Ratio > 1.0 → task overserved
 */
q16_t lottery_compute_fairness(
    const lottery_scheduler_t *sched,
    uint16_t task_id)
{
    if (sched == NULL || task_id >= DAG_MAX_TASKS) {
        return 0;
    }

    if (sched->total_selections == 0 || sched->total_tickets == 0) {
        return Q16(1.0); /* No data yet, assume fair */
    }

    /* Expected selections = (tickets / total) * total_selections */
    uint64_t expected = ((uint64_t)sched->tickets[task_id] *
                         sched->total_selections) /
                        sched->total_tickets;

    if (expected == 0) {
        return Q16(1.0); /* Avoid division by zero */
    }

    /* Ratio = actual / expected */
    uint64_t actual = sched->selections[task_id];
    q16_t ratio = ((actual << 16) / expected);

    return ratio;
}

/**
 * Print lottery scheduler statistics
 */
void lottery_print_stats(
    const lottery_scheduler_t *sched,
    const dag_pdac_t *dag)
{
    if (sched == NULL || dag == NULL) {
        return;
    }

    printf("\n=== Lottery Scheduler Statistics ===\n");
    printf("Total selections: %llu\n", sched->total_selections);
    printf("Total tickets: %u\n\n", sched->total_tickets);

    printf("%-4s %-20s %-8s %-12s %-12s %-10s\n",
           "ID", "Name", "Tickets", "Selections", "Expected", "Fairness");
    printf("----------------------------------------------------------------\n");

    for (uint16_t i = 0; i < dag->num_tasks; i++) {
        uint32_t tickets = sched->tickets[i];
        uint64_t selections = sched->selections[i];

        if (tickets == 0 && selections == 0) {
            continue; /* Skip tasks with no activity */
        }

        /* Compute expected selections */
        uint64_t expected = 0;
        if (sched->total_tickets > 0) {
            expected = ((uint64_t)tickets * sched->total_selections) /
                       sched->total_tickets;
        }

        /* Compute fairness ratio */
        q16_t fairness = lottery_compute_fairness(sched, i);

        printf("%-4u %-20s %-8u %-12llu %-12llu %.2f\n",
               i,
               dag->tasks[i].name,
               tickets,
               selections,
               expected,
               (double)fairness / 65536.0);
    }

    printf("\n");
}

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Lottery fairness
 *
 * Create 3 tasks with different resource requirements:
 * - Task A: Small (50 tickets)
 * - Task B: Medium (100 tickets)
 * - Task C: Large (200 tickets)
 *
 * Run lottery 1000 times, verify CPU time matches ticket ratios.
 */
void example_lottery_fairness(void)
{
    printf("\n=== Example: Lottery Fairness ===\n");
    printf("Testing proportional CPU time allocation\n\n");

    /* Initialize DAG and scheduler */
    dag_pdac_t dag;
    resource_vector_t quota = {
        .cpu = Q16(10.0),
        .memory = Q16(1024.0),
        .io_bandwidth = 0,
        .network_bandwidth = 0,
        .gpu_time = 0,
        .disk_quota = 0,
        .irq_count = 0,
        .capability_count = 0
    };
    pdac_dag_init(&dag, quota);

    /* Add 3 tasks with different resource requirements */
    resource_vector_t res_a = {.cpu = Q16(0.5), .memory = Q16(100.0)};
    resource_vector_t res_b = {.cpu = Q16(1.0), .memory = Q16(200.0)};
    resource_vector_t res_c = {.cpu = Q16(2.0), .memory = Q16(400.0)};

    int task_a = pdac_dag_add_task(&dag, "Task A (small)", res_a);
    int task_b = pdac_dag_add_task(&dag, "Task B (medium)", res_b);
    int task_c = pdac_dag_add_task(&dag, "Task C (large)", res_c);

    /* Mark all tasks as ready */
    dag.tasks[task_a].state = TASK_STATE_READY;
    dag.tasks[task_b].state = TASK_STATE_READY;
    dag.tasks[task_c].state = TASK_STATE_READY;

    /* Initialize lottery scheduler */
    lcg_state_t rng;
    lcg_init(&rng, 42);

    lottery_scheduler_t sched;
    lottery_init(&sched, &rng);
    lottery_recompute_all_tickets(&sched, &dag);

    printf("Task A tickets: %u\n", lottery_get_tickets(&sched, task_a));
    printf("Task B tickets: %u\n", lottery_get_tickets(&sched, task_b));
    printf("Task C tickets: %u\n", lottery_get_tickets(&sched, task_c));
    printf("\n");

    /* Run lottery 1000 times */
    printf("Running lottery 1000 times...\n");
    for (int i = 0; i < 1000; i++) {
        dag_task_t *winner = lottery_select(&sched, &dag);
        (void)winner; /* Winner recorded in statistics */
    }

    /* Print results */
    lottery_print_stats(&sched, &dag);

    printf("Expected: CPU time proportional to ticket count\n");
    printf("======================================\n\n");
}

/**
 * Example: Effect of ticket ratios
 *
 * Demonstrates how doubling tickets doubles CPU time.
 */
void example_lottery_ratios(void)
{
    printf("\n=== Example: Ticket Ratios → CPU Ratios ===\n");
    printf("Task A: 100 tickets, Task B: 200 tickets (2x ratio)\n\n");

    /* Setup DAG with 2 tasks */
    dag_pdac_t dag;
    resource_vector_t quota = {.cpu = Q16(4.0), .memory = Q16(512.0)};
    pdac_dag_init(&dag, quota);

    /* Task A: 1.0 CPU norm → ~100 tickets */
    resource_vector_t res_a = {.cpu = Q16(1.0), .memory = 0};
    int task_a = pdac_dag_add_task(&dag, "Task A", res_a);
    dag.tasks[task_a].state = TASK_STATE_READY;

    /* Task B: 2.0 CPU norm → ~200 tickets */
    resource_vector_t res_b = {.cpu = Q16(2.0), .memory = 0};
    int task_b = pdac_dag_add_task(&dag, "Task B (2x)", res_b);
    dag.tasks[task_b].state = TASK_STATE_READY;

    /* Run lottery */
    lcg_state_t rng;
    lcg_init(&rng, 12345);

    lottery_scheduler_t sched;
    lottery_init(&sched, &rng);
    lottery_recompute_all_tickets(&sched, &dag);

    for (int i = 0; i < 1000; i++) {
        lottery_select(&sched, &dag);
    }

    lottery_print_stats(&sched, &dag);

    printf("Expected: Task B wins ~2x as often as Task A\n");
    printf("=========================================\n\n");
}

/**
 * Example: Lottery with DAG dependencies
 *
 * Shows that lottery only selects from READY tasks (dependencies satisfied).
 */
void example_lottery_dag(void)
{
    printf("\n=== Example: Lottery + DAG Dependencies ===\n");
    printf("Task B depends on Task A (must wait until A completes)\n\n");

    /* Setup DAG */
    dag_pdac_t dag;
    resource_vector_t quota = {.cpu = Q16(4.0), .memory = Q16(512.0)};
    pdac_dag_init(&dag, quota);

    /* Add tasks */
    resource_vector_t res = {.cpu = Q16(1.0), .memory = Q16(100.0)};
    int task_a = pdac_dag_add_task(&dag, "Task A", res);
    int task_b = pdac_dag_add_task(&dag, "Task B (depends on A)", res);
    int task_c = pdac_dag_add_task(&dag, "Task C (independent)", res);

    /* Add dependency: B depends on A */
    pdac_dag_add_dependency(&dag, task_b, task_a);

    /* Initial state: only A and C are ready */
    dag.tasks[task_a].state = TASK_STATE_READY;
    dag.tasks[task_b].state = TASK_STATE_PENDING; /* Waiting for A */
    dag.tasks[task_c].state = TASK_STATE_READY;

    /* Run lottery */
    lcg_state_t rng;
    lcg_init(&rng, 99999);

    lottery_scheduler_t sched;
    lottery_init(&sched, &rng);
    lottery_recompute_all_tickets(&sched, &dag);

    printf("Phase 1: A and C ready, B pending\n");
    for (int i = 0; i < 100; i++) {
        dag_task_t *winner = lottery_select(&sched, &dag);
        if (winner && winner->id == task_a && i == 50) {
            /* Simulate A completing halfway through */
            dag.tasks[task_a].state = TASK_STATE_COMPLETED;
            dag.tasks[task_b].state = TASK_STATE_READY;
            printf("  → Task A completed, Task B now ready\n");
        }
    }

    lottery_print_stats(&sched, &dag);

    printf("Note: Task B only wins after Task A completes\n");
    printf("============================================\n\n");
}

/**
 * Run all lottery examples
 */
void lottery_run_all_examples(void)
{
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   LOTTERY SCHEDULER - EXAMPLES                             ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n");

    example_lottery_fairness();
    example_lottery_ratios();
    example_lottery_dag();

    printf("All lottery scheduler examples completed.\n");
    printf("See include/sched_lottery.h for API documentation.\n\n");
}
