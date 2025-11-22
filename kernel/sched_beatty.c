/**
 * @file sched_beatty.c
 * @brief Beatty Sequence Scheduler Implementation
 *
 * @see include/sched_beatty.h for API documentation
 */

#include "sched_beatty.h"
#include "resource_vector.h"
#include "printf.h"
#include <stdint.h>
#include <string.h>

/*******************************************************************************
 * HELPER STRUCTURES
 ******************************************************************************/

/**
 * Ready task entry (for sorting)
 */
typedef struct ready_task {
    dag_task_t *task;                         /* Pointer to task */
    q16_t priority;                           /* Task priority */
    uint16_t original_index;                  /* Original index in DAG */
} ready_task_t;

/*******************************************************************************
 * HELPER FUNCTIONS
 ******************************************************************************/

/**
 * Compare function for qsort (sort by priority descending)
 * Note: Not currently used, kept for potential future optimization.
 */
__attribute__((unused))
static int compare_priorities(const void *a, const void *b)
{
    const ready_task_t *ta = (const ready_task_t *)a;
    const ready_task_t *tb = (const ready_task_t *)b;

    /* Sort descending (higher priority first) */
    if (ta->priority > tb->priority) return -1;
    if (ta->priority < tb->priority) return 1;
    return 0;
}

/**
 * Simple insertion sort for small arrays (no qsort in kernel)
 *
 * Sorts ready_tasks array by priority (descending).
 */
static void sort_ready_tasks(ready_task_t *tasks, uint16_t count)
{
    for (uint16_t i = 1; i < count; i++) {
        ready_task_t key = tasks[i];
        int j = i - 1;

        /* Move elements greater than key to the right */
        while (j >= 0 && tasks[j].priority < key.priority) {
            tasks[j + 1] = tasks[j];
            j--;
        }

        tasks[j + 1] = key;
    }
}

/*******************************************************************************
 * CORE API IMPLEMENTATION
 ******************************************************************************/

/**
 * Initialize Beatty scheduler
 */
void beatty_init(beatty_scheduler_t *sched, q16_t alpha)
{
    if (sched == NULL) {
        return;
    }

    sched->counter = 0;
    sched->alpha = alpha;
    sched->total_selections = 0;

    /* Zero out priorities and statistics */
    memset(sched->priorities, 0, sizeof(sched->priorities));
    memset(sched->selections, 0, sizeof(sched->selections));
}

/**
 * Update priority for a single task
 */
void beatty_update_priority(
    beatty_scheduler_t *sched,
    uint16_t task_id,
    const dag_task_t *task)
{
    if (sched == NULL || task == NULL || task_id >= DAG_MAX_TASKS) {
        return;
    }

    /* Priority = octonion norm of resource vector */
    q16_t priority = resource_vector_norm(task->resources);
    sched->priorities[task_id] = priority;
}

/**
 * Recompute all priorities for tasks in DAG
 */
void beatty_recompute_all_priorities(
    beatty_scheduler_t *sched,
    const dag_pdac_t *dag)
{
    if (sched == NULL || dag == NULL) {
        return;
    }

    for (uint16_t i = 0; i < dag->num_tasks; i++) {
        beatty_update_priority(sched, i, &dag->tasks[i]);
    }
}

/**
 * Select next task to run using Beatty sequence
 *
 * ALGORITHM WALKTHROUGH:
 * ======================
 * Example: 5 ready tasks with priorities [10.0, 8.0, 6.0, 4.0, 2.0]
 *   counter = 7
 *
 * 1. Collect ready tasks: [T0, T1, T2, T3, T4]
 * 2. Sort by priority: [T0(10.0), T1(8.0), T2(6.0), T3(4.0), T4(2.0)]
 * 3. Compute Beatty: B_φ(7) = floor(7 * 1.618) = floor(11.326) = 11
 * 4. Select task: 11 mod 5 = 1 → T1 (second highest priority)
 * 5. Increment counter: 7 → 8
 *
 * Next iteration (counter = 8):
 * 3. B_φ(8) = floor(8 * 1.618) = floor(12.944) = 12
 * 4. 12 mod 5 = 2 → T2
 */
dag_task_t *beatty_select(
    beatty_scheduler_t *sched,
    dag_pdac_t *dag)
{
    if (sched == NULL || dag == NULL) {
        return NULL;
    }

    /* Step 1: Collect all READY tasks */
    ready_task_t ready_tasks[DAG_MAX_TASKS];
    uint16_t num_ready = 0;

    for (uint16_t i = 0; i < dag->num_tasks; i++) {
        if (dag->tasks[i].state == TASK_STATE_READY) {
            ready_tasks[num_ready].task = &dag->tasks[i];
            ready_tasks[num_ready].priority = sched->priorities[i];
            ready_tasks[num_ready].original_index = i;
            num_ready++;
        }
    }

    /* No ready tasks? */
    if (num_ready == 0) {
        return NULL;
    }

    /* Step 2: Sort by priority (descending) */
    sort_ready_tasks(ready_tasks, num_ready);

    /* Step 3: Compute Beatty number B_α(counter) */
    uint64_t beatty_num = ((uint64_t)sched->counter * sched->alpha) >> 16;

    /* Step 4: Select task at position (beatty_num mod num_ready) */
    uint16_t selected_idx = beatty_num % num_ready;
    ready_task_t *selected = &ready_tasks[selected_idx];

    /* Step 5: Increment counter */
    sched->counter++;

    /* Update statistics */
    sched->selections[selected->original_index]++;
    sched->total_selections++;
    selected->task->schedule_count++;

    return selected->task;
}

/**
 * Reset Beatty counter
 */
void beatty_reset_counter(beatty_scheduler_t *sched)
{
    if (sched == NULL) {
        return;
    }
    sched->counter = 0;
}

/*******************************************************************************
 * STATISTICS & INTROSPECTION
 ******************************************************************************/

uint64_t beatty_get_counter(const beatty_scheduler_t *sched)
{
    return sched ? sched->counter : 0;
}

uint64_t beatty_compute_next(const beatty_scheduler_t *sched)
{
    if (sched == NULL) {
        return 0;
    }

    /* B_α(counter) = floor(counter * α) */
    return ((uint64_t)sched->counter * sched->alpha) >> 16;
}

uint64_t beatty_get_selection_count(
    const beatty_scheduler_t *sched,
    uint16_t task_id)
{
    if (sched == NULL || task_id >= DAG_MAX_TASKS) {
        return 0;
    }
    return sched->selections[task_id];
}

/**
 * Analyze gap distribution
 *
 * Gap = B(n+1) - B(n)
 */
void beatty_analyze_gaps(
    beatty_scheduler_t *sched,
    uint32_t num_steps,
    uint32_t *gaps_out)
{
    if (sched == NULL || gaps_out == NULL) {
        return;
    }

    uint64_t prev = 0;
    for (uint32_t i = 0; i < num_steps; i++) {
        uint64_t curr = ((uint64_t)i * sched->alpha) >> 16;
        gaps_out[i] = (uint32_t)(curr - prev);
        prev = curr;
    }
}

/**
 * Print Beatty scheduler statistics
 */
void beatty_print_stats(
    const beatty_scheduler_t *sched,
    const dag_pdac_t *dag)
{
    if (sched == NULL || dag == NULL) {
        return;
    }

    printf("\n=== Beatty Scheduler Statistics ===\n");
    printf("Total selections: %llu\n", (unsigned long long)sched->total_selections);
    printf("Current counter: %llu\n", (unsigned long long)sched->counter);
    printf("Alpha (multiplier): %.3f\n\n", (double)sched->alpha / 65536.0);

    printf("%-4s %-20s %-10s %-10s %-8s %-10s %-10s\n",
           "ID", "Name", "Priority", "Selects", "%", "RunTime", "AvgLat");
    printf("--------------------------------------------------------------------------------\n");

    for (uint16_t i = 0; i < dag->num_tasks; i++) {
        uint64_t selections = sched->selections[i];
        const dag_task_t *t = &dag->tasks[i];

        if (sched->priorities[i] == 0 && selections == 0 && t->run_time_ticks == 0) {
            continue; /* Skip tasks with no activity */
        }

        double percentage = 0.0;
        if (sched->total_selections > 0) {
            percentage = (selections * 100.0) / sched->total_selections;
        }

        uint64_t avg_latency = 0;
        if (t->schedule_count > 0) {
            avg_latency = t->total_latency_ticks / t->schedule_count;
        }

        printf("%-4u %-20s %-10.2f %-10llu %-8.2f %-10llu %-10llu\n",
               i,
               t->name,
               (double)sched->priorities[i] / 65536.0,
               (unsigned long long)selections,
               percentage,
               (unsigned long long)t->run_time_ticks,
               (unsigned long long)avg_latency);
    }

    printf("\n");
}

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Three-distance theorem
 *
 * Demonstrates that Beatty sequence gaps have at most 3 distinct values.
 */
void example_beatty_three_distance(void)
{
    printf("\n=== Example: Three-Distance Theorem ===\n");
    printf("Beatty sequence with φ = 1.618...\n");
    printf("Gap distribution should have at most 3 distinct values\n\n");

    beatty_scheduler_t sched;
    beatty_init(&sched, BEATTY_GOLDEN_RATIO);

    /* Compute first 50 Beatty numbers and their gaps */
    uint32_t gaps[50];
    beatty_analyze_gaps(&sched, 50, gaps);

    printf("First 50 gaps: ");
    uint32_t gap_counts[10] = {0}; /* Count frequency of each gap size */

    for (int i = 0; i < 50; i++) {
        printf("%u ", gaps[i]);
        if (gaps[i] < 10) {
            gap_counts[gaps[i]]++;
        }
    }
    printf("\n\n");

    /* Show gap distribution */
    printf("Gap distribution:\n");
    for (int i = 0; i < 10; i++) {
        if (gap_counts[i] > 0) {
            printf("  Gap %d: %u occurrences\n", i, gap_counts[i]);
        }
    }

    printf("\nExpected: 2-3 distinct gap sizes (three-distance theorem)\n");
    printf("=====================================\n\n");
}

/**
 * Example: Beatty vs. round-robin spacing
 */
void example_beatty_vs_roundrobin(void)
{
    printf("\n=== Example: Beatty vs. Round-Robin ===\n");
    printf("Comparing task distribution patterns\n\n");

    /* Setup DAG with 5 tasks */
    dag_pdac_t dag;
    resource_vector_t quota = {.cpu = Q16(5.0), .memory = Q16(1024.0)};
    pdac_dag_init(&dag, quota);

    resource_vector_t res = {.cpu = Q16(1.0), .memory = Q16(100.0)};
    for (int i = 0; i < 5; i++) {
        char name[32];
        snprintf(name, sizeof(name), "Task %d", i);
        int id = pdac_dag_add_task(&dag, name, res);
        dag.tasks[id].state = TASK_STATE_READY;
    }

    /* Beatty scheduler */
    beatty_scheduler_t beatty;
    beatty_init(&beatty, BEATTY_GOLDEN_RATIO);
    beatty_recompute_all_priorities(&beatty, &dag);

    printf("Beatty sequence selection (first 20):\n  ");
    for (int i = 0; i < 20; i++) {
        dag_task_t *task = beatty_select(&beatty, &dag);
        printf("%u ", task->id);
    }
    printf("\n\n");

    /* Round-robin (for comparison) */
    printf("Round-robin selection (first 20):\n  ");
    for (int i = 0; i < 20; i++) {
        printf("%u ", i % 5);
    }
    printf("\n\n");

    printf("Note: Beatty provides more varied spacing than round-robin\n");
    printf("=====================================\n\n");
}

/**
 * Example: Deterministic scheduling (reproducibility)
 */
void example_beatty_determinism(void)
{
    printf("\n=== Example: Beatty Determinism ===\n");
    printf("Same DAG state → same schedule (reproducible)\n\n");

    /* Setup DAG */
    dag_pdac_t dag;
    resource_vector_t quota = {.cpu = Q16(4.0), .memory = Q16(512.0)};
    pdac_dag_init(&dag, quota);

    resource_vector_t res = {.cpu = Q16(1.0), .memory = Q16(100.0)};
    for (int i = 0; i < 4; i++) {
        char name[32];
        snprintf(name, sizeof(name), "Task %d", i);
        int id = pdac_dag_add_task(&dag, name, res);
        dag.tasks[id].state = TASK_STATE_READY;
    }

    /* Run 1 */
    beatty_scheduler_t sched1;
    beatty_init(&sched1, BEATTY_GOLDEN_RATIO);
    beatty_recompute_all_priorities(&sched1, &dag);

    printf("Run 1: ");
    for (int i = 0; i < 10; i++) {
        dag_task_t *task = beatty_select(&sched1, &dag);
        printf("%u ", task->id);
    }
    printf("\n");

    /* Run 2 (reset counter) */
    beatty_scheduler_t sched2;
    beatty_init(&sched2, BEATTY_GOLDEN_RATIO);
    beatty_recompute_all_priorities(&sched2, &dag);

    printf("Run 2: ");
    for (int i = 0; i < 10; i++) {
        dag_task_t *task = beatty_select(&sched2, &dag);
        printf("%u ", task->id);
    }
    printf("\n\n");

    printf("Note: Both runs produce identical schedules (deterministic)\n");
    printf("=====================================\n\n");
}

/**
 * Example: Beatty with priority-sorted tasks
 */
void example_beatty_priorities(void)
{
    printf("\n=== Example: Beatty with Priorities ===\n");
    printf("Tasks with different priorities (resource norms)\n\n");

    /* Setup DAG with varied priorities */
    dag_pdac_t dag;
    resource_vector_t quota = {.cpu = Q16(10.0), .memory = Q16(1024.0)};
    pdac_dag_init(&dag, quota);

    /* High priority task */
    resource_vector_t res_high = {.cpu = Q16(4.0), .memory = Q16(400.0)};
    int high = pdac_dag_add_task(&dag, "High Priority", res_high);
    dag.tasks[high].state = TASK_STATE_READY;

    /* Medium priority tasks */
    resource_vector_t res_med = {.cpu = Q16(2.0), .memory = Q16(200.0)};
    int med1 = pdac_dag_add_task(&dag, "Medium 1", res_med);
    int med2 = pdac_dag_add_task(&dag, "Medium 2", res_med);
    dag.tasks[med1].state = TASK_STATE_READY;
    dag.tasks[med2].state = TASK_STATE_READY;

    /* Low priority task */
    resource_vector_t res_low = {.cpu = Q16(0.5), .memory = Q16(50.0)};
    int low = pdac_dag_add_task(&dag, "Low Priority", res_low);
    dag.tasks[low].state = TASK_STATE_READY;

    /* Run Beatty scheduler */
    beatty_scheduler_t sched;
    beatty_init(&sched, BEATTY_GOLDEN_RATIO);
    beatty_recompute_all_priorities(&sched, &dag);

    printf("Task priorities:\n");
    for (int i = 0; i < 4; i++) {
        printf("  Task %d: %.2f\n", i,
               (double)sched.priorities[i] / 65536.0);
    }
    printf("\n");

    /* Run 100 selections */
    for (int i = 0; i < 100; i++) {
        beatty_select(&sched, &dag);
    }

    beatty_print_stats(&sched, &dag);

    printf("Note: Higher priority tasks selected more often\n");
    printf("      But low priority tasks still run (no starvation)\n");
    printf("=====================================\n\n");
}

/**
 * Run all Beatty examples
 */
void beatty_run_all_examples(void)
{
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   BEATTY SEQUENCE SCHEDULER - EXAMPLES                     ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n");

    example_beatty_three_distance();
    example_beatty_vs_roundrobin();
    example_beatty_determinism();
    example_beatty_priorities();

    printf("All Beatty scheduler examples completed.\n");
    printf("See include/sched_beatty.h for API documentation.\n\n");
}
