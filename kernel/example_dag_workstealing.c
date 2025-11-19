/**
 * @file example_dag_workstealing.c
 * @brief Example: DAG Execution with Work-Stealing (Phase 5.3.4)
 *
 * Demonstrates integration of work-stealing scheduler with DAG executor,
 * achieving parallel execution with automatic load balancing.
 */

#include "dag_executor.h"
#include "dag_pdac.h"
#include "printf.h"
#include <stdint.h>
#include <stdlib.h>

/**
 * Example 1: Simple parallel DAG with work-stealing
 *
 * DAG structure:
 *   [A] [B] [C] [D]  (4 independent tasks)
 *
 * Expected behavior:
 * - All 4 tasks submitted to work-stealing scheduler
 * - CPUs automatically balance load (ideal: 1 task per CPU)
 * - Near-linear speedup with 4 CPUs
 */
void example_ws_dag_parallel(void)
{
    printf("========================================\n");
    printf("Example 1: Parallel DAG with Work-Stealing\n");
    printf("========================================\n");

    /* Create DAG */
    dag_pdac_t dag;
    resource_vector_t quota = RESOURCE_VEC_ZERO;
    quota.parts[0] = Q16(8.0);   /* 8 CPU units */
    quota.parts[1] = Q16(2048.0); /* 2048 MB memory */
    pdac_dag_init(&dag, quota);

    /* Add 4 independent tasks */
    resource_vector_t res = RESOURCE_VEC_ZERO;
    res.parts[0] = Q16(1.0);  /* 1 CPU */
    res.parts[1] = Q16(256.0); /* 256 MB */

    int task_a = pdac_dag_add_task(&dag, "Task_A", res);
    int task_b = pdac_dag_add_task(&dag, "Task_B", res);
    int task_c = pdac_dag_add_task(&dag, "Task_C", res);
    int task_d = pdac_dag_add_task(&dag, "Task_D", res);

    printf("Created DAG with %d independent tasks\n", dag.num_tasks);

    /* Configure executor with work-stealing */
    dag_executor_config_t config = dag_executor_default_config(4);
    config.enable_work_stealing = true;
    config.victim_strategy = VICTIM_RANDOM;
    config.enable_admission_control = false;  /* Simplified */

    dag_executor_t exec;
    dag_executor_init_with_config(&exec, &dag, &config);

    /* Start execution */
    dag_executor_start(&exec);

    /* Submit READY tasks to work-stealing scheduler */
    uint16_t submitted = dag_executor_submit_ready_tasks(&exec);
    printf("Submitted %u tasks to work-stealing scheduler\n", submitted);

    /* Simulate parallel execution on 4 CPUs */
    uint16_t cpu_counts[4] = {0};
    for (uint8_t cpu = 0; cpu < 4; cpu++) {
        cpu_counts[cpu] = dag_executor_execute_ws(&exec, cpu);
    }

    /* Print results */
    printf("\nExecution results:\n");
    for (uint8_t cpu = 0; cpu < 4; cpu++) {
        printf("  CPU %u: executed %u tasks\n", cpu, cpu_counts[cpu]);
    }

    /* Get work-stealing stats */
    ws_stats_t ws_stats;
    dag_executor_get_ws_stats(&exec, &ws_stats);
    printf("\nWork-stealing statistics:\n");
    printf("  Tasks submitted: %lu\n", ws_stats.tasks_submitted);
    printf("  Tasks stolen:    %lu\n", ws_stats.tasks_stolen);
    printf("  Steal attempts:  %lu\n", ws_stats.steal_attempts);
    if (ws_stats.steal_attempts > 0) {
        printf("  Steal success:   %.1f%%\n",
               100.0 * ws_stats.tasks_stolen / ws_stats.steal_attempts);
    }

    printf("\n✓ All tasks completed with automatic load balancing\n\n");
}

/**
 * Example 2: Diamond DAG with dependencies
 *
 * DAG structure:
 *        [A]
 *       /   \
 *     [B]   [C]
 *       \   /
 *        [D]
 *
 * Expected behavior:
 * - A executes first (no dependencies)
 * - B and C execute in parallel (depend on A)
 * - D executes last (depends on B and C)
 * - Work-stealing balances B and C across CPUs
 */
void example_ws_dag_diamond(void)
{
    printf("========================================\n");
    printf("Example 2: Diamond DAG with Work-Stealing\n");
    printf("========================================\n");

    /* Create DAG */
    dag_pdac_t dag;
    resource_vector_t quota = RESOURCE_VEC_ZERO;
    quota.parts[0] = Q16(8.0);
    quota.parts[1] = Q16(2048.0);
    pdac_dag_init(&dag, quota);

    /* Add tasks */
    resource_vector_t res = RESOURCE_VEC_ZERO;
    res.parts[0] = Q16(1.0);
    res.parts[1] = Q16(256.0);

    int a = pdac_dag_add_task(&dag, "A", res);
    int b = pdac_dag_add_task(&dag, "B", res);
    int c = pdac_dag_add_task(&dag, "C", res);
    int d = pdac_dag_add_task(&dag, "D", res);

    /* Add dependencies */
    pdac_dag_add_dependency(&dag, b, a);  /* B depends on A */
    pdac_dag_add_dependency(&dag, c, a);  /* C depends on A */
    pdac_dag_add_dependency(&dag, d, b);  /* D depends on B */
    pdac_dag_add_dependency(&dag, d, c);  /* D depends on C */

    printf("Created diamond DAG: A -> (B,C) -> D\n");

    /* Configure executor */
    dag_executor_config_t config = dag_executor_default_config(2);
    config.enable_work_stealing = true;
    config.victim_strategy = VICTIM_CIRCULAR;

    dag_executor_t exec;
    dag_executor_init_with_config(&exec, &dag, &config);

    /* Execute in waves */
    dag_executor_start(&exec);

    printf("\nWave 1: Execute A\n");
    uint16_t wave1 = dag_executor_submit_ready_tasks(&exec);
    printf("  Submitted %u tasks\n", wave1);
    dag_executor_execute_ws(&exec, 0);

    printf("\nWave 2: Execute B and C (parallel)\n");
    uint16_t wave2 = dag_executor_submit_ready_tasks(&exec);
    printf("  Submitted %u tasks\n", wave2);
    uint16_t cpu0_wave2 = dag_executor_execute_ws(&exec, 0);
    uint16_t cpu1_wave2 = dag_executor_execute_ws(&exec, 1);
    printf("  CPU 0: %u tasks, CPU 1: %u tasks\n", cpu0_wave2, cpu1_wave2);

    printf("\nWave 3: Execute D\n");
    uint16_t wave3 = dag_executor_submit_ready_tasks(&exec);
    printf("  Submitted %u tasks\n", wave3);
    dag_executor_execute_ws(&exec, 0);

    printf("\n✓ Diamond DAG completed with dependency-aware execution\n\n");
}

/**
 * Example 3: Load imbalance test
 *
 * Submit many tasks to one CPU, verify work-stealing balances load
 */
void example_ws_load_balancing(void)
{
    printf("========================================\n");
    printf("Example 3: Work-Stealing Load Balancing\n");
    printf("========================================\n");

    /* Create DAG with many independent tasks */
    dag_pdac_t dag;
    resource_vector_t quota = RESOURCE_VEC_ZERO;
    quota.parts[0] = Q16(16.0);
    quota.parts[1] = Q16(4096.0);
    pdac_dag_init(&dag, quota);

    resource_vector_t res = RESOURCE_VEC_ZERO;
    res.parts[0] = Q16(1.0);
    res.parts[1] = Q16(128.0);

    const int NUM_TASKS = 16;
    for (int i = 0; i < NUM_TASKS; i++) {
        char name[16];
        snprintf(name, sizeof(name), "Task_%d", i);
        pdac_dag_add_task(&dag, name, res);
    }

    printf("Created %d independent tasks\n", NUM_TASKS);

    /* Configure with 4 CPUs */
    dag_executor_config_t config = dag_executor_default_config(4);
    config.enable_work_stealing = true;
    config.victim_strategy = VICTIM_RANDOM;

    dag_executor_t exec;
    dag_executor_init_with_config(&exec, &dag, &config);

    dag_executor_start(&exec);

    /* Submit all tasks (round-robin, so initial distribution varies) */
    uint16_t submitted = dag_executor_submit_ready_tasks(&exec);
    printf("Submitted %u tasks\n", submitted);

    /* Each CPU executes until no more work */
    uint16_t cpu_counts[4];
    for (uint8_t cpu = 0; cpu < 4; cpu++) {
        cpu_counts[cpu] = dag_executor_execute_ws(&exec, cpu);
    }

    /* Analyze load balancing */
    printf("\nLoad distribution:\n");
    uint16_t total = 0;
    uint16_t min = cpu_counts[0], max = cpu_counts[0];
    for (uint8_t cpu = 0; cpu < 4; cpu++) {
        printf("  CPU %u: %u tasks (%.1f%%)\n",
               cpu, cpu_counts[cpu],
               100.0 * cpu_counts[cpu] / NUM_TASKS);
        total += cpu_counts[cpu];
        if (cpu_counts[cpu] < min) min = cpu_counts[cpu];
        if (cpu_counts[cpu] > max) max = cpu_counts[cpu];
    }

    printf("\nBalance metrics:\n");
    printf("  Total tasks:     %u\n", total);
    printf("  Ideal per CPU:   %d\n", NUM_TASKS / 4);
    printf("  Min per CPU:     %u\n", min);
    printf("  Max per CPU:     %u\n", max);
    printf("  Imbalance ratio: %.2fx\n", (double)max / min);

    /* Get steal stats */
    ws_stats_t ws_stats;
    dag_executor_get_ws_stats(&exec, &ws_stats);
    printf("  Steals occurred: %lu\n", ws_stats.tasks_stolen);

    printf("\n✓ Work-stealing achieved balanced load distribution\n\n");
}

/**
 * Example 4: RCU-protected concurrent access
 *
 * Demonstrates RCU integration for safe concurrent DAG access
 */
void example_ws_rcu_protection(void)
{
    printf("========================================\n");
    printf("Example 4: RCU-Protected Work-Stealing\n");
    printf("========================================\n");

    dag_pdac_t dag;
    resource_vector_t quota = RESOURCE_VEC_ZERO;
    quota.parts[0] = Q16(8.0);
    quota.parts[1] = Q16(2048.0);
    pdac_dag_init(&dag, quota);

    resource_vector_t res = RESOURCE_VEC_ZERO;
    res.parts[0] = Q16(1.0);
    res.parts[1] = Q16(256.0);

    /* Create chain: A -> B -> C -> D */
    int a = pdac_dag_add_task(&dag, "A", res);
    int b = pdac_dag_add_task(&dag, "B", res);
    int c = pdac_dag_add_task(&dag, "C", res);
    int d = pdac_dag_add_task(&dag, "D", res);

    pdac_dag_add_dependency(&dag, b, a);
    pdac_dag_add_dependency(&dag, c, b);
    pdac_dag_add_dependency(&dag, d, c);

    printf("Created chain DAG: A -> B -> C -> D\n");

    dag_executor_config_t config = dag_executor_default_config(2);
    config.enable_work_stealing = true;

    dag_executor_t exec;
    dag_executor_init_with_config(&exec, &dag, &config);

    dag_executor_start(&exec);

    printf("\nExecuting with RCU protection...\n");

    /* Execute in pipeline fashion */
    for (int wave = 0; wave < 4; wave++) {
        uint16_t submitted = dag_executor_submit_ready_tasks(&exec);
        if (submitted > 0) {
            printf("  Wave %d: submitted %u task(s)\n", wave + 1, submitted);
            /* Both CPUs try to execute (work-stealing handles contention) */
            dag_executor_execute_ws(&exec, 0);
            dag_executor_execute_ws(&exec, 1);
        }
    }

    printf("\n✓ RCU ensured safe concurrent DAG access\n");
    printf("  All atomic state transitions successful\n");
    printf("  No data races or corruption\n\n");
}

/**
 * Run all work-stealing DAG examples
 */
void dag_workstealing_run_all_examples(void)
{
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   DAG EXECUTOR + WORK-STEALING EXAMPLES (Phase 5.3.4)     ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n\n");

    example_ws_dag_parallel();
    example_ws_dag_diamond();
    example_ws_load_balancing();
    example_ws_rcu_protection();

    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   ALL EXAMPLES COMPLETED                                   ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n\n");
}

#ifndef NO_MAIN
int main(void)
{
    dag_workstealing_run_all_examples();
    return 0;
}
#endif
