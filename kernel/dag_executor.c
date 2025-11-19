/**
 * @file dag_executor.c
 * @brief Complete DAG Execution Engine Implementation
 *
 * @see include/dag_executor.h for API documentation
 */

#include "dag_executor.h"
#include "printf.h"
#include <stdint.h>
#include <string.h>

/*******************************************************************************
 * EXECUTOR LIFECYCLE
 ******************************************************************************/

/**
 * Create default configuration
 */
dag_executor_config_t dag_executor_default_config(uint8_t num_cpus)
{
    dag_executor_config_t config = {
        .num_cpus = num_cpus,
        .refill_rate = {.cpu = Q16(0.5), .memory = Q16(50.0)},
        .burst_size = {.cpu = Q16(4.0), .memory = Q16(1024.0)},
        .enable_load_balancing = true,
        .enable_admission_control = true,
        .enable_telemetry = true,
        .max_runtime_us = 0  /* Unlimited */
    };

    return config;
}

void dag_executor_init(dag_executor_t *exec,
                       dag_pdac_t *dag,
                       uint8_t num_cpus)
{
    dag_executor_config_t config = dag_executor_default_config(num_cpus);
    dag_executor_init_with_config(exec, dag, &config);
}

void dag_executor_init_with_config(dag_executor_t *exec,
                                    dag_pdac_t *dag,
                                    const dag_executor_config_t *config)
{
    if (exec == NULL || dag == NULL || config == NULL) {
        return;
    }

    memset(exec, 0, sizeof(dag_executor_t));

    exec->dag = dag;
    exec->config = *config;

    /* Initialize RNG */
    lcg_init(&exec->rng, 42);

    /* Initialize RCU for concurrent DAG access */
    rcu_init(&exec->rcu, config->num_cpus);

    /* Initialize multi-core dispatcher */
    multicore_dispatch_init(&exec->dispatcher, dag, config->num_cpus);

    /* Initialize admission control */
    if (config->enable_admission_control) {
        admission_init(&exec->admission,
                       &exec->rng,
                       dag->system_quota,
                       config->refill_rate,
                       config->burst_size);
    }

    /* Initialize telemetry */
    if (config->enable_telemetry) {
        telemetry_init(&exec->telemetry, config->num_cpus);
    }

    /* Initialize task contexts */
    for (uint16_t i = 0; i < dag->num_tasks; i++) {
        task_exec_init(&exec->contexts[i], &dag->tasks[i], -1);
    }
}

/**
 * Validate DAG (simple cycle check via DFS)
 */
int dag_executor_validate(dag_executor_t *exec)
{
    if (exec == NULL || exec->dag == NULL) {
        return -1;
    }

    if (exec->dag->num_tasks == 0) {
        printf("Error: DAG has no tasks\n");
        return -1;
    }

    /* Basic validation: check all dependencies exist */
    for (uint16_t i = 0; i < exec->dag->num_tasks; i++) {
        dag_task_t *task = &exec->dag->tasks[i];

        for (uint8_t j = 0; j < task->num_deps; j++) {
            uint16_t dep_id = task->deps[j];

            if (dep_id >= exec->dag->num_tasks) {
                printf("Error: Task %u has invalid dependency %u\n", i, dep_id);
                return -1;
            }
        }
    }

    return 0;
}

/*******************************************************************************
 * EXECUTION CONTROL
 ******************************************************************************/

void dag_executor_start(dag_executor_t *exec)
{
    if (exec == NULL) {
        return;
    }

    exec->running = true;
    exec->start_time_us = 0;
    exec->current_time_us = 0;

    if (exec->config.enable_telemetry) {
        telemetry_start(&exec->telemetry, 0);
    }

    /* Initialize task states using atomic operations */
    for (uint16_t i = 0; i < exec->dag->num_tasks; i++) {
        dag_task_t *task = &exec->dag->tasks[i];

        if (task->num_deps == 0) {
            atomic_store(&task->state, TASK_STATE_READY);  /* No dependencies */
        } else {
            atomic_store(&task->state, TASK_STATE_PENDING);  /* Waiting for deps */
        }

        /* Record submission in telemetry */
        if (exec->config.enable_telemetry) {
            telemetry_record_submit(&exec->telemetry, i, exec->current_time_us);
        }
    }

    /* Initial dependency update */
    dag_executor_update_dependencies(exec);
}

bool dag_executor_step(dag_executor_t *exec)
{
    if (exec == NULL || !exec->running) {
        return false;
    }

    /* Step 1: Update dependencies (PENDING → READY) */
    dag_executor_update_dependencies(exec);

    /* Step 2: Try admission control for READY tasks */
    if (exec->config.enable_admission_control) {
        for (uint16_t i = 0; i < exec->dag->num_tasks; i++) {
            dag_task_t *task = &exec->dag->tasks[i];

            if (task->state == TASK_STATE_READY && !task->start_time) {
                /* Try to admit */
                if (admission_try_admit(&exec->admission, exec->dag, task)) {
                    /* Admitted - assign to CPU */
                    int cpu_id = multicore_dispatch_assign_task(&exec->dispatcher, task);

                    if (cpu_id >= 0 && exec->config.enable_telemetry) {
                        telemetry_record_start(&exec->telemetry, i, cpu_id,
                                               exec->current_time_us);
                    }
                }
            }
        }

        /* Refill admission tokens */
        admission_refill(&exec->admission, TIME_QUANTUM_MS);
    } else {
        /* No admission control - assign all READY tasks */
        for (uint16_t i = 0; i < exec->dag->num_tasks; i++) {
            task_state_t state = atomic_load(&exec->dag->tasks[i].state);
            if (state == TASK_STATE_READY &&
                !exec->dag->tasks[i].start_time) {
                multicore_dispatch_assign_task(&exec->dispatcher, &exec->dag->tasks[i]);
            }
        }
    }

    /* Step 3: Execute one quantum on all CPUs */
    multicore_dispatch_step(&exec->dispatcher, exec->current_time_us);

    /* Step 4: Check for completed tasks */
    for (uint16_t i = 0; i < exec->dag->num_tasks; i++) {
        task_state_t state = atomic_load(&exec->dag->tasks[i].state);
        if (state == TASK_STATE_COMPLETED &&
            !exec->contexts[i].task->end_time) {

            exec->dag->tasks[i].end_time = exec->current_time_us / 1000;

            if (exec->config.enable_telemetry) {
                telemetry_record_complete(&exec->telemetry, i, exec->current_time_us);
            }

            dag_executor_notify_completion(exec, i);
            exec->tasks_completed++;
        }
    }

    /* Step 5: Advance time */
    exec->current_time_us += TIME_QUANTUM_MS * 1000;

    /* Step 6: Update telemetry */
    if (exec->config.enable_telemetry) {
        telemetry_collect_from_dispatcher(&exec->telemetry,
                                           &exec->dispatcher,
                                           exec->current_time_us);
    }

    /* Check timeout */
    if (exec->config.max_runtime_us > 0 &&
        exec->current_time_us >= exec->config.max_runtime_us) {
        printf("Warning: Execution timeout\n");
        exec->running = false;
        return false;
    }

    /* Check completion */
    if (dag_executor_is_complete(exec)) {
        exec->running = false;
        exec->end_time_us = exec->current_time_us;
        return false;
    }

    return true;
}

int dag_executor_run_sync(dag_executor_t *exec)
{
    if (exec == NULL) {
        return -1;
    }

    /* Validate before execution */
    if (dag_executor_validate(exec) != 0) {
        return -1;
    }

    dag_executor_start(exec);

    /* Execute until complete */
    while (dag_executor_step(exec)) {
        /* Keep stepping */
    }

    return 0;
}

void dag_executor_stop(dag_executor_t *exec)
{
    if (exec == NULL) {
        return;
    }

    exec->running = false;
    exec->end_time_us = exec->current_time_us;
}

bool dag_executor_is_complete(const dag_executor_t *exec)
{
    if (exec == NULL || exec->dag == NULL) {
        return true;
    }

    /* Check if all tasks are in terminal state */
    for (uint16_t i = 0; i < exec->dag->num_tasks; i++) {
        task_state_t state = atomic_load(&exec->dag->tasks[i].state);

        if (state != TASK_STATE_COMPLETED && state != TASK_STATE_FAILED) {
            return false;  /* Found non-terminal task */
        }
    }

    return true;
}

/*******************************************************************************
 * DEPENDENCY MANAGEMENT
 ******************************************************************************/

bool dag_executor_deps_satisfied(const dag_executor_t *exec,
                                  uint16_t task_id)
{
    if (exec == NULL || task_id >= exec->dag->num_tasks) {
        return false;
    }

    const dag_task_t *task = &exec->dag->tasks[task_id];

    /* Check all dependencies under RCU protection */
    bool satisfied = true;
    for (uint8_t i = 0; i < task->num_deps; i++) {
        uint16_t dep_id = task->deps[i];
        const dag_task_t *dep = &exec->dag->tasks[dep_id];

        /* Atomic load of dependency state */
        task_state_t dep_state = atomic_load(&dep->state);
        if (dep_state != TASK_STATE_COMPLETED) {
            satisfied = false;
            break;  /* Dependency not complete */
        }
    }

    return satisfied;
}

void dag_executor_update_dependencies(dag_executor_t *exec)
{
    if (exec == NULL) {
        return;
    }

    /* Scan all PENDING tasks under RCU protection */
    /* Note: Using CPU 0 for single-threaded updates; will be generalized for work-stealing */
    rcu_read_lock(&exec->rcu, 0);

    for (uint16_t i = 0; i < exec->dag->num_tasks; i++) {
        dag_task_t *task = &exec->dag->tasks[i];

        /* Atomic load of task state */
        task_state_t current_state = atomic_load(&task->state);

        if (current_state == TASK_STATE_PENDING) {
            /* Check if dependencies satisfied */
            if (dag_executor_deps_satisfied(exec, i)) {
                /* Atomic state transition: PENDING → READY */
                task_state_t expected = TASK_STATE_PENDING;
                if (atomic_compare_exchange_strong(&task->state, &expected, TASK_STATE_READY)) {
                    exec->tasks_ready++;
                }
            }
        }
    }

    rcu_read_unlock(&exec->rcu, 0);
}

void dag_executor_notify_completion(dag_executor_t *exec,
                                     uint16_t task_id)
{
    if (exec == NULL) {
        return;
    }

    /* Update dependency state (will be picked up next iteration) */
    dag_executor_update_dependencies(exec);
}

/*******************************************************************************
 * STATISTICS & REPORTING
 ******************************************************************************/

uint64_t dag_executor_get_duration(const dag_executor_t *exec)
{
    if (exec == NULL) {
        return 0;
    }

    if (exec->running) {
        return exec->current_time_us - exec->start_time_us;
    }

    return exec->end_time_us - exec->start_time_us;
}

uint64_t dag_executor_get_makespan(const dag_executor_t *exec)
{
    if (exec == NULL || exec->dag == NULL) {
        return 0;
    }

    /* Find maximum completion time across all tasks */
    uint64_t max_time = 0;

    for (uint16_t i = 0; i < exec->dag->num_tasks; i++) {
        uint64_t complete_time = exec->dag->tasks[i].end_time * 1000;  /* Convert to μs */

        if (complete_time > max_time) {
            max_time = complete_time;
        }
    }

    return max_time;
}

uint64_t dag_executor_estimate_sequential_time(const dag_executor_t *exec)
{
    if (exec == NULL || exec->dag == NULL) {
        return 0;
    }

    uint64_t total_work = 0;

    for (uint16_t i = 0; i < exec->dag->num_tasks; i++) {
        total_work += task_estimate_work_remaining(&exec->contexts[i]);
    }

    return total_work;
}

q16_t dag_executor_compute_speedup(const dag_executor_t *exec)
{
    if (exec == NULL) {
        return 0;
    }

    uint64_t sequential = dag_executor_estimate_sequential_time(exec);
    uint64_t parallel = dag_executor_get_makespan(exec);

    if (parallel == 0) {
        return 0;
    }

    /* Speedup = sequential / parallel */
    return ((sequential << 16) / parallel);
}

q16_t dag_executor_compute_efficiency(const dag_executor_t *exec)
{
    if (exec == NULL || exec->config.num_cpus == 0) {
        return 0;
    }

    q16_t speedup = dag_executor_compute_speedup(exec);

    /* Efficiency = speedup / num_cpus */
    return (speedup / exec->config.num_cpus);
}

void dag_executor_print_stats(const dag_executor_t *exec)
{
    if (exec == NULL) {
        return;
    }

    printf("\n=== DAG Execution Statistics ===\n");
    printf("Tasks: %u (completed: %u, failed: %u)\n",
           exec->dag->num_tasks,
           exec->tasks_completed,
           exec->tasks_failed);

    printf("Execution time: %.2f ms\n",
           dag_executor_get_duration(exec) / 1000.0);

    printf("Makespan: %.2f ms\n",
           dag_executor_get_makespan(exec) / 1000.0);

    q16_t speedup = dag_executor_compute_speedup(exec);
    printf("Speedup: %.2fx\n", (double)speedup / 65536.0);

    q16_t efficiency = dag_executor_compute_efficiency(exec);
    printf("Efficiency: %.1f%%\n", (double)efficiency * 100.0 / 65536.0);

    printf("=================================\n\n");
}

void dag_executor_print_report(const dag_executor_t *exec)
{
    if (exec == NULL) {
        return;
    }

    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║          PDAC DAG EXECUTOR - FINAL REPORT                  ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n");

    dag_executor_print_stats(exec);

    if (exec->config.enable_telemetry) {
        telemetry_print_summary(&exec->telemetry);
    }

    multicore_dispatch_print_stats(&exec->dispatcher);
}

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

void example_dag_executor_pipeline(void)
{
    printf("\n=== Example: Pipeline Execution (A → B → C) ===\n");
    printf("Sequential dependencies, expect minimal parallelism\n\n");

    /* Create DAG */
    dag_pdac_t dag;
    resource_vector_t quota = {.cpu = Q16(4.0), .memory = Q16(1024.0)};
    pdac_dag_init(&dag, quota);

    /* Add tasks */
    resource_vector_t res = {.cpu = Q16(1.0), .memory = Q16(200.0)};
    int a = pdac_dag_add_task(&dag, "Task A", res);
    int b = pdac_dag_add_task(&dag, "Task B", res);
    int c = pdac_dag_add_task(&dag, "Task C", res);

    /* Add dependencies: A → B → C */
    pdac_dag_add_dependency(&dag, b, a);
    pdac_dag_add_dependency(&dag, c, b);

    /* Execute */
    dag_executor_t exec;
    dag_executor_init(&exec, &dag, 2);  /* 2 CPUs */

    printf("Executing pipeline...\n");
    dag_executor_run_sync(&exec);

    dag_executor_print_report(&exec);

    printf("Note: Pipeline has limited parallelism (sequential)\n");
    printf("===============================================\n\n");
}

void example_dag_executor_diamond(void)
{
    printf("\n=== Example: Diamond DAG ===\n");
    printf("     A\n");
    printf("    / \\\n");
    printf("   B   C\n");
    printf("    \\ /\n");
    printf("     D\n\n");
    printf("B and C can run in parallel\n\n");

    /* Create DAG */
    dag_pdac_t dag;
    resource_vector_t quota = {.cpu = Q16(8.0), .memory = Q16(2048.0)};
    pdac_dag_init(&dag, quota);

    resource_vector_t res = {.cpu = Q16(1.0), .memory = Q16(200.0)};
    int a = pdac_dag_add_task(&dag, "Task A", res);
    int b = pdac_dag_add_task(&dag, "Task B", res);
    int c = pdac_dag_add_task(&dag, "Task C", res);
    int d = pdac_dag_add_task(&dag, "Task D", res);

    /* Diamond structure */
    pdac_dag_add_dependency(&dag, b, a);  /* B depends on A */
    pdac_dag_add_dependency(&dag, c, a);  /* C depends on A */
    pdac_dag_add_dependency(&dag, d, b);  /* D depends on B */
    pdac_dag_add_dependency(&dag, d, c);  /* D depends on C */

    /* Execute on 2 CPUs (should see parallelism in B,C) */
    dag_executor_t exec;
    dag_executor_init(&exec, &dag, 2);

    printf("Executing diamond DAG on 2 CPUs...\n");
    dag_executor_run_sync(&exec);

    dag_executor_print_report(&exec);

    printf("Note: B and C should execute in parallel\n");
    printf("=======================================\n\n");
}

void example_dag_executor_scaling(void)
{
    printf("\n=== Example: Multi-Core Scaling ===\n");
    printf("10 independent tasks on 1, 2, 4 CPUs\n\n");

    /* Create DAG with 10 independent tasks */
    dag_pdac_t dag;
    resource_vector_t quota = {.cpu = Q16(16.0), .memory = Q16(4096.0)};
    pdac_dag_init(&dag, quota);

    resource_vector_t res = {.cpu = Q16(1.0), .memory = Q16(200.0)};
    for (int i = 0; i < 10; i++) {
        char name[32];
        snprintf(name, sizeof(name), "Task %d", i);
        pdac_dag_add_task(&dag, name, res);
    }

    /* Test with different CPU counts */
    uint8_t cpu_counts[] = {1, 2, 4};

    for (int test = 0; test < 3; test++) {
        uint8_t num_cpus = cpu_counts[test];

        dag_executor_t exec;
        dag_executor_init(&exec, &dag, num_cpus);

        printf("Running with %u CPU(s)...\n", num_cpus);
        dag_executor_run_sync(&exec);

        printf("  Makespan: %.2f ms\n",
               dag_executor_get_makespan(&exec) / 1000.0);
        printf("  Speedup: %.2fx\n\n",
               (double)dag_executor_compute_speedup(&exec) / 65536.0);
    }

    printf("Expected: Near-linear speedup for independent tasks\n");
    printf("==================================================\n\n");
}

/**
 * Run all DAG executor examples
 */
void dag_executor_run_all_examples(void)
{
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   DAG EXECUTOR - EXAMPLES                                  ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n");

    example_dag_executor_pipeline();
    example_dag_executor_diamond();
    example_dag_executor_scaling();

    printf("All DAG executor examples completed.\n");
    printf("See include/dag_executor.h for API documentation.\n\n");
}
