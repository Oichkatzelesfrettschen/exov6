/**
 * @file percpu_sched.c
 * @brief Per-CPU Run Queues and Multi-Core Dispatcher Implementation
 *
 * @see include/percpu_sched.h for API documentation
 */

#include "percpu_sched.h"
#include "printf.h"
#include <stdint.h>
#include <string.h>

/*******************************************************************************
 * PER-CPU SCHEDULER IMPLEMENTATION
 ******************************************************************************/

/**
 * Initialize per-CPU scheduler
 */
void percpu_sched_init(percpu_scheduler_t *cpu, uint8_t cpu_id, uint32_t seed)
{
    if (cpu == NULL || cpu_id >= MAX_CPUS) {
        return;
    }

    memset(cpu, 0, sizeof(percpu_scheduler_t));

    cpu->cpu_id = cpu_id;

    /* Initialize per-CPU RNG */
    lcg_init(&cpu->rng, seed);

    /* Initialize hybrid scheduler */
    hybrid_init(&cpu->sched, &cpu->rng);
}

/**
 * Add task to ready queue
 */
int percpu_sched_add_task(percpu_scheduler_t *cpu, dag_task_t *task)
{
    if (cpu == NULL || task == NULL) {
        return -1;
    }

    if (cpu->num_ready >= PERCPU_MAX_READY_TASKS) {
        return -1; /* Queue full */
    }

    cpu->ready_queue[cpu->num_ready] = task;
    cpu->num_ready++;

    /* Update scheduler metadata */
    hybrid_update_task(&cpu->sched, task->id, task);

    return 0;
}

/**
 * Remove task from ready queue
 */
int percpu_sched_remove_task(percpu_scheduler_t *cpu, dag_task_t *task)
{
    if (cpu == NULL || task == NULL) {
        return -1;
    }

    /* Find task in queue */
    for (uint16_t i = 0; i < cpu->num_ready; i++) {
        if (cpu->ready_queue[i] == task) {
            /* Shift remaining tasks */
            for (uint16_t j = i; j < cpu->num_ready - 1; j++) {
                cpu->ready_queue[j] = cpu->ready_queue[j + 1];
            }
            cpu->num_ready--;
            return 0;
        }
    }

    return -1; /* Not found */
}

/**
 * Select next task to run
 */
dag_task_t *percpu_sched_select_next(percpu_scheduler_t *cpu)
{
    if (cpu == NULL || cpu->num_ready == 0) {
        return NULL;
    }

    /* Create temporary DAG with only this CPU's ready tasks */
    dag_pdac_t local_dag;
    memset(&local_dag, 0, sizeof(local_dag));

    for (uint16_t i = 0; i < cpu->num_ready; i++) {
        local_dag.tasks[i] = *cpu->ready_queue[i];
    }
    local_dag.num_tasks = cpu->num_ready;

    /* Use hybrid scheduler to select */
    dag_task_t *selected = hybrid_select(&cpu->sched, &local_dag);

    return selected;
}

/**
 * Execute current task for one quantum
 */
bool percpu_sched_run_current(percpu_scheduler_t *cpu, uint64_t now_us)
{
    if (cpu == NULL || cpu->current_task == NULL || cpu->current_context == NULL) {
        /* CPU idle */
        if (cpu->last_activity_us > 0) {
            cpu->total_idle_time_us += (now_us - cpu->last_activity_us);
        }
        cpu->last_activity_us = now_us;
        return false;
    }

    /* Execute task for quantum */
    uint64_t quantum_us = TIME_QUANTUM_MS * 1000;
    bool completed = task_exec_run(cpu->current_context, quantum_us);

    /* Update busy time */
    cpu->total_busy_time_us += quantum_us;
    cpu->last_activity_us = now_us + quantum_us;

    if (completed) {
        /* Task finished */
        task_exec_complete(cpu->current_context, now_us + quantum_us);
        cpu->current_task = NULL;
        cpu->current_context = NULL;
        cpu->total_tasks_run++;
        return true;
    }

    /* Check if should preempt */
    if (task_should_preempt(cpu->current_context)) {
        task_exec_preempt(cpu->current_context, now_us + quantum_us);

        /* Put task back in ready queue */
        percpu_sched_add_task(cpu, cpu->current_task);

        cpu->current_task = NULL;
        cpu->current_context = NULL;
    }

    return false;
}

/**
 * Compute CPU load
 */
q16_t percpu_sched_compute_load(const percpu_scheduler_t *cpu)
{
    if (cpu == NULL) {
        return 0;
    }

    /* Load = num_ready + (current_task ? 1 : 0) */
    uint32_t load = cpu->num_ready;
    if (cpu->current_task != NULL) {
        load++;
    }

    return Q16((double)load);
}

/**
 * Get CPU utilization
 */
q16_t percpu_sched_get_utilization(const percpu_scheduler_t *cpu)
{
    if (cpu == NULL) {
        return 0;
    }

    uint64_t total_time = cpu->total_busy_time_us + cpu->total_idle_time_us;
    if (total_time == 0) {
        return 0;
    }

    /* Utilization = busy_time / total_time */
    return ((cpu->total_busy_time_us << 16) / total_time);
}

/*******************************************************************************
 * MULTI-CORE DISPATCHER IMPLEMENTATION
 ******************************************************************************/

/**
 * Initialize multi-core dispatcher
 */
void multicore_dispatch_init(multicore_dispatcher_t *dispatch,
                              dag_pdac_t *dag,
                              uint8_t num_cpus)
{
    if (dispatch == NULL || dag == NULL || num_cpus == 0 || num_cpus > MAX_CPUS) {
        return;
    }

    memset(dispatch, 0, sizeof(multicore_dispatcher_t));

    dispatch->dag = dag;
    dispatch->num_cpus = num_cpus;
    dispatch->balance_interval_us = LOAD_BALANCE_INTERVAL_MS * 1000;

    /* Initialize per-CPU schedulers */
    for (uint8_t i = 0; i < num_cpus; i++) {
        /* Use different seed per CPU for RNG independence */
        uint32_t seed = 42 + (i * 1000);
        percpu_sched_init(&dispatch->cpus[i], i, seed);
    }
}

/**
 * Assign task to CPU with lowest load
 */
int multicore_dispatch_assign_task(multicore_dispatcher_t *dispatch,
                                   dag_task_t *task)
{
    if (dispatch == NULL || task == NULL) {
        return -1;
    }

    /* Find CPU with lowest load */
    uint8_t min_cpu = 0;
    q16_t min_load = percpu_sched_compute_load(&dispatch->cpus[0]);

    for (uint8_t i = 1; i < dispatch->num_cpus; i++) {
        q16_t load = percpu_sched_compute_load(&dispatch->cpus[i]);
        if (load < min_load) {
            min_load = load;
            min_cpu = i;
        }
    }

    /* Add task to selected CPU */
    int ret = percpu_sched_add_task(&dispatch->cpus[min_cpu], task);
    if (ret == 0) {
        return min_cpu;
    }

    return -1;
}

/**
 * Perform load balancing
 */
void multicore_dispatch_balance(multicore_dispatcher_t *dispatch,
                                uint64_t now_us)
{
    if (dispatch == NULL) {
        return;
    }

    /* Check if enough time has passed */
    if (now_us - dispatch->last_balance_time_us < dispatch->balance_interval_us) {
        return;
    }

    dispatch->last_balance_time_us = now_us;

    /* Find most and least loaded CPUs */
    uint8_t max_cpu = 0, min_cpu = 0;
    q16_t max_load = percpu_sched_compute_load(&dispatch->cpus[0]);
    q16_t min_load = max_load;

    for (uint8_t i = 1; i < dispatch->num_cpus; i++) {
        q16_t load = percpu_sched_compute_load(&dispatch->cpus[i]);

        if (load > max_load) {
            max_load = load;
            max_cpu = i;
        }

        if (load < min_load) {
            min_load = load;
            min_cpu = i;
        }
    }

    /* Check if imbalance is significant */
    q16_t imbalance = max_load - min_load;
    if (imbalance < LOAD_IMBALANCE_THRESHOLD) {
        return; /* Load is balanced enough */
    }

    /* Migrate one task from max_cpu to min_cpu */
    if (dispatch->cpus[max_cpu].num_ready > 0) {
        dag_task_t *task = dispatch->cpus[max_cpu].ready_queue[0];
        multicore_dispatch_migrate_task(dispatch, task, max_cpu, min_cpu);
    }
}

/**
 * Migrate task between CPUs
 */
int multicore_dispatch_migrate_task(multicore_dispatcher_t *dispatch,
                                    dag_task_t *task,
                                    uint8_t from_cpu,
                                    uint8_t to_cpu)
{
    if (dispatch == NULL || task == NULL ||
        from_cpu >= dispatch->num_cpus ||
        to_cpu >= dispatch->num_cpus) {
        return -1;
    }

    /* Remove from source CPU */
    int ret = percpu_sched_remove_task(&dispatch->cpus[from_cpu], task);
    if (ret != 0) {
        return -1;
    }

    /* Add to destination CPU */
    ret = percpu_sched_add_task(&dispatch->cpus[to_cpu], task);
    if (ret != 0) {
        /* Failed - try to restore to source */
        percpu_sched_add_task(&dispatch->cpus[from_cpu], task);
        return -1;
    }

    dispatch->total_migrations++;
    return 0;
}

/**
 * Execute one step on all CPUs
 */
void multicore_dispatch_step(multicore_dispatcher_t *dispatch,
                             uint64_t now_us)
{
    if (dispatch == NULL) {
        return;
    }

    /* Process each CPU */
    for (uint8_t i = 0; i < dispatch->num_cpus; i++) {
        percpu_scheduler_t *cpu = &dispatch->cpus[i];

        /* If CPU idle, select next task */
        if (cpu->current_task == NULL && cpu->num_ready > 0) {
            dag_task_t *next = percpu_sched_select_next(cpu);
            if (next != NULL) {
                /* Remove from ready queue */
                percpu_sched_remove_task(cpu, next);

                /* Start execution */
                task_context_t *ctx = malloc(sizeof(task_context_t));
                task_exec_init(ctx, next, -1);
                task_exec_start(ctx, now_us);

                cpu->current_task = next;
                cpu->current_context = ctx;
            }
        }

        /* Execute current task */
        bool completed = percpu_sched_run_current(cpu, now_us);
        if (completed) {
            dispatch->total_tasks_completed++;

            /* Free context */
            if (cpu->current_context != NULL) {
                free(cpu->current_context);
                cpu->current_context = NULL;
            }
        }
    }

    /* Periodic load balancing */
    multicore_dispatch_balance(dispatch, now_us);
}

/**
 * Check if all CPUs idle
 */
bool multicore_dispatch_all_idle(const multicore_dispatcher_t *dispatch)
{
    if (dispatch == NULL) {
        return true;
    }

    for (uint8_t i = 0; i < dispatch->num_cpus; i++) {
        if (dispatch->cpus[i].current_task != NULL ||
            dispatch->cpus[i].num_ready > 0) {
            return false;
        }
    }

    return true;
}

/*******************************************************************************
 * STATISTICS & INTROSPECTION
 ******************************************************************************/

uint64_t multicore_dispatch_get_migrations(const multicore_dispatcher_t *dispatch)
{
    return dispatch ? dispatch->total_migrations : 0;
}

q16_t multicore_dispatch_get_avg_load(const multicore_dispatcher_t *dispatch)
{
    if (dispatch == NULL || dispatch->num_cpus == 0) {
        return 0;
    }

    uint64_t total_load = 0;
    for (uint8_t i = 0; i < dispatch->num_cpus; i++) {
        total_load += percpu_sched_compute_load(&dispatch->cpus[i]);
    }

    return (q16_t)(total_load / dispatch->num_cpus);
}

q16_t multicore_dispatch_get_load_imbalance(const multicore_dispatcher_t *dispatch)
{
    if (dispatch == NULL || dispatch->num_cpus == 0) {
        return 0;
    }

    q16_t max_load = 0, min_load = Q16(1000.0);

    for (uint8_t i = 0; i < dispatch->num_cpus; i++) {
        q16_t load = percpu_sched_compute_load(&dispatch->cpus[i]);
        if (load > max_load) max_load = load;
        if (load < min_load) min_load = load;
    }

    return max_load - min_load;
}

void multicore_dispatch_print_stats(const multicore_dispatcher_t *dispatch)
{
    if (dispatch == NULL) {
        return;
    }

    printf("\n=== Multi-Core Dispatcher Statistics ===\n");
    printf("Number of CPUs: %u\n", dispatch->num_cpus);
    printf("Total tasks completed: %llu\n", dispatch->total_tasks_completed);
    printf("Total migrations: %llu\n", dispatch->total_migrations);
    printf("Average load: %.2f\n",
           (double)multicore_dispatch_get_avg_load(dispatch) / 65536.0);
    printf("Load imbalance: %.2f\n\n",
           (double)multicore_dispatch_get_load_imbalance(dispatch) / 65536.0);

    printf("%-6s %-8s %-12s %-12s %-12s\n",
           "CPU", "Load", "Tasks Run", "Utilization", "Status");
    printf("------------------------------------------------------------\n");

    for (uint8_t i = 0; i < dispatch->num_cpus; i++) {
        percpu_scheduler_t *cpu = &dispatch->cpus[i];
        q16_t load = percpu_sched_compute_load(cpu);
        q16_t util = percpu_sched_get_utilization(cpu);

        const char *status = cpu->current_task ? "BUSY" : "IDLE";

        printf("%-6u %-8.1f %-12llu %-12.1f%% %-12s\n",
               i,
               (double)load / 65536.0,
               cpu->total_tasks_run,
               (double)util * 100.0 / 65536.0,
               status);
    }

    printf("=========================================\n\n");
}

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Multi-core speedup
 */
void example_multicore_speedup(void)
{
    printf("\n=== Example: Multi-Core Speedup ===\n");
    printf("Compare 1 CPU vs. 4 CPUs for 16 independent tasks\n\n");

    /* Test with 1 CPU */
    dag_pdac_t dag1;
    resource_vector_t quota = {.cpu = Q16(16.0), .memory = Q16(4096.0)};
    pdac_dag_init(&dag1, quota);

    /* Add 16 tasks */
    resource_vector_t res = {.cpu = Q16(1.0), .memory = Q16(200.0)};
    for (int i = 0; i < 16; i++) {
        char name[32];
        snprintf(name, sizeof(name), "Task %d", i);
        int id = pdac_dag_add_task(&dag1, name, res);
        dag1.tasks[id].state = TASK_STATE_READY;
    }

    multicore_dispatcher_t dispatch1;
    multicore_dispatch_init(&dispatch1, &dag1, 1); /* 1 CPU */

    /* Assign all tasks */
    for (int i = 0; i < 16; i++) {
        multicore_dispatch_assign_task(&dispatch1, &dag1.tasks[i]);
    }

    /* Run until complete */
    uint64_t now1 = 0;
    uint64_t start1 = now1;
    while (!multicore_dispatch_all_idle(&dispatch1)) {
        multicore_dispatch_step(&dispatch1, now1);
        now1 += TIME_QUANTUM_MS * 1000;
    }
    uint64_t time1 = now1 - start1;

    printf("1 CPU: Completed in %llu ms\n", time1 / 1000);

    /* Test with 4 CPUs */
    dag_pdac_t dag4;
    pdac_dag_init(&dag4, quota);

    for (int i = 0; i < 16; i++) {
        char name[32];
        snprintf(name, sizeof(name), "Task %d", i);
        int id = pdac_dag_add_task(&dag4, name, res);
        dag4.tasks[id].state = TASK_STATE_READY;
    }

    multicore_dispatcher_t dispatch4;
    multicore_dispatch_init(&dispatch4, &dag4, 4); /* 4 CPUs */

    for (int i = 0; i < 16; i++) {
        multicore_dispatch_assign_task(&dispatch4, &dag4.tasks[i]);
    }

    uint64_t now4 = 0;
    uint64_t start4 = now4;
    while (!multicore_dispatch_all_idle(&dispatch4)) {
        multicore_dispatch_step(&dispatch4, now4);
        now4 += TIME_QUANTUM_MS * 1000;
    }
    uint64_t time4 = now4 - start4;

    printf("4 CPUs: Completed in %llu ms\n", time4 / 1000);
    printf("Speedup: %.2fx\n\n", (double)time1 / time4);

    multicore_dispatch_print_stats(&dispatch4);
    printf("===================================\n\n");
}

/**
 * Example: Load balancing
 */
void example_load_balancing(void)
{
    printf("\n=== Example: Load Balancing ===\n");
    printf("Initially unbalanced, should converge\n\n");

    dag_pdac_t dag;
    resource_vector_t quota = {.cpu = Q16(8.0), .memory = Q16(2048.0)};
    pdac_dag_init(&dag, quota);

    /* Add 10 tasks */
    resource_vector_t res = {.cpu = Q16(1.0), .memory = Q16(200.0)};
    for (int i = 0; i < 10; i++) {
        char name[32];
        snprintf(name, sizeof(name), "Task %d", i);
        int id = pdac_dag_add_task(&dag, name, res);
        dag.tasks[id].state = TASK_STATE_READY;
    }

    multicore_dispatcher_t dispatch;
    multicore_dispatch_init(&dispatch, &dag, 4);

    /* Manually create imbalance - assign all to CPU 0 */
    for (int i = 0; i < 10; i++) {
        percpu_sched_add_task(&dispatch.cpus[0], &dag.tasks[i]);
    }

    printf("Initial state:\n");
    printf("  CPU 0: %u tasks\n", dispatch.cpus[0].num_ready);
    printf("  CPU 1: %u tasks\n", dispatch.cpus[1].num_ready);
    printf("  CPU 2: %u tasks\n", dispatch.cpus[2].num_ready);
    printf("  CPU 3: %u tasks\n\n", dispatch.cpus[3].num_ready);

    /* Run load balancing */
    uint64_t now = 0;
    for (int i = 0; i < 5; i++) {
        multicore_dispatch_balance(&dispatch, now);
        now += LOAD_BALANCE_INTERVAL_MS * 1000;
    }

    printf("After load balancing:\n");
    printf("  CPU 0: %u tasks\n", dispatch.cpus[0].num_ready);
    printf("  CPU 1: %u tasks\n", dispatch.cpus[1].num_ready);
    printf("  CPU 2: %u tasks\n", dispatch.cpus[2].num_ready);
    printf("  CPU 3: %u tasks\n", dispatch.cpus[3].num_ready);
    printf("  Migrations: %llu\n\n", dispatch.total_migrations);

    printf("==============================\n\n");
}

/**
 * Run all per-CPU scheduler examples
 */
void percpu_sched_run_all_examples(void)
{
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   PER-CPU SCHEDULER - EXAMPLES                             ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n");

    example_multicore_speedup();
    example_load_balancing();

    printf("All per-CPU scheduler examples completed.\n");
    printf("See include/percpu_sched.h for API documentation.\n\n");
}
