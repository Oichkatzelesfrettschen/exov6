/**
 * @file scheduler_lockfree.c
 * @brief Lock-Free RCU Scheduler Implementation (Task 5.5.2)
 *
 * High-performance lock-free scheduler with per-CPU queues and RCU.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "scheduler_lockfree.h"

/*******************************************************************************
 * INTERNAL HELPERS
 ******************************************************************************/

/**
 * @brief Get current time in nanoseconds
 */
uint64_t scheduler_get_time_ns(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

/**
 * @brief Allocate task structure
 */
static task_t *task_alloc(task_id_t id, q16_t priority,
                         void (*task_func)(void *), void *task_arg)
{
    task_t *task = calloc(1, sizeof(task_t));
    if (!task) return NULL;

    task->id = id;
    atomic_store(&task->state, TASK_STATE_NEW);
    atomic_store(&task->current_cpu, 0xFF);  /* Invalid CPU */
    atomic_store(&task->runtime_ns, 0);
    atomic_store(&task->context_switches, 0);
    task->priority = priority;
    task->quantum_ns = SCHEDULER_QUANTUM_US * 1000;
    task->deadline_ns = 0;
    task->preferred_cpu = 0;
    task->cpu_mask = 0xFFFFFFFFFFFFFFFFULL;  /* All CPUs allowed */
    task->memory_allocated = 0;
    task->io_operations = 0;
    task->create_time_ns = scheduler_get_time_ns();
    task->start_time_ns = 0;
    task->task_func = task_func;
    task->task_arg = task_arg;

    return task;
}

/**
 * @brief Free task structure (RCU callback)
 */
static void task_free_rcu(rcu_head_t *head, uint8_t cpu_id)
{
    (void)cpu_id;
    task_t *task = container_of(head, task_t, rcu_head);
    free(task);
}

/*******************************************************************************
 * SCHEDULER MANAGEMENT
 ******************************************************************************/

int scheduler_lockfree_init(scheduler_lockfree_t *sched, uint8_t num_cpus)
{
    if (!sched || num_cpus == 0 || num_cpus > MAX_CPUS) return -1;

    memset(sched, 0, sizeof(*sched));
    sched->num_cpus = num_cpus;

    /* Initialize per-CPU schedulers */
    for (uint8_t cpu = 0; cpu < num_cpus; cpu++) {
        cpu_scheduler_t *cpu_sched = &sched->cpus[cpu];

        /* Initialize lock-free ready queue */
        ms_queue_init(&cpu_sched->ready_queue);

        atomic_store(&cpu_sched->current_task, NULL);
        atomic_store(&cpu_sched->queue_length, 0);
        atomic_store(&cpu_sched->total_enqueues, 0);
        atomic_store(&cpu_sched->total_dequeues, 0);
        atomic_store(&cpu_sched->idle_time_ns, 0);
        atomic_store(&cpu_sched->stolen_from, 0);
        atomic_store(&cpu_sched->stolen_to, 0);
    }

    /* Initialize RCU */
    rcu_init(&sched->rcu, num_cpus);

    /* Initialize hazard pointer domain */
    hp_domain_init(&sched->hp, num_cpus);

    /* Initialize task table */
    for (uint32_t i = 0; i < MAX_TASKS; i++) {
        atomic_store(&sched->task_table[i], NULL);
    }

    /* Initialize global statistics */
    atomic_store(&sched->total_tasks, 0);
    atomic_store(&sched->active_tasks, 0);
    atomic_store(&sched->completed_tasks, 0);
    atomic_store(&sched->total_runtime_ns, 0);

    /* Configuration */
    sched->default_quantum_ns = SCHEDULER_QUANTUM_US * 1000;
    sched->enable_work_stealing = true;

    return 0;
}

void scheduler_lockfree_destroy(scheduler_lockfree_t *sched)
{
    if (!sched) return;

    /* Free all tasks */
    for (uint32_t i = 0; i < MAX_TASKS; i++) {
        task_t *task = atomic_load(&sched->task_table[i]);
        if (task) {
            free(task);
        }
    }

    /* Destroy per-CPU queues */
    for (uint8_t cpu = 0; cpu < sched->num_cpus; cpu++) {
        ms_queue_destroy(&sched->cpus[cpu].ready_queue);
    }

    /* Cleanup RCU and HP */
    rcu_destroy(&sched->rcu);
    hp_domain_destroy(&sched->hp);
}

/*******************************************************************************
 * TASK MANAGEMENT
 ******************************************************************************/

int scheduler_task_create(scheduler_lockfree_t *sched, task_id_t id,
                         q16_t priority, void (*task_func)(void *),
                         void *task_arg)
{
    if (!sched || id >= MAX_TASKS) return -1;

    /* Allocate task */
    task_t *task = task_alloc(id, priority, task_func, task_arg);
    if (!task) return -2;

    /* Insert into task table (atomic) */
    task_t *expected = NULL;
    if (!atomic_compare_exchange_strong(&sched->task_table[id],
                                       &expected, task)) {
        /* Duplicate ID */
        free(task);
        return -3;
    }

    atomic_fetch_add(&sched->total_tasks, 1);
    atomic_fetch_add(&sched->active_tasks, 1);

    return 0;
}

int scheduler_task_enqueue(scheduler_lockfree_t *sched, task_id_t id,
                          uint8_t cpu)
{
    if (!sched || id >= MAX_TASKS || cpu >= sched->num_cpus) return -1;

    /* Lookup task */
    task_t *task = scheduler_task_lookup(sched, id);
    if (!task) return -2;

    /* Atomic state transition: NEW/BLOCKED → READY */
    task_state_t expected = TASK_STATE_NEW;
    if (!atomic_compare_exchange_strong(&task->state, &expected,
                                       TASK_STATE_READY)) {
        /* Try BLOCKED → READY */
        expected = TASK_STATE_BLOCKED;
        if (!atomic_compare_exchange_strong(&task->state, &expected,
                                           TASK_STATE_READY)) {
            return -3;  /* Already in wrong state */
        }
    }

    /* Lock-free enqueue to CPU's ready queue */
    ms_enqueue(&sched->cpus[cpu].ready_queue, task, cpu);

    /* Update statistics */
    atomic_fetch_add(&sched->cpus[cpu].queue_length, 1);
    atomic_fetch_add(&sched->cpus[cpu].total_enqueues, 1);

    return 0;
}

task_t *scheduler_task_dequeue(scheduler_lockfree_t *sched, uint8_t cpu)
{
    if (!sched || cpu >= sched->num_cpus) return NULL;

    cpu_scheduler_t *cpu_sched = &sched->cpus[cpu];

    /* Try local queue first (lock-free dequeue) */
    task_t *task = ms_dequeue(&cpu_sched->ready_queue, cpu);

    if (task) {
        /* Verify and transition state: READY → RUNNING */
        task_state_t expected = TASK_STATE_READY;
        if (atomic_compare_exchange_strong(&task->state, &expected,
                                          TASK_STATE_RUNNING)) {
            /* Success */
            atomic_store(&task->current_cpu, cpu);
            atomic_store(&cpu_sched->current_task, task);
            task->start_time_ns = scheduler_get_time_ns();

            atomic_fetch_sub(&cpu_sched->queue_length, 1);
            atomic_fetch_add(&cpu_sched->total_dequeues, 1);
            atomic_fetch_add(&task->context_switches, 1);

            return task;
        }

        /* State changed (race condition), retry */
        return scheduler_task_dequeue(sched, cpu);
    }

    /* Local queue empty - try work stealing if enabled */
    if (sched->enable_work_stealing) {
        return scheduler_steal_task(sched, cpu);
    }

    return NULL;
}

int scheduler_task_complete(scheduler_lockfree_t *sched, task_t *task)
{
    if (!sched || !task) return -1;

    /* Atomic state transition: RUNNING → COMPLETED */
    task_state_t expected = TASK_STATE_RUNNING;
    if (!atomic_compare_exchange_strong(&task->state, &expected,
                                       TASK_STATE_COMPLETED)) {
        return -2;  /* Not in RUNNING state */
    }

    /* Update runtime */
    uint64_t now = scheduler_get_time_ns();
    uint64_t runtime = now - task->start_time_ns;
    atomic_fetch_add(&task->runtime_ns, runtime);
    atomic_fetch_add(&sched->total_runtime_ns, runtime);

    /* Update statistics */
    atomic_fetch_sub(&sched->active_tasks, 1);
    atomic_fetch_add(&sched->completed_tasks, 1);

    /* Clear current task on CPU */
    uint8_t cpu = atomic_load(&task->current_cpu);
    if (cpu < sched->num_cpus) {
        atomic_store(&sched->cpus[cpu].current_task, NULL);
    }

    /* Defer task deletion via RCU */
    call_rcu(&sched->rcu, &task->rcu_head, task_free_rcu, cpu);

    return 0;
}

int scheduler_task_block(scheduler_lockfree_t *sched, task_t *task)
{
    if (!sched || !task) return -1;

    /* Atomic state transition: RUNNING → BLOCKED */
    task_state_t expected = TASK_STATE_RUNNING;
    if (!atomic_compare_exchange_strong(&task->state, &expected,
                                       TASK_STATE_BLOCKED)) {
        return -2;
    }

    /* Update runtime */
    uint64_t now = scheduler_get_time_ns();
    uint64_t runtime = now - task->start_time_ns;
    atomic_fetch_add(&task->runtime_ns, runtime);

    return 0;
}

int scheduler_task_unblock(scheduler_lockfree_t *sched, task_id_t id,
                          uint8_t cpu)
{
    if (!sched || id >= MAX_TASKS || cpu >= sched->num_cpus) return -1;

    /* Re-enqueue task */
    return scheduler_task_enqueue(sched, id, cpu);
}

/*******************************************************************************
 * LOAD BALANCING
 ******************************************************************************/

task_t *scheduler_steal_task(scheduler_lockfree_t *sched, uint8_t cpu)
{
    if (!sched || cpu >= sched->num_cpus) return NULL;

    /* Find most loaded CPU (excluding self) */
    uint8_t victim_cpu = cpu;
    uint32_t max_load = 0;

    for (uint8_t i = 0; i < sched->num_cpus; i++) {
        if (i == cpu) continue;

        uint32_t load = atomic_load(&sched->cpus[i].queue_length);
        if (load > max_load) {
            max_load = load;
            victim_cpu = i;
        }
    }

    /* Nothing to steal */
    if (victim_cpu == cpu || max_load <= 1) {
        return NULL;
    }

    /* Attempt to steal from victim (lock-free) */
    task_t *task = ms_dequeue(&sched->cpus[victim_cpu].ready_queue, cpu);

    if (task) {
        /* Verify state and transition READY → RUNNING */
        task_state_t expected = TASK_STATE_READY;
        if (atomic_compare_exchange_strong(&task->state, &expected,
                                          TASK_STATE_RUNNING)) {
            /* Success */
            atomic_store(&task->current_cpu, cpu);
            atomic_store(&sched->cpus[cpu].current_task, task);
            task->start_time_ns = scheduler_get_time_ns();

            /* Update statistics */
            atomic_fetch_sub(&sched->cpus[victim_cpu].queue_length, 1);
            atomic_fetch_add(&sched->cpus[victim_cpu].stolen_from, 1);
            atomic_fetch_add(&sched->cpus[cpu].stolen_to, 1);
            atomic_fetch_add(&task->context_switches, 1);

            return task;
        }

        /* State changed, retry */
        return scheduler_steal_task(sched, cpu);
    }

    return NULL;
}

uint8_t scheduler_get_least_loaded_cpu(scheduler_lockfree_t *sched)
{
    if (!sched) return 0;

    uint8_t min_cpu = 0;
    uint32_t min_load = UINT32_MAX;

    for (uint8_t cpu = 0; cpu < sched->num_cpus; cpu++) {
        uint32_t load = atomic_load(&sched->cpus[cpu].queue_length);
        if (load < min_load) {
            min_load = load;
            min_cpu = cpu;
        }
    }

    return min_cpu;
}

void scheduler_balance_load(scheduler_lockfree_t *sched, uint8_t cpu)
{
    if (!sched || cpu >= sched->num_cpus) return;

    uint32_t local_load = atomic_load(&sched->cpus[cpu].queue_length);

    /* Only balance if we have excess load */
    if (local_load <= 2) return;

    /* Find least loaded CPU */
    uint8_t target_cpu = scheduler_get_least_loaded_cpu(sched);
    if (target_cpu == cpu) return;

    uint32_t target_load = atomic_load(&sched->cpus[target_cpu].queue_length);

    /* Balance threshold: migrate if difference > 2 */
    if (local_load - target_load <= 2) return;

    /* Migrate one task */
    rcu_read_lock(&sched->rcu, cpu);

    task_t *task = ms_dequeue(&sched->cpus[cpu].ready_queue, cpu);
    if (task) {
        /* Re-enqueue on target CPU */
        task_state_t state = atomic_load(&task->state);
        if (state == TASK_STATE_READY) {
            ms_enqueue(&sched->cpus[target_cpu].ready_queue, task, target_cpu);
            atomic_fetch_sub(&sched->cpus[cpu].queue_length, 1);
            atomic_fetch_add(&sched->cpus[target_cpu].queue_length, 1);
        }
    }

    rcu_read_unlock(&sched->rcu, cpu);
}

/*******************************************************************************
 * STATISTICS
 ******************************************************************************/

void scheduler_get_cpu_stats(const scheduler_lockfree_t *sched, uint8_t cpu,
                            cpu_stats_t *stats)
{
    if (!sched || cpu >= sched->num_cpus || !stats) return;

    const cpu_scheduler_t *cpu_sched = &sched->cpus[cpu];

    stats->queue_length = atomic_load(&cpu_sched->queue_length);
    stats->total_enqueues = atomic_load(&cpu_sched->total_enqueues);
    stats->total_dequeues = atomic_load(&cpu_sched->total_dequeues);
    stats->idle_time_ns = atomic_load(&cpu_sched->idle_time_ns);
    stats->stolen_from = atomic_load(&cpu_sched->stolen_from);
    stats->stolen_to = atomic_load(&cpu_sched->stolen_to);
    stats->current_task = atomic_load(&cpu_sched->current_task);
}

void scheduler_get_stats(const scheduler_lockfree_t *sched,
                        scheduler_stats_t *stats)
{
    if (!sched || !stats) return;

    stats->total_tasks = atomic_load(&sched->total_tasks);
    stats->active_tasks = atomic_load(&sched->active_tasks);
    stats->completed_tasks = atomic_load(&sched->completed_tasks);
    stats->total_runtime_ns = atomic_load(&sched->total_runtime_ns);
    stats->num_cpus = sched->num_cpus;
}

/*******************************************************************************
 * UTILITIES
 ******************************************************************************/

void scheduler_task_print(const task_t *task)
{
    if (!task) return;

    printf("Task ID: %u\n", task->id);
    printf("  State: %d\n", atomic_load(((_Atomic task_state_t *)&task->state)));
    printf("  Priority: %d\n", q16_to_int(task->priority));
    printf("  Current CPU: %u\n", atomic_load(((_Atomic uint8_t *)&task->current_cpu)));
    printf("  Runtime: %lu ns\n", atomic_load(((_Atomic uint64_t *)&task->runtime_ns)));
    printf("  Context Switches: %lu\n",
           atomic_load(((_Atomic uint64_t *)&task->context_switches)));
    printf("  Quantum: %lu ns\n", task->quantum_ns);
}

void scheduler_print_stats(const scheduler_lockfree_t *sched)
{
    if (!sched) return;

    scheduler_stats_t stats;
    scheduler_get_stats(sched, &stats);

    printf("\nScheduler Statistics:\n");
    printf("  Total Tasks: %lu\n", stats.total_tasks);
    printf("  Active Tasks: %lu\n", stats.active_tasks);
    printf("  Completed Tasks: %lu\n", stats.completed_tasks);
    printf("  Total Runtime: %lu ns\n", stats.total_runtime_ns);
    printf("  CPUs: %u\n", stats.num_cpus);

    printf("\nPer-CPU Statistics:\n");
    for (uint8_t cpu = 0; cpu < sched->num_cpus; cpu++) {
        cpu_stats_t cpu_stats;
        scheduler_get_cpu_stats(sched, cpu, &cpu_stats);

        printf("  CPU %u:\n", cpu);
        printf("    Queue Length: %u\n", cpu_stats.queue_length);
        printf("    Enqueues: %lu\n", cpu_stats.total_enqueues);
        printf("    Dequeues: %lu\n", cpu_stats.total_dequeues);
        printf("    Stolen From: %lu\n", cpu_stats.stolen_from);
        printf("    Stolen To: %lu\n", cpu_stats.stolen_to);
    }
}
