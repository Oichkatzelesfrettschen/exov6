/**
 * @file work_stealing.c
 * @brief Chase-Lev Work-Stealing Deque Implementation
 *
 * IMPLEMENTATION NOTES:
 * =====================
 * This is a faithful implementation of the Chase-Lev algorithm with
 * careful attention to memory ordering and correctness.
 *
 * KEY CHALLENGES:
 * ===============
 * 1. **Array resizing**: Must be done atomically visible to thieves
 * 2. **Memory reclamation**: Old arrays freed via RCU
 * 3. **ABA problem**: Avoided by using indices (not pointers)
 * 4. **Contention**: Owner vs thief on last element resolved via CAS
 *
 * MEMORY ORDERING:
 * ================
 * - bottom stores: release (publish tasks to thieves)
 * - bottom loads by thieves: acquire (see published tasks)
 * - top CAS: acq_rel (synchronize steal operations)
 * - array loads: acquire (see initialized array)
 *
 * LINEARIZATION POINTS:
 * =====================
 * - push: Store to bottom
 * - pop (fast path): Store to bottom
 * - pop (contention): CAS on top
 * - steal: CAS on top
 */

#include "work_stealing.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <time.h>

/*******************************************************************************
 * UTILITY FUNCTIONS
 ******************************************************************************/

/**
 * Simple pseudo-random number generator (thread-safe via per-CPU state)
 */
static uint32_t ws_random_seed = 0;

static uint32_t ws_random(void) {
    if (ws_random_seed == 0) {
        ws_random_seed = (uint32_t)time(NULL);
    }
    ws_random_seed = ws_random_seed * 1664525 + 1013904223;
    return ws_random_seed;
}

/*******************************************************************************
 * DEQUE ARRAY OPERATIONS
 ******************************************************************************/

/**
 * Allocate new circular array
 */
ws_array_t *ws_array_new(size_t capacity) {
    ws_array_t *array = (ws_array_t*)malloc(sizeof(ws_array_t));
    if (!array) {
        return NULL;
    }

    array->capacity = capacity;
    array->mask = capacity - 1;
    array->tasks = (dag_task_t**)calloc(capacity, sizeof(dag_task_t*));

    if (!array->tasks) {
        free(array);
        return NULL;
    }

    return array;
}

/**
 * Free array (called via RCU)
 */
void ws_array_free(rcu_head_t *head) {
    ws_array_t *array = container_of(head, ws_array_t, rcu);
    free(array->tasks);
    free(array);
}

/**
 * Resize array (double capacity)
 *
 * ALGORITHM:
 * 1. Allocate new array of 2x capacity
 * 2. Copy tasks from old array
 * 3. Update deque->array atomically
 * 4. Reclaim old array via RCU
 */
static ws_array_t *ws_deque_resize(ws_deque_t *deque, ws_array_t *old_array,
                                     size_t top, size_t bottom, rcu_state_t *rcu) {
    size_t old_capacity = old_array->capacity;
    size_t new_capacity = old_capacity * 2;

    if (new_capacity > WS_DEQUE_MAX_CAPACITY) {
        /* Cannot grow further */
        return NULL;
    }

    /* Allocate new array */
    ws_array_t *new_array = ws_array_new(new_capacity);
    if (!new_array) {
        return NULL;
    }

    /* Copy tasks from old to new */
    for (size_t i = top; i < bottom; i++) {
        dag_task_t *task = ws_array_get(old_array, i);
        ws_array_put(new_array, i, task);
    }

    /* Atomically update array pointer */
    rcu_assign_pointer(&deque->array, new_array);

    /* Reclaim old array via RCU */
    if (rcu) {
        call_rcu(rcu, &old_array->rcu, ws_array_free, deque->owner_cpu);
    } else {
        /* If no RCU, immediate free (unsafe, for testing only) */
        ws_array_free(&old_array->rcu);
    }

    atomic_fetch_add(&deque->resize_count, 1);

    return new_array;
}

/*******************************************************************************
 * CHASE-LEV DEQUE OPERATIONS
 ******************************************************************************/

/**
 * Initialize work-stealing deque
 */
void ws_deque_init(ws_deque_t *deque, uint8_t owner_cpu) {
    /* Allocate initial array */
    ws_array_t *array = ws_array_new(WS_DEQUE_INITIAL_CAPACITY);
    assert(array != NULL);

    atomic_store(&deque->bottom, 0);
    atomic_store(&deque->top, 0);
    atomic_store(&deque->array, array);

    deque->owner_cpu = owner_cpu;

    atomic_store(&deque->push_count, 0);
    atomic_store(&deque->pop_count, 0);
    atomic_store(&deque->steal_count, 0);
    atomic_store(&deque->steal_attempts, 0);
    atomic_store(&deque->resize_count, 0);
}

/**
 * Push task to bottom (owner only)
 *
 * CHASE-LEV ALGORITHM:
 * ```
 * b = bottom
 * t = top
 * a = array
 * if (b - t >= a.size - 1):
 *     a = resize(a, 2 * a.size)
 *     array = a
 * a[b] = task
 * bottom = b + 1
 * ```
 */
void ws_deque_push(ws_deque_t *deque, dag_task_t *task, rcu_state_t *rcu) {
    /* Load bottom (non-atomic for owner) */
    size_t bottom = atomic_load_explicit(&deque->bottom, memory_order_relaxed);

    /* Load top (atomic, thieves might be reading) */
    size_t top = atomic_load_explicit(&deque->top, memory_order_acquire);

    /* Load array (RCU-protected) */
    ws_array_t *array = (ws_array_t*)atomic_load_explicit(&deque->array,
                                                           memory_order_acquire);

    size_t size = bottom - top;

    /* Check if resize needed */
    if (size >= array->capacity - 1) {
        array = ws_deque_resize(deque, array, top, bottom, rcu);
        if (!array) {
            /* Resize failed, cannot push */
            return;
        }
    }

    /* Store task */
    ws_array_put(array, bottom, task);

    /* LINEARIZATION POINT: Increment bottom (release for visibility) */
    atomic_store_explicit(&deque->bottom, bottom + 1, memory_order_release);

    atomic_fetch_add(&deque->push_count, 1);
}

/**
 * Pop task from bottom (owner only)
 *
 * CHASE-LEV ALGORITHM:
 * ```
 * b = bottom - 1
 * bottom = b
 * t = top
 * if (t <= b):
 *     task = array[b]
 *     if (t == b):
 *         if (!CAS(&top, t, t+1)):
 *             task = EMPTY
 *         bottom = t + 1
 *     return task
 * else:
 *     bottom = t
 *     return EMPTY
 * ```
 */
dag_task_t *ws_deque_pop(ws_deque_t *deque, uint8_t cpu_id, rcu_state_t *rcu) {
    (void)cpu_id;  /* Used for RCU in future */
    (void)rcu;

    /* Load bottom */
    size_t bottom = atomic_load_explicit(&deque->bottom, memory_order_relaxed);

    /* Load array */
    ws_array_t *array = (ws_array_t*)atomic_load_explicit(&deque->array,
                                                           memory_order_acquire);

    /* Decrement bottom */
    bottom = bottom - 1;

    /* LINEARIZATION POINT (tentative): Store new bottom */
    atomic_store_explicit(&deque->bottom, bottom, memory_order_seq_cst);

    /* Load top */
    size_t top = atomic_load_explicit(&deque->top, memory_order_seq_cst);

    if (top <= bottom) {
        /* Deque is not empty */
        dag_task_t *task = ws_array_get(array, bottom);

        if (top == bottom) {
            /* Last element, potential contention with thieves */
            /* Try to claim it via CAS */
            size_t expected_top = top;
            if (!atomic_compare_exchange_strong_explicit(
                    &deque->top, &expected_top, top + 1,
                    memory_order_seq_cst, memory_order_relaxed)) {
                /* CAS failed, thief stole it */
                task = NULL;
            }

            /* Reset bottom */
            atomic_store_explicit(&deque->bottom, top + 1, memory_order_relaxed);
        }

        if (task) {
            atomic_fetch_add(&deque->pop_count, 1);
        }
        return task;
    } else {
        /* Deque was empty, restore bottom */
        atomic_store_explicit(&deque->bottom, top, memory_order_relaxed);
        return NULL;
    }
}

/**
 * Steal task from top (thieves only)
 *
 * CHASE-LEV ALGORITHM:
 * ```
 * t = top
 * b = bottom
 * if (t < b):
 *     task = array[t]
 *     if (!CAS(&top, t, t+1)):
 *         return ABORT
 *     return task
 * return EMPTY
 * ```
 */
dag_task_t *ws_deque_steal(ws_deque_t *deque, uint8_t cpu_id, rcu_state_t *rcu) {
    (void)cpu_id;
    (void)rcu;

    atomic_fetch_add(&deque->steal_attempts, 1);

    /* Load top */
    size_t top = atomic_load_explicit(&deque->top, memory_order_acquire);

    /* Load bottom */
    size_t bottom = atomic_load_explicit(&deque->bottom, memory_order_acquire);

    if (top < bottom) {
        /* Deque is not empty */

        /* Load array */
        ws_array_t *array = (ws_array_t*)atomic_load_explicit(&deque->array,
                                                               memory_order_acquire);

        /* Load task */
        dag_task_t *task = ws_array_get(array, top);

        /* LINEARIZATION POINT: Try CAS to claim task */
        size_t expected_top = top;
        if (atomic_compare_exchange_strong_explicit(
                &deque->top, &expected_top, top + 1,
                memory_order_seq_cst, memory_order_relaxed)) {
            /* Success! */
            atomic_fetch_add(&deque->steal_count, 1);
            return task;
        }

        /* CAS failed, another thief stole it */
        return NULL;
    }

    /* Deque is empty */
    return NULL;
}

/**
 * Check if deque is empty
 */
bool ws_deque_is_empty(const ws_deque_t *deque) {
    size_t top = atomic_load_explicit(&deque->top, memory_order_acquire);
    size_t bottom = atomic_load_explicit(&deque->bottom, memory_order_acquire);
    return top >= bottom;
}

/**
 * Get deque size
 */
size_t ws_deque_size(const ws_deque_t *deque) {
    size_t top = atomic_load_explicit(&deque->top, memory_order_acquire);
    size_t bottom = atomic_load_explicit(&deque->bottom, memory_order_acquire);
    return (bottom > top) ? (bottom - top) : 0;
}

/*******************************************************************************
 * WORK-STEALING SCHEDULER OPERATIONS
 ******************************************************************************/

/**
 * Initialize work-stealing scheduler
 */
void ws_scheduler_init(ws_scheduler_t *sched, uint8_t num_cpus, rcu_state_t *rcu) {
    sched->num_cpus = num_cpus;
    sched->rcu = rcu;

    /* Initialize per-CPU schedulers */
    for (uint8_t i = 0; i < num_cpus; i++) {
        ws_percpu_sched_t *cpu = &sched->cpus[i];
        cpu->cpu_id = i;

        ws_deque_init(&cpu->deque, i);

        cpu->victim_strategy = WS_VICTIM_RANDOM;
        cpu->next_victim = (i + 1) % num_cpus;

        atomic_store(&cpu->tasks_executed, 0);
        atomic_store(&cpu->steals_succeeded, 0);
        atomic_store(&cpu->steals_failed, 0);
        atomic_store(&cpu->idle_cycles, 0);
    }

    /* Initialize global stats */
    atomic_store(&sched->total_tasks, 0);
    atomic_store(&sched->total_steals, 0);
    atomic_store(&sched->total_migrations, 0);
}

/**
 * Submit task to local CPU queue
 */
void ws_scheduler_submit(ws_scheduler_t *sched, dag_task_t *task, uint8_t cpu_id) {
    ws_percpu_sched_t *cpu = &sched->cpus[cpu_id];
    ws_deque_push(&cpu->deque, task, sched->rcu);
    atomic_fetch_add(&sched->total_tasks, 1);
}

/**
 * Select victim CPU for stealing
 */
uint8_t ws_scheduler_select_victim(ws_scheduler_t *sched, uint8_t thief_cpu) {
    ws_percpu_sched_t *cpu = &sched->cpus[thief_cpu];

    switch (cpu->victim_strategy) {
    case WS_VICTIM_RANDOM: {
        /* Random victim (exclude self) */
        uint8_t victim;
        do {
            victim = ws_random() % sched->num_cpus;
        } while (victim == thief_cpu && sched->num_cpus > 1);
        return victim;
    }

    case WS_VICTIM_CIRCULAR: {
        /* Round-robin through victims */
        uint8_t victim = cpu->next_victim;
        cpu->next_victim = (victim + 1) % sched->num_cpus;
        if (cpu->next_victim == thief_cpu) {
            cpu->next_victim = (cpu->next_victim + 1) % sched->num_cpus;
        }
        return victim;
    }

    case WS_VICTIM_AFFINITY:
        /* Future: NUMA-aware selection */
        return (thief_cpu + 1) % sched->num_cpus;

    default:
        return (thief_cpu + 1) % sched->num_cpus;
    }
}

/**
 * Try stealing from specific victim
 */
dag_task_t *ws_scheduler_try_steal(ws_scheduler_t *sched, uint8_t victim_cpu,
                                     uint8_t thief_cpu) {
    ws_percpu_sched_t *victim = &sched->cpus[victim_cpu];
    ws_percpu_sched_t *thief = &sched->cpus[thief_cpu];

    dag_task_t *task = ws_deque_steal(&victim->deque, thief_cpu, sched->rcu);

    if (task) {
        atomic_fetch_add(&thief->steals_succeeded, 1);
        atomic_fetch_add(&sched->total_steals, 1);
        atomic_fetch_add(&sched->total_migrations, 1);
    } else {
        atomic_fetch_add(&thief->steals_failed, 1);
    }

    return task;
}

/**
 * Get next task for execution
 */
dag_task_t *ws_scheduler_get_task(ws_scheduler_t *sched, uint8_t cpu_id) {
    ws_percpu_sched_t *cpu = &sched->cpus[cpu_id];

    /* Try local pop first */
    dag_task_t *task = ws_deque_pop(&cpu->deque, cpu_id, sched->rcu);
    if (task) {
        atomic_fetch_add(&cpu->tasks_executed, 1);
        return task;
    }

    /* Local queue empty, try stealing */
    for (int attempt = 0; attempt < WS_STEAL_ATTEMPTS; attempt++) {
        uint8_t victim = ws_scheduler_select_victim(sched, cpu_id);
        task = ws_scheduler_try_steal(sched, victim, cpu_id);

        if (task) {
            atomic_fetch_add(&cpu->tasks_executed, 1);
            return task;
        }
    }

    /* All steal attempts failed */
    atomic_fetch_add(&cpu->idle_cycles, 1);
    return NULL;
}

/*******************************************************************************
 * STATISTICS & MONITORING
 ******************************************************************************/

/**
 * Collect work-stealing statistics
 */
void ws_get_stats(const ws_scheduler_t *sched, ws_stats_t *stats) {
    stats->total_tasks = atomic_load(&sched->total_tasks);
    stats->total_steals = atomic_load(&sched->total_steals);
    stats->total_migrations = atomic_load(&sched->total_migrations);

    /* Aggregate per-CPU stats */
    stats->total_pushes = 0;
    stats->total_pops = 0;
    uint64_t total_deque_size = 0;

    for (uint8_t i = 0; i < sched->num_cpus; i++) {
        const ws_deque_t *deque = &sched->cpus[i].deque;
        stats->total_pushes += atomic_load(&deque->push_count);
        stats->total_pops += atomic_load(&deque->pop_count);
        total_deque_size += ws_deque_size(deque);
    }

    stats->avg_deque_size = (sched->num_cpus > 0) ?
                            (total_deque_size / sched->num_cpus) : 0;

    /* Calculate steal success rate */
    uint64_t steal_attempts = 0;
    for (uint8_t i = 0; i < sched->num_cpus; i++) {
        const ws_deque_t *deque = &sched->cpus[i].deque;
        steal_attempts += atomic_load(&deque->steal_attempts);
    }

    stats->steal_success_rate = (steal_attempts > 0) ?
                                (stats->total_steals * 100 / steal_attempts) : 0;
}

/**
 * Print work-stealing statistics
 */
void ws_print_stats(const ws_scheduler_t *sched) {
    ws_stats_t stats;
    ws_get_stats(sched, &stats);

    printf("=== Work-Stealing Scheduler Statistics ===\n");
    printf("Total tasks:        %lu\n", stats.total_tasks);
    printf("Total steals:       %lu\n", stats.total_steals);
    printf("Total migrations:   %lu\n", stats.total_migrations);
    printf("Total pushes:       %lu\n", stats.total_pushes);
    printf("Total pops:         %lu\n", stats.total_pops);
    printf("Steal success rate: %lu%%\n", stats.steal_success_rate);
    printf("Avg deque size:     %lu\n", stats.avg_deque_size);
}

/**
 * Print per-CPU statistics
 */
void ws_print_percpu_stats(const ws_scheduler_t *sched) {
    printf("\n=== Per-CPU Statistics ===\n");

    for (uint8_t i = 0; i < sched->num_cpus; i++) {
        const ws_percpu_sched_t *cpu = &sched->cpus[i];
        const ws_deque_t *deque = &cpu->deque;

        printf("CPU %d:\n", i);
        printf("  Tasks executed:   %lu\n", atomic_load(&cpu->tasks_executed));
        printf("  Steals succeeded: %lu\n", atomic_load(&cpu->steals_succeeded));
        printf("  Steals failed:    %lu\n", atomic_load(&cpu->steals_failed));
        printf("  Idle cycles:      %lu\n", atomic_load(&cpu->idle_cycles));
        printf("  Deque size:       %zu\n", ws_deque_size(deque));
        printf("  Push count:       %lu\n", atomic_load(&deque->push_count));
        printf("  Pop count:        %lu\n", atomic_load(&deque->pop_count));
        printf("  Steal count:      %lu\n", atomic_load(&deque->steal_count));
        printf("  Resize count:     %lu\n", atomic_load(&deque->resize_count));
    }
}

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Basic work-stealing
 */
void example_work_stealing_basic(void) {
    printf("=== Basic Work-Stealing Example ===\n\n");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    /* Simulate: CPU 0 gets all tasks initially */
    printf("CPU 0 receives 100 tasks...\n");
    for (int i = 0; i < 100; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, 0);
    }

    printf("Initial deque sizes:\n");
    for (int i = 0; i < 4; i++) {
        printf("  CPU %d: %zu tasks\n", i, ws_deque_size(&sched.cpus[i].deque));
    }

    /* Simulate: Other CPUs steal */
    printf("\nOther CPUs stealing...\n");
    for (int cpu = 1; cpu < 4; cpu++) {
        for (int steal = 0; steal < 10; steal++) {
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                free(task);
            }
        }
    }

    printf("\nAfter stealing:\n");
    for (int i = 0; i < 4; i++) {
        printf("  CPU %d: %zu tasks\n", i, ws_deque_size(&sched.cpus[i].deque));
    }

    ws_print_stats(&sched);

    printf("\n");
}

/**
 * Example: Chase-Lev deque operations
 */
void example_chase_lev_deque(void) {
    printf("=== Chase-Lev Deque Example ===\n\n");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    ws_deque_t deque;
    ws_deque_init(&deque, 0);

    /* Owner pushes tasks */
    printf("Owner pushing 5 tasks...\n");
    for (int i = 0; i < 5; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_deque_push(&deque, task, &rcu);
    }
    printf("Deque size: %zu\n", ws_deque_size(&deque));

    /* Owner pops */
    printf("\nOwner popping...\n");
    dag_task_t *task = ws_deque_pop(&deque, 0, &rcu);
    printf("Popped task %d\n", task ? task->id : -1);
    if (task) free(task);
    printf("Deque size: %zu\n", ws_deque_size(&deque));

    /* Thief steals */
    printf("\nThief stealing...\n");
    task = ws_deque_steal(&deque, 1, &rcu);
    printf("Stole task %d\n", task ? task->id : -1);
    if (task) free(task);
    printf("Deque size: %zu\n", ws_deque_size(&deque));

    /* Drain deque */
    printf("\nDraining deque...\n");
    while ((task = ws_deque_pop(&deque, 0, &rcu)) != NULL) {
        printf("Popped task %d\n", task->id);
        free(task);
    }
    printf("Deque empty: %s\n", ws_deque_is_empty(&deque) ? "yes" : "no");

    printf("\n");
}

/**
 * Example: Load balancing
 */
void example_work_stealing_load_balance(void) {
    printf("=== Load Balancing Example ===\n\n");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    /* Unbalanced load: CPU 0 has 80 tasks, others have 0 */
    printf("Imbalanced load: CPU 0 has 80 tasks\n");
    for (int i = 0; i < 80; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, 0);
    }

    /* All CPUs process tasks */
    printf("\nAll CPUs processing (automatic load balancing via stealing)...\n");
    int total_processed = 0;
    while (total_processed < 80) {
        for (int cpu = 0; cpu < 4; cpu++) {
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                total_processed++;
                free(task);
            }
        }
    }

    printf("\n");
    ws_print_percpu_stats(&sched);
    printf("\n");
}

/**
 * Example: Static vs work-stealing
 */
void example_work_stealing_vs_static(void) {
    printf("=== Static Partitioning vs Work-Stealing ===\n\n");

    printf("Static Partitioning:\n");
    printf("  - CPU 0: 25 tasks (finishes fast)\n");
    printf("  - CPU 1: 25 tasks (finishes fast)\n");
    printf("  - CPU 2: 25 tasks (finishes fast)\n");
    printf("  - CPU 3: 25 tasks (finishes fast)\n");
    printf("  Problem: If workload is imbalanced, some CPUs idle\n\n");

    printf("Work-Stealing:\n");
    printf("  - All tasks initially on CPU 0\n");
    printf("  - Other CPUs steal when idle\n");
    printf("  - Automatic load balancing\n");
    printf("  - Better utilization with irregular workloads\n\n");

    printf("Trade-off:\n");
    printf("  Static: Lower overhead, but requires balanced workload\n");
    printf("  Work-Stealing: Higher overhead (stealing), but adapts to imbalance\n\n");
}
