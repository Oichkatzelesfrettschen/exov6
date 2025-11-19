/**
 * @file sched_admission.c
 * @brief Stochastic Admission Control Implementation
 *
 * @see include/sched_admission.h for API documentation
 */

#include "sched_admission.h"
#include "resource_vector.h"
#include "printf.h"
#include <stdint.h>
#include <string.h>

/*******************************************************************************
 * HELPER FUNCTIONS
 ******************************************************************************/

/**
 * Sum resources of all RUNNING tasks
 */
static resource_vector_t sum_running_resources(const dag_pdac_t *dag)
{
    resource_vector_t total = {0};

    if (dag == NULL) {
        return total;
    }

    for (uint16_t i = 0; i < dag->num_tasks; i++) {
        if (dag->tasks[i].state == TASK_STATE_RUNNING) {
            total = resource_vector_add(total, dag->tasks[i].resources);
        }
    }

    return total;
}

/*******************************************************************************
 * CORE API IMPLEMENTATION
 ******************************************************************************/

/**
 * Initialize admission control
 */
void admission_init(
    admission_control_t *ac,
    lcg_state_t *rng,
    resource_vector_t capacity,
    resource_vector_t refill_rate,
    resource_vector_t burst_size)
{
    if (ac == NULL || rng == NULL) {
        return;
    }

    /* Initialize RNG */
    ac->rng = rng;

    /* Initialize token bucket */
    token_bucket_init(&ac->quota, refill_rate, burst_size);

    /* Store system capacity */
    ac->system_capacity = capacity;

    /* Reset statistics */
    ac->total_attempts = 0;
    ac->token_admits = 0;
    ac->stochastic_admits = 0;
    ac->rejections = 0;
    ac->current_load = 0;
}

/**
 * Try to admit a task
 *
 * ALGORITHM WALKTHROUGH:
 * ======================
 * Example: System capacity = CPU:4.0, MEM:1024
 *          Running tasks   = CPU:3.2, MEM:800
 *          New task        = CPU:1.0, MEM:200
 *
 * Stage 1: Token bucket check
 *   - Tokens available for {CPU:1.0, MEM:200}? NO (would exceed CPU quota)
 *   - Go to Stage 2
 *
 * Stage 2: Stochastic admission
 *   - Load = norm(3.2, 800) / norm(4.0, 1024) ≈ 0.82
 *   - P(admit) = 1 / (1 + 0.82) ≈ 0.55
 *   - Random = 0.42 < 0.55? YES → ADMIT
 *   - Update statistics: stochastic_admits++
 */
int admission_try_admit(
    admission_control_t *ac,
    const dag_pdac_t *dag,
    const dag_task_t *task)
{
    if (ac == NULL || dag == NULL || task == NULL) {
        return 0;
    }

    ac->total_attempts++;

    /* Compute resource norm for this task */
    q16_t task_norm = resource_vector_norm(task->resources);

    /* Stage 1: Try token bucket (hard quota) */
    if (token_bucket_consume(&ac->quota, task_norm)) {
        ac->token_admits++;
        return 1; /* Admitted via token bucket */
    }

    /* Stage 2: Stochastic admission (soft limit) */

    /* Compute current load */
    ac->current_load = admission_compute_load(ac, dag);

    /* Compute admission probability */
    q16_t admit_prob = admission_compute_probability(ac->current_load);

    /* Make stochastic decision */
    double u = lcg_uniform(ac->rng);
    double prob = (double)admit_prob / 65536.0;

    if (u < prob) {
        /* Admitted stochastically */
        ac->stochastic_admits++;
        return 1;
    }

    /* Rejected */
    ac->rejections++;
    return 0;
}

/**
 * Release resources when task completes
 */
void admission_release(
    admission_control_t *ac,
    const dag_task_t *task)
{
    if (ac == NULL || task == NULL) {
        return;
    }

    /* Note: Token bucket refill happens periodically via admission_refill() */
    /* This function is a placeholder for future resource tracking */
    (void)task;
}

/**
 * Refill token bucket
 */
void admission_refill(
    admission_control_t *ac,
    uint32_t dt_ms)
{
    if (ac == NULL) {
        return;
    }

    token_bucket_refill(&ac->quota, dt_ms);
}

/*******************************************************************************
 * LOAD COMPUTATION
 ******************************************************************************/

/**
 * Compute current system load
 *
 * Load = ||running_resources|| / ||capacity||
 */
q16_t admission_compute_load(
    const admission_control_t *ac,
    const dag_pdac_t *dag)
{
    if (ac == NULL || dag == NULL) {
        return 0;
    }

    /* Sum resources of all running tasks */
    resource_vector_t running = sum_running_resources(dag);

    /* Compute norms */
    q16_t running_norm = resource_vector_norm(running);
    q16_t capacity_norm = resource_vector_norm(ac->system_capacity);

    /* Load = running / capacity */
    if (capacity_norm == 0) {
        return Q16(1.0); /* Assume full load if capacity is zero */
    }

    /* Q16 division: (running_norm << 16) / capacity_norm */
    uint64_t load = ((uint64_t)running_norm << 16) / capacity_norm;

    return (q16_t)load;
}

/**
 * Compute admission probability from load
 *
 * Formula: P = 1 / (1 + load)
 *
 * Implemented using Q16 fixed-point:
 *   P = (1 << 16) / ((1 << 16) + load)
 */
q16_t admission_compute_probability(q16_t load)
{
    /* P = 1.0 / (1.0 + load) */
    uint64_t denominator = Q16(1.0) + load;

    if (denominator == 0) {
        return ADMISSION_MAX_PROBABILITY;
    }

    uint64_t prob = ((uint64_t)Q16(1.0) << 16) / denominator;

    /* Clamp to [MIN, MAX] */
    if (prob < ADMISSION_MIN_PROBABILITY) {
        prob = ADMISSION_MIN_PROBABILITY;
    }
    if (prob > ADMISSION_MAX_PROBABILITY) {
        prob = ADMISSION_MAX_PROBABILITY;
    }

    return (q16_t)prob;
}

/*******************************************************************************
 * STATISTICS & INTROSPECTION
 ******************************************************************************/

uint64_t admission_get_total_attempts(const admission_control_t *ac)
{
    return ac ? ac->total_attempts : 0;
}

uint64_t admission_get_token_admits(const admission_control_t *ac)
{
    return ac ? ac->token_admits : 0;
}

uint64_t admission_get_stochastic_admits(const admission_control_t *ac)
{
    return ac ? ac->stochastic_admits : 0;
}

uint64_t admission_get_rejections(const admission_control_t *ac)
{
    return ac ? ac->rejections : 0;
}

q16_t admission_get_rate(const admission_control_t *ac)
{
    if (ac == NULL || ac->total_attempts == 0) {
        return Q16(1.0);
    }

    uint64_t admitted = ac->token_admits + ac->stochastic_admits;
    uint64_t rate = (admitted << 16) / ac->total_attempts;

    return (q16_t)rate;
}

q16_t admission_get_current_load(const admission_control_t *ac)
{
    return ac ? ac->current_load : 0;
}

/**
 * Print admission control statistics
 */
void admission_print_stats(const admission_control_t *ac)
{
    if (ac == NULL) {
        return;
    }

    printf("\n=== Admission Control Statistics ===\n");
    printf("Total attempts:      %llu\n", ac->total_attempts);
    printf("Token bucket admits: %llu (%.1f%%)\n",
           ac->token_admits,
           (ac->token_admits * 100.0) / ac->total_attempts);
    printf("Stochastic admits:   %llu (%.1f%%)\n",
           ac->stochastic_admits,
           (ac->stochastic_admits * 100.0) / ac->total_attempts);
    printf("Rejections:          %llu (%.1f%%)\n",
           ac->rejections,
           (ac->rejections * 100.0) / ac->total_attempts);

    q16_t rate = admission_get_rate(ac);
    printf("Admission rate:      %.2f\n", (double)rate / 65536.0);
    printf("Current load:        %.2f\n\n",
           (double)ac->current_load / 65536.0);
}

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Admission probability curve
 */
void example_admission_probability_curve(void)
{
    printf("\n=== Example: Admission Probability Curve ===\n");
    printf("P(admit) = 1 / (1 + load)\n\n");

    printf("%-10s %-15s\n", "Load", "P(admit)");
    printf("----------------------------\n");

    q16_t loads[] = {
        Q16(0.0),  Q16(0.1),  Q16(0.5),  Q16(1.0),
        Q16(2.0),  Q16(5.0),  Q16(10.0), Q16(20.0)
    };

    for (int i = 0; i < 8; i++) {
        q16_t prob = admission_compute_probability(loads[i]);
        printf("%-10.1f %-15.3f\n",
               (double)loads[i] / 65536.0,
               (double)prob / 65536.0);
    }

    printf("\nNote: Probability decreases smoothly with load\n");
    printf("      Never reaches 0 (always a chance)\n");
    printf("=========================================\n\n");
}

/**
 * Example: Two-stage admission
 */
void example_admission_two_stage(void)
{
    printf("\n=== Example: Two-Stage Admission ===\n");
    printf("Stage 1: Token bucket (hard quota)\n");
    printf("Stage 2: Stochastic (soft limit)\n\n");

    /* Setup admission control */
    lcg_state_t rng;
    lcg_init(&rng, 42);

    resource_vector_t capacity = {
        .cpu = Q16(4.0),
        .memory = Q16(1024.0)
    };

    resource_vector_t refill_rate = {
        .cpu = Q16(0.1),    /* 0.1 CPU per tick */
        .memory = Q16(10.0) /* 10 MB per tick */
    };

    resource_vector_t burst_size = {
        .cpu = Q16(2.0),    /* Burst up to 2 CPU */
        .memory = Q16(512.0)
    };

    admission_control_t ac;
    admission_init(&ac, &rng, capacity, refill_rate, burst_size);

    /* Setup DAG with light load */
    dag_pdac_t dag;
    pdac_dag_init(&dag, capacity);

    /* Add running task (uses some resources) */
    resource_vector_t res_running = {.cpu = Q16(1.0), .memory = Q16(256.0)};
    int running_id = pdac_dag_add_task(&dag, "Running Task", res_running);
    dag.tasks[running_id].state = TASK_STATE_RUNNING;

    /* Try admitting several tasks */
    printf("Attempting to admit 10 tasks...\n");
    resource_vector_t res_new = {.cpu = Q16(0.5), .memory = Q16(128.0)};

    for (int i = 0; i < 10; i++) {
        dag_task_t new_task = {0};
        new_task.resources = res_new;
        strcpy(new_task.name, "New Task");

        int admitted = admission_try_admit(&ac, &dag, &new_task);
        printf("  Task %d: %s\n", i, admitted ? "ADMITTED" : "REJECTED");

        if (admitted && i < 5) {
            /* Add first 5 admitted tasks to DAG as running */
            int id = pdac_dag_add_task(&dag, "Admitted Task", res_new);
            dag.tasks[id].state = TASK_STATE_RUNNING;
        }
    }

    admission_print_stats(&ac);
    printf("========================================\n\n");
}

/**
 * Example: Graceful degradation under overload
 */
void example_admission_overload(void)
{
    printf("\n=== Example: Graceful Degradation ===\n");
    printf("System under heavy load still admits some tasks\n\n");

    /* Setup admission control with small capacity */
    lcg_state_t rng;
    lcg_init(&rng, 12345);

    resource_vector_t capacity = {.cpu = Q16(2.0), .memory = Q16(512.0)};
    resource_vector_t refill = {.cpu = Q16(0.01), .memory = Q16(1.0)};
    resource_vector_t burst = {.cpu = Q16(0.5), .memory = Q16(128.0)};

    admission_control_t ac;
    admission_init(&ac, &rng, capacity, refill, burst);

    /* Setup DAG with HEAVY load (already near capacity) */
    dag_pdac_t dag;
    pdac_dag_init(&dag, capacity);

    resource_vector_t res_heavy = {.cpu = Q16(1.8), .memory = Q16(480.0)};
    int heavy_id = pdac_dag_add_task(&dag, "Heavy Task", res_heavy);
    dag.tasks[heavy_id].state = TASK_STATE_RUNNING;

    /* Compute load */
    q16_t load = admission_compute_load(&ac, &dag);
    q16_t prob = admission_compute_probability(load);

    printf("System load: %.2f\n", (double)load / 65536.0);
    printf("Admission probability: %.2f\n\n", (double)prob / 65536.0);

    /* Try admitting 100 small tasks */
    printf("Attempting to admit 100 small tasks...\n");
    resource_vector_t res_small = {.cpu = Q16(0.1), .memory = Q16(50.0)};

    for (int i = 0; i < 100; i++) {
        dag_task_t task = {0};
        task.resources = res_small;
        strcpy(task.name, "Small Task");
        admission_try_admit(&ac, &dag, &task);
    }

    admission_print_stats(&ac);

    printf("Note: Even under heavy load, some tasks get admitted\n");
    printf("      (Graceful degradation, not hard cutoff)\n");
    printf("=====================================\n\n");
}

/**
 * Example: 8D load computation
 */
void example_admission_multidimensional_load(void)
{
    printf("\n=== Example: Multidimensional Load ===\n");
    printf("Computing load across 8D resource space\n\n");

    /* Setup capacity with all 8 dimensions */
    resource_vector_t capacity = {
        .cpu = Q16(4.0),
        .memory = Q16(1024.0),
        .io_bandwidth = Q16(100.0),
        .network_bandwidth = Q16(1000.0),
        .gpu_time = Q16(2.0),
        .disk_quota = Q16(10240.0),
        .irq_count = Q16(50.0),
        .capability_count = Q16(100.0)
    };

    printf("System capacity (8D):\n");
    printf("  CPU: %.1f, MEM: %.0f, IO: %.0f, NET: %.0f\n",
           (double)capacity.cpu / 65536.0,
           (double)capacity.memory / 65536.0,
           (double)capacity.io_bandwidth / 65536.0,
           (double)capacity.network_bandwidth / 65536.0);
    printf("  GPU: %.1f, DISK: %.0f, IRQ: %.0f, CAP: %.0f\n\n",
           (double)capacity.gpu_time / 65536.0,
           (double)capacity.disk_quota / 65536.0,
           (double)capacity.irq_count / 65536.0,
           (double)capacity.capability_count / 65536.0);

    /* Setup DAG with mixed workloads */
    dag_pdac_t dag;
    pdac_dag_init(&dag, capacity);

    /* CPU-bound task */
    resource_vector_t res_cpu = {.cpu = Q16(2.0), .memory = Q16(100.0)};
    int cpu_id = pdac_dag_add_task(&dag, "CPU-bound", res_cpu);
    dag.tasks[cpu_id].state = TASK_STATE_RUNNING;

    /* I/O-bound task */
    resource_vector_t res_io = {
        .cpu = Q16(0.5),
        .memory = Q16(200.0),
        .io_bandwidth = Q16(80.0)
    };
    int io_id = pdac_dag_add_task(&dag, "I/O-bound", res_io);
    dag.tasks[io_id].state = TASK_STATE_RUNNING;

    /* Compute load */
    lcg_state_t rng;
    lcg_init(&rng, 777);

    admission_control_t ac;
    ac.rng = &rng;
    ac.system_capacity = capacity;

    q16_t load = admission_compute_load(&ac, &dag);

    printf("Running tasks: CPU-bound + I/O-bound\n");
    printf("Total load (octonion norm): %.2f\n\n", (double)load / 65536.0);

    printf("Note: Load computed across all 8 dimensions\n");
    printf("      Uses octonion norm (non-associative algebra)\n");
    printf("=====================================\n\n");
}

/**
 * Run all admission control examples
 */
void admission_run_all_examples(void)
{
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   STOCHASTIC ADMISSION CONTROL - EXAMPLES                  ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n");

    example_admission_probability_curve();
    example_admission_two_stage();
    example_admission_overload();
    example_admission_multidimensional_load();

    printf("All admission control examples completed.\n");
    printf("See include/sched_admission.h for API documentation.\n\n");
}
