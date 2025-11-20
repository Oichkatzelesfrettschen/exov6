/**
 * @file task_exec.c
 * @brief Task Execution Model Implementation
 *
 * @see include/task_exec.h for API documentation
 */

#include "task_exec.h"
#include "resource_vector.h"
#include "printf.h"
#include <stdint.h>
#include <string.h>

/*******************************************************************************
 * TASK LIFECYCLE IMPLEMENTATION
 ******************************************************************************/

/**
 * Initialize task execution context
 */
void task_exec_init(task_context_t *ctx, dag_task_t *task, int cap_slot)
{
    if (ctx == NULL || task == NULL) {
        return;
    }

    memset(ctx, 0, sizeof(task_context_t));

    ctx->task = task;
    ctx->capability_slot = cap_slot;
    ctx->quantum_remaining_us = TIME_QUANTUM_MS * 1000; /* Convert ms to μs */
    ctx->preferred_cpu = 0; /* Default to CPU 0 */
}

/**
 * Start task execution
 */
void task_exec_start(task_context_t *ctx, uint64_t now)
{
    if (ctx == NULL) {
        return;
    }

    ctx->start_time_us = now;
    ctx->last_scheduled_us = now;
    ctx->quantum_remaining_us = TIME_QUANTUM_MS * 1000;
    ctx->quantum_expired = false;

    /* Transition task state */
    if (ctx->task != NULL) {
        ctx->task->state = TASK_STATE_RUNNING;
        ctx->task->start_time = now / 1000; /* Store in ms */
    }
}

/**
 * Execute task for a duration
 *
 * ALGORITHM:
 * 1. Consume quantum time
 * 2. Update CPU time used
 * 3. Simulate work progress
 * 4. Check if work complete
 */
bool task_exec_run(task_context_t *ctx, uint64_t duration_us)
{
    if (ctx == NULL) {
        return false;
    }

    /* Consume quantum */
    task_consume_quantum(ctx, duration_us);

    /* Update CPU time */
    ctx->cpu_time_used_us += duration_us;

    /* Check if work is complete */
    return task_is_work_complete(ctx);
}

/**
 * Preempt task execution
 */
void task_exec_preempt(task_context_t *ctx, uint64_t now)
{
    if (ctx == NULL) {
        return;
    }

    /* Mark preemption */
    ctx->context_switches++;
    ctx->quantum_expired = true;

    /* Calculate wait time (will start accumulating when back in READY) */
    uint64_t running_time = now - ctx->last_scheduled_us;
    (void)running_time; /* Used for accounting */

    /* Transition task state */
    if (ctx->task != NULL) {
        ctx->task->state = TASK_STATE_READY;
    }
}

/**
 * Complete task execution
 */
void task_exec_complete(task_context_t *ctx, uint64_t now)
{
    if (ctx == NULL) {
        return;
    }

    /* Transition task state */
    if (ctx->task != NULL) {
        ctx->task->state = TASK_STATE_COMPLETED;
        ctx->task->end_time = now / 1000; /* Store in ms */
    }
}

/*******************************************************************************
 * QUANTUM MANAGEMENT
 ******************************************************************************/

bool task_should_preempt(const task_context_t *ctx)
{
    if (ctx == NULL) {
        return false;
    }

    return ctx->quantum_remaining_us == 0 || ctx->quantum_expired;
}

void task_consume_quantum(task_context_t *ctx, uint64_t elapsed_us)
{
    if (ctx == NULL) {
        return;
    }

    if (elapsed_us >= ctx->quantum_remaining_us) {
        ctx->quantum_remaining_us = 0;
        ctx->quantum_expired = true;
    } else {
        ctx->quantum_remaining_us -= elapsed_us;
    }
}

void task_reset_quantum(task_context_t *ctx)
{
    if (ctx == NULL) {
        return;
    }

    ctx->quantum_remaining_us = TIME_QUANTUM_MS * 1000;
    ctx->quantum_expired = false;
}

uint64_t task_get_quantum_remaining(const task_context_t *ctx)
{
    return ctx ? ctx->quantum_remaining_us : 0;
}

/*******************************************************************************
 * CONTEXT SWITCHING
 ******************************************************************************/

/**
 * Perform context switch
 *
 * Simulates realistic overhead:
 * - Register save/restore
 * - TLB flush (if different address space)
 * - Cache pollution (working set displaced)
 * - Pipeline flush
 */
uint64_t task_context_switch(task_context_t *from, task_context_t *to)
{
    uint64_t cost = CONTEXT_SWITCH_COST_US;

    /* Update context switch counts */
    if (from != NULL) {
        from->context_switches++;
    }

    if (to != NULL) {
        to->context_switches++;
    }

    /* Additional cost if switching between different tasks */
    if (from != NULL && to != NULL && from->task != to->task) {
        /* TLB flush adds extra overhead */
        cost += 1; /* +1 μs for TLB flush */
    }

    return cost;
}

uint64_t task_get_context_switch_overhead(const task_context_t *ctx)
{
    if (ctx == NULL) {
        return 0;
    }

    return ctx->context_switches * CONTEXT_SWITCH_COST_US;
}

/*******************************************************************************
 * CPU AFFINITY
 ******************************************************************************/

void task_set_preferred_cpu(task_context_t *ctx, uint8_t cpu_id)
{
    if (ctx == NULL || cpu_id >= MAX_CPUS) {
        return;
    }

    ctx->preferred_cpu = cpu_id;
}

uint8_t task_get_preferred_cpu(const task_context_t *ctx)
{
    return ctx ? ctx->preferred_cpu : 0;
}

bool task_on_preferred_cpu(const task_context_t *ctx)
{
    if (ctx == NULL) {
        return false;
    }

    return ctx->cpu_id == ctx->preferred_cpu;
}

/*******************************************************************************
 * STATISTICS & INTROSPECTION
 ******************************************************************************/

uint64_t task_get_turnaround_time(const task_context_t *ctx, uint64_t now)
{
    if (ctx == NULL || ctx->start_time_us == 0) {
        return 0;
    }

    return now - ctx->start_time_us;
}

uint64_t task_get_wait_time(const task_context_t *ctx)
{
    return ctx ? ctx->total_wait_time_us : 0;
}

q16_t task_get_utilization(const task_context_t *ctx, uint64_t now)
{
    if (ctx == NULL || ctx->start_time_us == 0) {
        return 0;
    }

    uint64_t turnaround = task_get_turnaround_time(ctx, now);
    if (turnaround == 0) {
        return 0;
    }

    /* Utilization = cpu_time / turnaround_time */
    uint64_t util_scaled = (ctx->cpu_time_used_us << 16) / turnaround;

    return (q16_t)util_scaled;
}

void task_print_stats(const task_context_t *ctx)
{
    if (ctx == NULL || ctx->task == NULL) {
        return;
    }

    printf("\n=== Task Execution Statistics ===\n");
    printf("Task: %s (ID %u)\n", ctx->task->name, ctx->task->id);
    printf("CPU time: %llu μs (%.2f ms)\n",
           ctx->cpu_time_used_us,
           ctx->cpu_time_used_us / 1000.0);
    printf("Context switches: %llu\n", ctx->context_switches);
    printf("Context switch overhead: %llu μs\n",
           task_get_context_switch_overhead(ctx));

    if (ctx->task->state == TASK_STATE_COMPLETED) {
        uint64_t turnaround = ctx->task->end_time - ctx->task->start_time;
        printf("Turnaround time: %llu ms\n", turnaround);
        printf("Wait time: %llu μs (%.2f ms)\n",
               ctx->total_wait_time_us,
               ctx->total_wait_time_us / 1000.0);
    }

    printf("CPU affinity: %u (preferred: %u)\n",
           ctx->cpu_id, ctx->preferred_cpu);
    printf("=================================\n\n");
}

/*******************************************************************************
 * WORK SIMULATION
 ******************************************************************************/

/**
 * Estimate work remaining
 *
 * Uses resource norm as proxy:
 * - norm = 1.0 → 100ms work
 * - norm = 2.0 → 200ms work
 * - norm = 0.5 →  50ms work
 */
uint64_t task_estimate_work_remaining(const task_context_t *ctx)
{
    if (ctx == NULL || ctx->task == NULL) {
        return 0;
    }

    /* Compute resource norm (represents work complexity) */
    q16_t norm = resource_vector_norm(ctx->task->resources);

    /* Convert to microseconds: norm * 100ms */
    uint64_t total_work_us = ((uint64_t)norm * 100000) >> 16;

    /* Subtract work already done */
    if (ctx->cpu_time_used_us >= total_work_us) {
        return 0;
    }

    return total_work_us - ctx->cpu_time_used_us;
}

bool task_is_work_complete(const task_context_t *ctx)
{
    return task_estimate_work_remaining(ctx) == 0;
}

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Task lifecycle
 */
void example_task_lifecycle(void)
{
    printf("\n=== Example: Task Lifecycle ===\n");
    printf("Demonstrating state transitions: NEW → READY → RUNNING → COMPLETED\n\n");

    /* Create task */
    dag_task_t task;
    task.id = 0;
    strcpy(task.name, "Example Task");
    task.resources.cpu = Q16(1.0);
    task.resources.memory = Q16(200.0);
    task.state = TASK_STATE_READY;

    /* Initialize execution context */
    task_context_t ctx;
    task_exec_init(&ctx, &task, -1);

    printf("1. Task initialized (state: READY)\n");

    /* Start execution */
    uint64_t now = 0;
    task_exec_start(&ctx, now);
    printf("2. Task started (state: %s)\n",
           task.state == TASK_STATE_RUNNING ? "RUNNING" : "???");

    /* Run for 5ms */
    now += 5000; /* 5ms = 5000 μs */
    bool complete = task_exec_run(&ctx, 5000);
    printf("3. Task ran for 5ms (complete: %s, quantum: %llu μs)\n",
           complete ? "YES" : "NO",
           task_get_quantum_remaining(&ctx));

    /* Preempt (quantum expires) */
    now += 5000;
    task_exec_run(&ctx, 5000);
    if (task_should_preempt(&ctx)) {
        task_exec_preempt(&ctx, now);
        printf("4. Task preempted (state: %s)\n",
               task.state == TASK_STATE_READY ? "READY" : "???");
    }

    /* Resume and complete */
    task_exec_start(&ctx, now);
    now += 100000; /* Run until complete */
    complete = task_exec_run(&ctx, 100000);
    if (complete) {
        task_exec_complete(&ctx, now);
        printf("5. Task completed (state: %s)\n",
               task.state == TASK_STATE_COMPLETED ? "COMPLETED" : "???");
    }

    task_print_stats(&ctx);
    printf("==============================\n\n");
}

/**
 * Example: Quantum-based preemption
 */
void example_quantum_preemption(void)
{
    printf("\n=== Example: Quantum-Based Preemption ===\n");
    printf("Time quantum: %u ms\n", TIME_QUANTUM_MS);
    printf("Task will be preempted after quantum expires\n\n");

    /* Create long-running task */
    dag_task_t task;
    task.id = 1;
    strcpy(task.name, "CPU-bound Task");
    task.resources.cpu = Q16(10.0); /* Lots of work */
    task.state = TASK_STATE_READY;

    task_context_t ctx;
    task_exec_init(&ctx, &task, -1);

    uint64_t now = 0;
    task_exec_start(&ctx, now);

    /* Run in 1ms increments until quantum expires */
    for (int i = 0; i < 15; i++) {
        now += 1000; /* 1ms */
        task_exec_run(&ctx, 1000);

        printf("Time %2d ms: quantum remaining = %llu μs\n",
               i + 1,
               task_get_quantum_remaining(&ctx));

        if (task_should_preempt(&ctx)) {
            printf("  → PREEMPTED (quantum expired)\n");
            task_exec_preempt(&ctx, now);
            break;
        }
    }

    printf("\n");
    task_print_stats(&ctx);
    printf("=========================================\n\n");
}

/**
 * Example: Context switch overhead
 */
void example_context_switch_cost(void)
{
    printf("\n=== Example: Context Switch Overhead ===\n");
    printf("Context switch cost: %u μs per switch\n", CONTEXT_SWITCH_COST_US);
    printf("Simulating rapid task switching (round-robin)\n\n");

    /* Create 3 tasks */
    dag_task_t tasks[3];
    task_context_t contexts[3];

    for (int i = 0; i < 3; i++) {
        tasks[i].id = i;
        snprintf(tasks[i].name, sizeof(tasks[i].name), "Task %d", i);
        tasks[i].resources.cpu = Q16(1.0);
        tasks[i].state = TASK_STATE_READY;

        task_exec_init(&contexts[i], &tasks[i], -1);
    }

    /* Simulate rapid switching (1ms each) */
    uint64_t now = 0;
    for (int round = 0; round < 5; round++) {
        for (int i = 0; i < 3; i++) {
            /* Context switch */
            task_context_t *prev = (i == 0) ? NULL : &contexts[i - 1];
            uint64_t switch_cost = task_context_switch(prev, &contexts[i]);
            now += switch_cost;

            /* Run task */
            task_exec_start(&contexts[i], now);
            now += 1000; /* 1ms */
            task_exec_run(&contexts[i], 1000);
            task_exec_preempt(&contexts[i], now);
        }
    }

    /* Print statistics */
    printf("After 5 rounds of switching:\n");
    for (int i = 0; i < 3; i++) {
        printf("\nTask %d:\n", i);
        printf("  Context switches: %llu\n", contexts[i].context_switches);
        printf("  Total overhead: %llu μs (%.2f ms)\n",
               task_get_context_switch_overhead(&contexts[i]),
               task_get_context_switch_overhead(&contexts[i]) / 1000.0);
        printf("  CPU time: %llu μs (%.2f ms)\n",
               contexts[i].cpu_time_used_us,
               contexts[i].cpu_time_used_us / 1000.0);

        /* Efficiency = cpu_time / (cpu_time + overhead) */
        uint64_t overhead = task_get_context_switch_overhead(&contexts[i]);
        uint64_t total = contexts[i].cpu_time_used_us + overhead;
        double efficiency = (contexts[i].cpu_time_used_us * 100.0) / total;
        printf("  Efficiency: %.1f%%\n", efficiency);
    }

    printf("\n========================================\n\n");
}

/**
 * Run all task execution examples
 */
void task_exec_run_all_examples(void)
{
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   TASK EXECUTION MODEL - EXAMPLES                          ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n");

    example_task_lifecycle();
    example_quantum_preemption();
    example_context_switch_cost();

    printf("All task execution examples completed.\n");
    printf("See include/task_exec.h for API documentation.\n\n");
}
