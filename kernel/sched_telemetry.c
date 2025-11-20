/**
 * @file sched_telemetry.c
 * @brief Performance Telemetry Implementation
 *
 * @see include/sched_telemetry.h for API documentation
 */

#include "sched_telemetry.h"
#include "printf.h"
#include <stdint.h>
#include <string.h>
#include <math.h>

/*******************************************************************************
 * TELEMETRY LIFECYCLE
 ******************************************************************************/

void telemetry_init(sched_telemetry_t *telem, uint8_t num_cpus)
{
    if (telem == NULL || num_cpus == 0 || num_cpus > MAX_CPUS) {
        return;
    }

    memset(telem, 0, sizeof(sched_telemetry_t));
    telem->num_cpus = num_cpus;
    telem->histogram_bucket_size_us = 1000; /* 1ms default */
}

void telemetry_reset(sched_telemetry_t *telem)
{
    if (telem == NULL) {
        return;
    }

    uint8_t num_cpus = telem->num_cpus;
    telemetry_init(telem, num_cpus);
}

void telemetry_start(sched_telemetry_t *telem, uint64_t now_us)
{
    if (telem == NULL) {
        return;
    }

    telem->start_time_us = now_us;
    telem->last_update_us = now_us;
}

/*******************************************************************************
 * EVENT RECORDING
 ******************************************************************************/

void telemetry_record_submit(sched_telemetry_t *telem,
                              uint16_t task_id,
                              uint64_t now_us)
{
    if (telem == NULL || task_id >= DAG_MAX_TASKS) {
        return;
    }

    telem->tasks[task_id].submit_time_us = now_us;
    telem->total_tasks_submitted++;

    if (task_id >= telem->num_tasks) {
        telem->num_tasks = task_id + 1;
    }
}

void telemetry_record_start(sched_telemetry_t *telem,
                             uint16_t task_id,
                             uint8_t cpu_id,
                             uint64_t now_us)
{
    if (telem == NULL || task_id >= DAG_MAX_TASKS || cpu_id >= MAX_CPUS) {
        return;
    }

    task_telemetry_t *task = &telem->tasks[task_id];

    /* Record first start time */
    if (task->start_time_us == 0) {
        task->start_time_us = now_us;

        /* Compute wait time (submit → first start) */
        if (task->submit_time_us > 0) {
            task->wait_time_us = now_us - task->submit_time_us;
        }
    }
}

void telemetry_record_complete(sched_telemetry_t *telem,
                                uint16_t task_id,
                                uint64_t now_us)
{
    if (telem == NULL || task_id >= DAG_MAX_TASKS) {
        return;
    }

    task_telemetry_t *task = &telem->tasks[task_id];

    task->complete_time_us = now_us;
    telem->total_tasks_completed++;

    /* Compute turnaround time (submit → complete) */
    if (task->submit_time_us > 0) {
        task->turnaround_time_us = now_us - task->submit_time_us;
    }

    /* Compute run time (turnaround - wait) */
    task->run_time_us = task->turnaround_time_us - task->wait_time_us;
}

void telemetry_record_preempt(sched_telemetry_t *telem,
                               uint16_t task_id,
                               uint8_t cpu_id)
{
    if (telem == NULL || task_id >= DAG_MAX_TASKS || cpu_id >= MAX_CPUS) {
        return;
    }

    telem->tasks[task_id].preemptions++;
}

void telemetry_record_migrate(sched_telemetry_t *telem,
                               uint16_t task_id,
                               uint8_t from_cpu,
                               uint8_t to_cpu)
{
    if (telem == NULL || task_id >= DAG_MAX_TASKS) {
        return;
    }

    telem->tasks[task_id].migrations++;
    telem->total_migrations++;
}

void telemetry_record_context_switch(sched_telemetry_t *telem,
                                      uint8_t cpu_id)
{
    if (telem == NULL || cpu_id >= MAX_CPUS) {
        return;
    }

    telem->cpus[cpu_id].context_switches++;
    telem->total_context_switches++;
}

/*******************************************************************************
 * METRIC COMPUTATION
 ******************************************************************************/

void telemetry_update(sched_telemetry_t *telem, uint64_t now_us)
{
    if (telem == NULL) {
        return;
    }

    telem->last_update_us = now_us;

    /* Update computed metrics */
    telem->avg_latency_ms = telemetry_compute_avg_latency(telem);
    telem->throughput = telemetry_compute_throughput(telem);
    telem->fairness_index = (double)telemetry_compute_fairness(telem) / 65536.0;

    /* Update CPU utilizations */
    for (uint8_t i = 0; i < telem->num_cpus; i++) {
        telem->cpus[i].utilization = telemetry_compute_cpu_utilization(telem, i);
    }
}

/**
 * Compute Jain's fairness index
 *
 * FI = (Σ x_i)² / (n × Σ x_i²)
 */
q16_t telemetry_compute_fairness(const sched_telemetry_t *telem)
{
    if (telem == NULL || telem->num_tasks == 0) {
        return Q16(1.0); /* Perfect fairness by default */
    }

    uint64_t sum = 0;
    uint64_t sum_squared = 0;
    uint32_t count = 0;

    for (uint16_t i = 0; i < telem->num_tasks; i++) {
        uint64_t run_time = telem->tasks[i].run_time_us;

        if (run_time > 0) {
            sum += run_time;
            sum_squared += (run_time * run_time) / 1000000; /* Scale to prevent overflow */
            count++;
        }
    }

    if (count == 0 || sum_squared == 0) {
        return Q16(1.0);
    }

    /* FI = sum² / (count × sum_squared) */
    double fi = ((double)sum * sum) / ((double)count * sum_squared * 1000000.0);

    /* Clamp to [0, 1] */
    if (fi > 1.0) fi = 1.0;
    if (fi < 0.0) fi = 0.0;

    return Q16(fi);
}

double telemetry_compute_avg_latency(const sched_telemetry_t *telem)
{
    if (telem == NULL || telem->total_tasks_completed == 0) {
        return 0.0;
    }

    uint64_t total_latency_us = 0;

    for (uint16_t i = 0; i < telem->num_tasks; i++) {
        if (telem->tasks[i].complete_time_us > 0) {
            total_latency_us += telem->tasks[i].turnaround_time_us;
        }
    }

    return (double)total_latency_us / (telem->total_tasks_completed * 1000.0);
}

double telemetry_compute_throughput(const sched_telemetry_t *telem)
{
    if (telem == NULL || telem->start_time_us == 0) {
        return 0.0;
    }

    uint64_t elapsed_us = telem->last_update_us - telem->start_time_us;

    if (elapsed_us == 0) {
        return 0.0;
    }

    /* Tasks per second = completed / (elapsed_us / 1000000) */
    return (double)telem->total_tasks_completed * 1000000.0 / elapsed_us;
}

q16_t telemetry_compute_cpu_utilization(const sched_telemetry_t *telem,
                                        uint8_t cpu_id)
{
    if (telem == NULL || cpu_id >= telem->num_cpus) {
        return 0;
    }

    const cpu_telemetry_t *cpu = &telem->cpus[cpu_id];
    uint64_t total = cpu->busy_time_us + cpu->idle_time_us;

    if (total == 0) {
        return 0;
    }

    return ((cpu->busy_time_us << 16) / total);
}

q16_t telemetry_compute_avg_utilization(const sched_telemetry_t *telem)
{
    if (telem == NULL || telem->num_cpus == 0) {
        return 0;
    }

    uint64_t total_util = 0;

    for (uint8_t i = 0; i < telem->num_cpus; i++) {
        total_util += telemetry_compute_cpu_utilization(telem, i);
    }

    return (q16_t)(total_util / telem->num_cpus);
}

/*******************************************************************************
 * HISTOGRAM GENERATION
 ******************************************************************************/

void telemetry_generate_histogram(sched_telemetry_t *telem,
                                   uint64_t bucket_size_us)
{
    if (telem == NULL) {
        return;
    }

    telem->histogram_bucket_size_us = bucket_size_us;
    memset(telem->latency_histogram, 0, sizeof(telem->latency_histogram));

    /* Populate histogram */
    for (uint16_t i = 0; i < telem->num_tasks; i++) {
        if (telem->tasks[i].complete_time_us > 0) {
            uint64_t latency = telem->tasks[i].turnaround_time_us;
            uint32_t bucket = (uint32_t)(latency / bucket_size_us);

            if (bucket >= TELEMETRY_MAX_HISTOGRAM_BUCKETS) {
                bucket = TELEMETRY_MAX_HISTOGRAM_BUCKETS - 1;
            }

            telem->latency_histogram[bucket]++;
        }
    }
}

uint32_t telemetry_get_histogram_bucket(const sched_telemetry_t *telem,
                                         uint32_t bucket)
{
    if (telem == NULL || bucket >= TELEMETRY_MAX_HISTOGRAM_BUCKETS) {
        return 0;
    }

    return telem->latency_histogram[bucket];
}

/*******************************************************************************
 * DISPLAY & REPORTING
 ******************************************************************************/

void telemetry_print_dashboard(const sched_telemetry_t *telem)
{
    if (telem == NULL) {
        return;
    }

    printf("\n");
    printf("╔═══════════════════════════════════════════════════════════╗\n");
    printf("║          PDAC SCHEDULER TELEMETRY DASHBOARD               ║\n");
    printf("╠═══════════════════════════════════════════════════════════╣\n");
    printf("║  Throughput:         %8.1f tasks/sec                  ║\n", telem->throughput);
    printf("║  Avg Latency:        %8.2f ms                         ║\n", telem->avg_latency_ms);
    printf("║  Fairness Index:     %8.3f (1.0 = perfect)            ║\n", telem->fairness_index);
    printf("║  Tasks Completed:    %8llu                            ║\n", telem->total_tasks_completed);
    printf("║  Context Switches:   %8llu                            ║\n", telem->total_context_switches);
    printf("║  Task Migrations:    %8llu                            ║\n", telem->total_migrations);

    q16_t avg_util = telemetry_compute_avg_utilization(telem);
    printf("║  Avg CPU Util:       %8.1f%%                          ║\n",
           (double)avg_util * 100.0 / 65536.0);

    printf("╚═══════════════════════════════════════════════════════════╝\n");
    printf("\n");
}

void telemetry_print_task_stats(const sched_telemetry_t *telem)
{
    if (telem == NULL) {
        return;
    }

    printf("\n=== Per-Task Statistics ===\n");
    printf("%-6s %-12s %-12s %-12s %-10s %-10s\n",
           "TaskID", "Wait(ms)", "Run(ms)", "Turnaround", "Preempt", "Migrate");
    printf("----------------------------------------------------------------\n");

    for (uint16_t i = 0; i < telem->num_tasks; i++) {
        const task_telemetry_t *task = &telem->tasks[i];

        if (task->complete_time_us > 0) {
            printf("%-6u %-12.2f %-12.2f %-12.2f %-10u %-10u\n",
                   i,
                   task->wait_time_us / 1000.0,
                   task->run_time_us / 1000.0,
                   task->turnaround_time_us / 1000.0,
                   task->preemptions,
                   task->migrations);
        }
    }

    printf("\n");
}

void telemetry_print_cpu_stats(const sched_telemetry_t *telem)
{
    if (telem == NULL) {
        return;
    }

    printf("\n=== Per-CPU Statistics ===\n");
    printf("%-6s %-12s %-12s %-12s %-12s\n",
           "CPU", "Busy(ms)", "Idle(ms)", "Util(%)", "CtxSw");
    printf("----------------------------------------------------------------\n");

    for (uint8_t i = 0; i < telem->num_cpus; i++) {
        const cpu_telemetry_t *cpu = &telem->cpus[i];
        q16_t util = telemetry_compute_cpu_utilization(telem, i);

        printf("%-6u %-12.2f %-12.2f %-12.1f %-12llu\n",
               i,
               cpu->busy_time_us / 1000.0,
               cpu->idle_time_us / 1000.0,
               (double)util * 100.0 / 65536.0,
               cpu->context_switches);
    }

    printf("\n");
}

void telemetry_print_histogram(const sched_telemetry_t *telem)
{
    if (telem == NULL) {
        return;
    }

    printf("\n=== Latency Histogram ===\n");
    printf("Bucket size: %.2f ms\n\n", telem->histogram_bucket_size_us / 1000.0);

    /* Find max count for scaling */
    uint32_t max_count = 0;
    for (int i = 0; i < TELEMETRY_MAX_HISTOGRAM_BUCKETS; i++) {
        if (telem->latency_histogram[i] > max_count) {
            max_count = telem->latency_histogram[i];
        }
    }

    if (max_count == 0) {
        printf("No data\n");
        return;
    }

    /* Print histogram bars */
    for (int i = 0; i < TELEMETRY_MAX_HISTOGRAM_BUCKETS; i++) {
        uint32_t count = telem->latency_histogram[i];

        if (count == 0) continue;

        double range_start = i * telem->histogram_bucket_size_us / 1000.0;
        double range_end = (i + 1) * telem->histogram_bucket_size_us / 1000.0;

        printf("[%6.1f-%6.1f ms]: ", range_start, range_end);

        /* Print bar (scaled to 50 characters max) */
        int bar_len = (count * 50) / max_count;
        for (int j = 0; j < bar_len; j++) {
            printf("█");
        }
        printf(" %u\n", count);
    }

    printf("\n");
}

void telemetry_print_summary(const sched_telemetry_t *telem)
{
    if (telem == NULL) {
        return;
    }

    telemetry_print_dashboard(telem);
    telemetry_print_cpu_stats(telem);
    telemetry_print_task_stats(telem);
    telemetry_print_histogram(telem);
}

/*******************************************************************************
 * INTEGRATION HELPERS
 ******************************************************************************/

void telemetry_collect_from_dispatcher(sched_telemetry_t *telem,
                                        const multicore_dispatcher_t *dispatch,
                                        uint64_t now_us)
{
    if (telem == NULL || dispatch == NULL) {
        return;
    }

    /* Collect per-CPU statistics */
    for (uint8_t i = 0; i < dispatch->num_cpus; i++) {
        const percpu_scheduler_t *cpu = &dispatch->cpus[i];

        telem->cpus[i].busy_time_us = cpu->total_busy_time_us;
        telem->cpus[i].idle_time_us = cpu->total_idle_time_us;
        telem->cpus[i].tasks_executed = cpu->total_tasks_run;
    }

    /* Update global statistics */
    telem->total_tasks_completed = dispatch->total_tasks_completed;
    telem->total_context_switches = dispatch->total_context_switches;
    telem->total_migrations = dispatch->total_migrations;

    /* Recompute metrics */
    telemetry_update(telem, now_us);
}

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

void example_telemetry_fairness(void)
{
    printf("\n=== Example: Fairness Analysis ===\n");
    printf("Comparing fair vs. unfair task distributions\n\n");

    /* Fair distribution: 3 tasks with equal CPU time */
    sched_telemetry_t telem_fair;
    telemetry_init(&telem_fair, 1);
    telemetry_start(&telem_fair, 0);

    for (int i = 0; i < 3; i++) {
        telemetry_record_submit(&telem_fair, i, 0);
        telemetry_record_start(&telem_fair, i, 0, 1000 * i);
        telemetry_record_complete(&telem_fair, i, 1000 * i + 100000); /* Each gets 100ms */
    }

    q16_t fi_fair = telemetry_compute_fairness(&telem_fair);
    printf("Fair distribution (100ms each):\n");
    printf("  Fairness Index: %.3f\n\n", (double)fi_fair / 65536.0);

    /* Unfair distribution: One task dominates */
    sched_telemetry_t telem_unfair;
    telemetry_init(&telem_unfair, 1);
    telemetry_start(&telem_unfair, 0);

    uint64_t runtimes[] = {200000, 50000, 50000}; /* 200ms, 50ms, 50ms */
    for (int i = 0; i < 3; i++) {
        telemetry_record_submit(&telem_unfair, i, 0);
        telemetry_record_start(&telem_unfair, i, 0, 1000 * i);
        telemetry_record_complete(&telem_unfair, i, 1000 * i + runtimes[i]);
    }

    q16_t fi_unfair = telemetry_compute_fairness(&telem_unfair);
    printf("Unfair distribution (200ms, 50ms, 50ms):\n");
    printf("  Fairness Index: %.3f\n\n", (double)fi_unfair / 65536.0);

    printf("Expected: Fair > 0.9, Unfair < 0.8\n");
    printf("===================================\n\n");
}

void example_telemetry_histogram(void)
{
    printf("\n=== Example: Latency Histogram ===\n");
    printf("Demonstrating histogram generation\n\n");

    sched_telemetry_t telem;
    telemetry_init(&telem, 1);
    telemetry_start(&telem, 0);

    /* Simulate 20 tasks with varying latencies */
    uint64_t latencies_us[] = {
        5000, 8000, 12000, 15000, 18000,    /* 5-18ms */
        22000, 25000, 28000, 32000, 35000,  /* 22-35ms */
        40000, 45000, 50000, 55000, 60000,  /* 40-60ms */
        70000, 80000, 90000, 100000, 120000 /* 70-120ms */
    };

    for (int i = 0; i < 20; i++) {
        telemetry_record_submit(&telem, i, 0);
        telemetry_record_start(&telem, i, 0, 1000);
        telemetry_record_complete(&telem, i, 1000 + latencies_us[i]);
    }

    /* Generate histogram with 10ms buckets */
    telemetry_generate_histogram(&telem, 10000);
    telemetry_print_histogram(&telem);

    printf("===================================\n\n");
}

void example_telemetry_utilization(void)
{
    printf("\n=== Example: CPU Utilization Tracking ===\n");
    printf("Simulating CPU busy/idle periods\n\n");

    sched_telemetry_t telem;
    telemetry_init(&telem, 4); /* 4 CPUs */
    telemetry_start(&telem, 0);

    /* Simulate different CPU loads */
    telem.cpus[0].busy_time_us = 90000000;  /* 90s busy */
    telem.cpus[0].idle_time_us = 10000000;  /* 10s idle → 90% util */

    telem.cpus[1].busy_time_us = 75000000;  /* 75s busy */
    telem.cpus[1].idle_time_us = 25000000;  /* 25s idle → 75% util */

    telem.cpus[2].busy_time_us = 50000000;  /* 50s busy */
    telem.cpus[2].idle_time_us = 50000000;  /* 50s idle → 50% util */

    telem.cpus[3].busy_time_us = 20000000;  /* 20s busy */
    telem.cpus[3].idle_time_us = 80000000;  /* 80s idle → 20% util */

    telemetry_print_cpu_stats(&telem);

    q16_t avg_util = telemetry_compute_avg_utilization(&telem);
    printf("Average utilization: %.1f%% (expected: 58.75%%)\n",
           (double)avg_util * 100.0 / 65536.0);

    printf("===================================\n\n");
}

/**
 * Run all telemetry examples
 */
void telemetry_run_all_examples(void)
{
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   SCHEDULER TELEMETRY - EXAMPLES                           ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n");

    example_telemetry_fairness();
    example_telemetry_histogram();
    example_telemetry_utilization();

    printf("All telemetry examples completed.\n");
    printf("See include/sched_telemetry.h for API documentation.\n\n");
}
