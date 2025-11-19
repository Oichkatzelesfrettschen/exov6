#pragma once

/**
 * @file sched_telemetry.h
 * @brief Performance Telemetry and Monitoring for PDAC Scheduler
 *
 * PEDAGOGICAL PURPOSE:
 * ====================
 * Demonstrates how to measure and analyze scheduler performance using
 * real-time metrics, fairness indices, and statistical analysis.
 *
 * KEY METRICS:
 * ============
 * **Latency**: Time from task submission to completion (turnaround time)
 * **Throughput**: Tasks completed per second
 * **Fairness**: Jain's fairness index (1.0 = perfect fairness)
 * **Utilization**: Percentage of time CPUs are busy
 * **Overhead**: Time spent in scheduler vs. running tasks
 *
 * JAIN'S FAIRNESS INDEX:
 * ======================
 * Formula: FI = (Σ x_i)² / (n × Σ x_i²)
 *
 * Where x_i = CPU time for task i
 *
 * Interpretation:
 * - FI = 1.0: Perfect fairness (all tasks get equal CPU time)
 * - FI = 1/n: Worst fairness (one task gets all CPU time)
 * - FI > 0.9: Good fairness
 * - FI < 0.7: Poor fairness
 *
 * Example:
 * Tasks: A=100ms, B=100ms, C=100ms → FI = (300)²/(3×30000) = 1.0 ✓
 * Tasks: A=200ms, B=50ms, C=50ms  → FI = (300)²/(3×50000) = 0.6 ✗
 *
 * REAL-WORLD ANALOGUES:
 * =====================
 * - Linux: perf, ftrace, /proc/schedstat
 * - FreeBSD: DTrace scheduler probes
 * - Xen: xenmon, xentop
 * - Windows: Performance Monitor, ETW
 */

#include "types.h"
#include "dag_pdac.h"
#include "percpu_sched.h"

/*******************************************************************************
 * CONFIGURATION
 ******************************************************************************/

/**
 * Maximum histogram buckets for latency distribution
 */
#define TELEMETRY_MAX_HISTOGRAM_BUCKETS 16

/**
 * Sampling interval for CPU utilization (microseconds)
 */
#define TELEMETRY_SAMPLE_INTERVAL_US 1000000  /* 1 second */

/*******************************************************************************
 * TELEMETRY DATA STRUCTURES
 ******************************************************************************/

/**
 * Per-task telemetry metrics
 */
typedef struct task_telemetry {
    /* Timing */
    uint64_t submit_time_us;        /* When task was submitted */
    uint64_t start_time_us;         /* When task first ran */
    uint64_t complete_time_us;      /* When task completed */

    /* Computed metrics */
    uint64_t wait_time_us;          /* Time spent waiting (READY) */
    uint64_t run_time_us;           /* Time spent running */
    uint64_t turnaround_time_us;    /* submit → complete */

    /* Events */
    uint32_t preemptions;           /* Times preempted */
    uint32_t migrations;            /* Times migrated between CPUs */
} task_telemetry_t;

/**
 * Per-CPU telemetry metrics
 */
typedef struct cpu_telemetry {
    /* Time accounting */
    uint64_t busy_time_us;          /* Time spent executing tasks */
    uint64_t idle_time_us;          /* Time spent idle */
    uint64_t scheduler_time_us;     /* Time in scheduler code */

    /* Task accounting */
    uint64_t tasks_executed;        /* Total tasks run */
    uint64_t context_switches;      /* Total context switches */

    /* Computed metrics */
    q16_t utilization;              /* busy / (busy + idle) */
    q16_t scheduler_overhead;       /* scheduler / (busy + scheduler) */
} cpu_telemetry_t;

/**
 * Global scheduler telemetry
 */
typedef struct sched_telemetry {
    /* Per-task metrics */
    task_telemetry_t tasks[DAG_MAX_TASKS];
    uint16_t num_tasks;

    /* Per-CPU metrics */
    cpu_telemetry_t cpus[MAX_CPUS];
    uint8_t num_cpus;

    /* Global aggregates */
    uint64_t total_tasks_completed;  /* Tasks finished */
    uint64_t total_tasks_submitted;  /* Tasks submitted */
    uint64_t total_context_switches; /* All CPUs combined */
    uint64_t total_migrations;       /* Task migrations */

    /* Performance metrics */
    double avg_latency_ms;           /* Average turnaround time */
    double avg_wait_time_ms;         /* Average wait time */
    double throughput;               /* Tasks per second */
    double fairness_index;           /* Jain's fairness index */

    /* Histogram data */
    uint32_t latency_histogram[TELEMETRY_MAX_HISTOGRAM_BUCKETS];
    uint64_t histogram_bucket_size_us; /* Bucket size in microseconds */

    /* Timing */
    uint64_t start_time_us;          /* When telemetry started */
    uint64_t last_update_us;         /* Last telemetry update */
} sched_telemetry_t;

/*******************************************************************************
 * TELEMETRY LIFECYCLE
 ******************************************************************************/

/**
 * Initialize telemetry system
 *
 * @param telem    Telemetry state
 * @param num_cpus Number of CPUs to track
 */
void telemetry_init(sched_telemetry_t *telem, uint8_t num_cpus);

/**
 * Reset telemetry counters
 *
 * @param telem  Telemetry state
 */
void telemetry_reset(sched_telemetry_t *telem);

/**
 * Start telemetry collection
 *
 * @param telem   Telemetry state
 * @param now_us  Current time (microseconds)
 */
void telemetry_start(sched_telemetry_t *telem, uint64_t now_us);

/*******************************************************************************
 * EVENT RECORDING
 ******************************************************************************/

/**
 * Record task submission
 *
 * @param telem    Telemetry state
 * @param task_id  Task identifier
 * @param now_us   Current time (microseconds)
 */
void telemetry_record_submit(sched_telemetry_t *telem,
                              uint16_t task_id,
                              uint64_t now_us);

/**
 * Record task start (first execution)
 *
 * @param telem    Telemetry state
 * @param task_id  Task identifier
 * @param cpu_id   CPU executing task
 * @param now_us   Current time (microseconds)
 */
void telemetry_record_start(sched_telemetry_t *telem,
                             uint16_t task_id,
                             uint8_t cpu_id,
                             uint64_t now_us);

/**
 * Record task completion
 *
 * @param telem    Telemetry state
 * @param task_id  Task identifier
 * @param now_us   Current time (microseconds)
 */
void telemetry_record_complete(sched_telemetry_t *telem,
                                uint16_t task_id,
                                uint64_t now_us);

/**
 * Record task preemption
 *
 * @param telem    Telemetry state
 * @param task_id  Task identifier
 * @param cpu_id   CPU that preempted
 */
void telemetry_record_preempt(sched_telemetry_t *telem,
                               uint16_t task_id,
                               uint8_t cpu_id);

/**
 * Record task migration
 *
 * @param telem     Telemetry state
 * @param task_id   Task identifier
 * @param from_cpu  Source CPU
 * @param to_cpu    Destination CPU
 */
void telemetry_record_migrate(sched_telemetry_t *telem,
                               uint16_t task_id,
                               uint8_t from_cpu,
                               uint8_t to_cpu);

/**
 * Record context switch
 *
 * @param telem   Telemetry state
 * @param cpu_id  CPU performing switch
 */
void telemetry_record_context_switch(sched_telemetry_t *telem,
                                      uint8_t cpu_id);

/*******************************************************************************
 * METRIC COMPUTATION
 ******************************************************************************/

/**
 * Update all computed metrics
 *
 * Call periodically to recompute averages, fairness, etc.
 *
 * @param telem   Telemetry state
 * @param now_us  Current time (microseconds)
 */
void telemetry_update(sched_telemetry_t *telem, uint64_t now_us);

/**
 * Compute Jain's fairness index
 *
 * FI = (Σ x_i)² / (n × Σ x_i²)
 *
 * @param telem  Telemetry state
 * @return       Fairness index (0.0 to 1.0, Q16 fixed-point)
 */
q16_t telemetry_compute_fairness(const sched_telemetry_t *telem);

/**
 * Compute average task latency (turnaround time)
 *
 * @param telem  Telemetry state
 * @return       Average latency (milliseconds)
 */
double telemetry_compute_avg_latency(const sched_telemetry_t *telem);

/**
 * Compute throughput (tasks per second)
 *
 * @param telem  Telemetry state
 * @return       Throughput (tasks/second)
 */
double telemetry_compute_throughput(const sched_telemetry_t *telem);

/**
 * Compute CPU utilization for a specific CPU
 *
 * @param telem   Telemetry state
 * @param cpu_id  CPU identifier
 * @return        Utilization (0.0 to 1.0, Q16 fixed-point)
 */
q16_t telemetry_compute_cpu_utilization(const sched_telemetry_t *telem,
                                        uint8_t cpu_id);

/**
 * Compute average CPU utilization across all CPUs
 *
 * @param telem  Telemetry state
 * @return       Average utilization (0.0 to 1.0, Q16 fixed-point)
 */
q16_t telemetry_compute_avg_utilization(const sched_telemetry_t *telem);

/*******************************************************************************
 * HISTOGRAM GENERATION
 ******************************************************************************/

/**
 * Generate latency histogram
 *
 * Creates histogram with logarithmic buckets:
 * Bucket 0: [0, bucket_size)
 * Bucket 1: [bucket_size, 2*bucket_size)
 * ...
 *
 * @param telem           Telemetry state
 * @param bucket_size_us  Bucket size (microseconds)
 */
void telemetry_generate_histogram(sched_telemetry_t *telem,
                                   uint64_t bucket_size_us);

/**
 * Get histogram bucket count
 *
 * @param telem     Telemetry state
 * @param bucket    Bucket index
 * @return          Number of samples in bucket
 */
uint32_t telemetry_get_histogram_bucket(const sched_telemetry_t *telem,
                                         uint32_t bucket);

/*******************************************************************************
 * DISPLAY & REPORTING
 ******************************************************************************/

/**
 * Print telemetry dashboard
 *
 * Shows real-time metrics in formatted table.
 *
 * @param telem  Telemetry state
 */
void telemetry_print_dashboard(const sched_telemetry_t *telem);

/**
 * Print per-task statistics
 *
 * @param telem  Telemetry state
 */
void telemetry_print_task_stats(const sched_telemetry_t *telem);

/**
 * Print per-CPU statistics
 *
 * @param telem  Telemetry state
 */
void telemetry_print_cpu_stats(const sched_telemetry_t *telem);

/**
 * Print latency histogram
 *
 * @param telem  Telemetry state
 */
void telemetry_print_histogram(const sched_telemetry_t *telem);

/**
 * Print summary report
 *
 * Includes all metrics in comprehensive report.
 *
 * @param telem  Telemetry state
 */
void telemetry_print_summary(const sched_telemetry_t *telem);

/*******************************************************************************
 * INTEGRATION HELPERS
 ******************************************************************************/

/**
 * Collect telemetry from multi-core dispatcher
 *
 * @param telem     Telemetry state
 * @param dispatch  Multi-core dispatcher
 * @param now_us    Current time (microseconds)
 */
void telemetry_collect_from_dispatcher(sched_telemetry_t *telem,
                                        const multicore_dispatcher_t *dispatch,
                                        uint64_t now_us);

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Fairness analysis
 */
void example_telemetry_fairness(void);

/**
 * Example: Latency histogram
 */
void example_telemetry_histogram(void);

/**
 * Example: CPU utilization tracking
 */
void example_telemetry_utilization(void);
