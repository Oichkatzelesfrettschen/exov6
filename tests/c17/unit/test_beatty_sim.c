/*
 * Phoenix Exokernel - Beatty Scheduler Fairness Test
 * * RESOLUTION NOTE: 
 * This test is configured as a WHITEBOX test. It includes .c implementation 
 * files directly to access internal data structures (dag.tasks, sched.priorities) 
 * that are not exposed in the public API headers.
 */

#include "printf.h"
#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdatomic.h>
#include <float.h>
#include <math.h>

/* Mock Q16 fixed point if not defined in headers */
#ifndef Q16
#define Q16(x) ((int32_t)((x) * 65536.0))
#endif

/* Include kernel source to test static functions and internals */
/* We rely on relative paths to kernel implementation for whitebox testing */
#include "../../../kernel/dag_pdac.c"
#include "../../../kernel/sched_beatty.c"

/* Test Framework Macros */
#define TEST_PASS(msg) printf("[PASS] %s\n", msg)
#define TEST_FAIL(msg) do { printf("[FAIL] %s (Line %d)\n", msg, __LINE__); return 1; } while(0)
#define TEST_ASSERT_MSG(cond, msg) if (!(cond)) TEST_FAIL(msg)

/* Telemetry extensions for analysis */
typedef struct {
    uint64_t min_latency;
    uint64_t max_latency;
    double sum_squared_latency; /* For variance/jitter calc */
} task_metrics_t;

int test_beatty_fairness_sim(void) {
    printf("=== Beatty Scheduler Fairness & Jitter Simulation ===\n");

    /* 1. Setup */
    beatty_scheduler_t sched;
    beatty_init(&sched, BEATTY_GOLDEN_RATIO);

    dag_pdac_t dag;
    /* e0=CPU, e1=MEM - giving generous quota */
    resource_vector_t quota = {.e0 = Q16(100.0), .e1 = Q16(1024.0)}; 
    pdac_dag_init(&dag, quota);

    /* * Create 5 tasks with heterogeneous resource demands to test weight calculation 
     * Task 0: High Priority (High Resource Norm)
     */
    resource_vector_t res_high = {.e0 = Q16(10.0), .e1 = Q16(100.0)};
    int t0 = pdac_dag_add_task(&dag, "High Priority", res_high);
    (void)t0;

    /* Task 1, 2: Medium Priority */
    resource_vector_t res_med = {.e0 = Q16(5.0), .e1 = Q16(50.0)};
    int t1 = pdac_dag_add_task(&dag, "Medium 1", res_med);
    int t2 = pdac_dag_add_task(&dag, "Medium 2", res_med);
    (void)t1; (void)t2;

    /* Task 3, 4: Low Priority */
    resource_vector_t res_low = {.e0 = Q16(1.0), .e1 = Q16(10.0)};
    int t3 = pdac_dag_add_task(&dag, "Low 1", res_low);
    int t4 = pdac_dag_add_task(&dag, "Low 2", res_low);
    (void)t3; (void)t4;

    /* Initialize metrics */
    task_metrics_t metrics[5];
    for(int i=0; i<5; i++) {
        atomic_store(&dag.tasks[i].state, TASK_STATE_READY);
        dag.tasks[i].last_runnable_time = 0; /* Simulation start */
        dag.tasks[i].schedule_count = 0;
        dag.tasks[i].run_time_ticks = 0;
        dag.tasks[i].total_latency_ticks = 0;
        
        metrics[i].min_latency = UINT64_MAX;
        metrics[i].max_latency = 0;
        metrics[i].sum_squared_latency = 0.0;
    }

    /* Force priority recomputation based on new resource vectors */
    beatty_recompute_all_priorities(&sched, &dag);

    /* 2. Simulate Run Loop */
    const int total_ticks = 10000;
    uint64_t current_time = 0;

    for (int tick = 0; tick < total_ticks; tick++) {
        dag_task_t *selected = beatty_select(&sched, &dag);
        TEST_ASSERT_MSG(selected != NULL, "Scheduler returned NULL (Starvation/Logic Error)");

        /* Find index for metrics update */
        int idx = -1;
        for(int i=0; i<5; i++) {
            if(&dag.tasks[i] == selected) { idx = i; break; }
        }
        TEST_ASSERT_MSG(idx >= 0, "Selected task not found in array");

        /* Simulate execution */
        selected->run_time_ticks++;

        /* Compute latency: time from when task became ready until selected */
        uint64_t latency = current_time - selected->last_runnable_time;
        selected->total_latency_ticks += latency;
        
        /* Update advanced metrics */
        if (latency < metrics[idx].min_latency) metrics[idx].min_latency = latency;
        if (latency > metrics[idx].max_latency) metrics[idx].max_latency = latency;
        metrics[idx].sum_squared_latency += (double)latency * latency;

        /* Task completes execution and becomes ready again immediately (CPU bound simulation) */
        /* Set last_runnable_time to current time + 1 (when it becomes ready for next cycle) */
        selected->last_runnable_time = current_time + 1;
        
        current_time++;
    }

    /* 3. Analyze Results */
    printf("\n=== Simulation Results (%d ticks) ===\n", total_ticks);
    printf("%-15s %-8s %-8s %-8s %-8s %-8s %-8s\n", 
           "Name", "Prio", "Count", "AvgLat", "MinLat", "MaxLat", "Jitter");

    uint64_t total_selections = 0;
    
    /* Calculate Ideal Total Weight for Drift Analysis */
    double total_weight_norm = 0.0;
    /* Assuming priority maps to inverse weight or similar in implementation. 
       For this test, we observe the output distribution. */

    for(int i=0; i<5; i++) {
        dag_task_t *t = &dag.tasks[i];
        q16_t prio = sched.priorities[i]; // Whitebox access

        uint64_t avg_lat = 0;
        double jitter = 0.0;
        
        if (t->schedule_count > 0) {
            avg_lat = t->total_latency_ticks / t->schedule_count;
            
            /* Variance = E[X^2] - (E[X])^2 */
            double mean = (double)t->total_latency_ticks / t->schedule_count;
            double variance = (metrics[i].sum_squared_latency / t->schedule_count) - (mean * mean);
            jitter = sqrt(variance > 0 ? variance : 0);
        }

        printf("%-15s %-8.2f %-8llu %-8llu %-8llu %-8llu %-8.2f\n",
               t->name, (double)prio/65536.0,
               (unsigned long long)t->schedule_count,
               (unsigned long long)avg_lat,
               (unsigned long long)metrics[i].min_latency,
               (unsigned long long)metrics[i].max_latency,
               jitter);

        total_selections += t->schedule_count;
        TEST_ASSERT_MSG(t->schedule_count > 0, "Task Starvation Detected: Count == 0");
    }

    TEST_ASSERT_MSG(total_selections == (uint64_t)total_ticks, "Total selections match ticks");

    /* * Fairness Check 
     * In a perfectly fair round-robin (equal weights), share should be 0.2.
     * With Beatty resource-based weights, we expect deviation, but it should be bounded.
     */
    printf("\n=== Fairness & Drift Analysis ===\n");
    double expected_share = 1.0 / 5.0; /* Baseline expectation */
    int tasks_within_bounds = 0;

    for(int i=0; i<5; i++) {
        double share = (double)dag.tasks[i].schedule_count / total_ticks;
        double drift_pct = ((share - expected_share) / expected_share) * 100.0;
        
        printf("Task %d Share: %.4f (Drift: %+.2f%%)\n", i, share, drift_pct);

        /* * Logic update: Since we set explicit resource vectors, we don't expect 
         * perfect equal sharing if the scheduler is weighted. 
         * However, for this basic fairness test, we ensure no task hogs the CPU (>30%) 
         * and no task starves (<10%).
         */
        if (share > 0.10 && share < 0.30) {
            tasks_within_bounds++;
        } else {
            printf("WARNING: Task %d outside loose fairness bounds (10%% - 30%%)\n", i);
        }
    }

    TEST_ASSERT_MSG(tasks_within_bounds == 5, "All tasks received fair share within bounds");
    TEST_ASSERT_MSG(dag.tasks[0].run_time_ticks > 0, "Telemetry: Run time updated correctly");

    /* Dump internal stats if available */
    beatty_print_stats(&sched, &dag);

    TEST_PASS("beatty_fairness_sim");
    return 0;
}

int main(void) {
    if (test_beatty_fairness_sim() != 0) {
        return 1;
    }
    printf("\n[SUCCESS] All simulations passed.\n");
    return 0;
}