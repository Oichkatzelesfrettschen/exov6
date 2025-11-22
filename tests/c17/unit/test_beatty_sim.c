#include "printf.h"
#include <assert.h>
#include <stdlib.h>
#include <string.h>

/* Include kernel source to test static functions and internals */
/* We need to ensure include paths are set correctly in CMake */
#include "../../../kernel/sched_beatty.c"

/* Simple test framework */
#define TEST_PASS(msg) printf("PASS: %s\n", msg)
#define TEST_FAIL(msg) do { printf("FAIL: %s\n", msg); return 1; } while(0)
#define TEST_ASSERT_MSG(cond, msg) if (!(cond)) TEST_FAIL(msg)

int test_beatty_fairness_sim(void) {
    printf("=== Beatty Scheduler Fairness Simulation ===\n");

    /* 1. Setup */
    beatty_scheduler_t sched;
    beatty_init(&sched, BEATTY_GOLDEN_RATIO);

    dag_pdac_t dag;
    resource_vector_t quota = {.e0 = Q16(100.0), .e1 = Q16(1024.0)}; /* e0=CPU, e1=MEM */
    pdac_dag_init(&dag, quota);

    /* Create 5 tasks with different priorities via resource usage */
    /* Task 0: High Priority (High Resource Norm) */
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

    /* Make all ready */
    for(int i=0; i<dag.num_tasks; i++) {
        dag.tasks[i].state = TASK_STATE_READY;
        dag.tasks[i].last_runnable_time = 0; /* Simulation start */
        dag.tasks[i].schedule_count = 0;
        dag.tasks[i].run_time_ticks = 0;
        dag.tasks[i].total_latency_ticks = 0;
    }

    beatty_recompute_all_priorities(&sched, &dag);

    /* 2. Simulate Run Loop */
    int total_ticks = 10000;

    /* Current time tracking if needed, though we just increment ticks */
    // uint64_t current_time = 0;

    for (int tick = 0; tick < total_ticks; tick++) {
        dag_task_t *selected = beatty_select(&sched, &dag);
        TEST_ASSERT_MSG(selected != NULL, "Should select a task");

        /* Simulate execution */
        selected->run_time_ticks++;

        /* Update Latency for ALL ready tasks */
        for(int i=0; i<dag.num_tasks; i++) {
            dag_task_t *t = &dag.tasks[i];
            if (t->state == TASK_STATE_READY) {
                if (t != selected) {
                    /* Task was ready but not selected -> Latency increases */
                     t->total_latency_ticks++;
                }
            }
        }
        // current_time++;
    }

    /* 3. Analyze Results */
    printf("\nResults after %d ticks:\n", total_ticks);
    printf("%-15s %-10s %-10s %-10s %-10s\n", "Name", "Priority", "Count", "RunTime", "AvgLat");

    uint64_t total_selections = 0;
    for(int i=0; i<dag.num_tasks; i++) {
        dag_task_t *t = &dag.tasks[i];
        q16_t prio = sched.priorities[i];

        uint64_t avg_lat = 0;
        if (t->schedule_count > 0)
             avg_lat = t->total_latency_ticks / t->schedule_count;

        printf("%-15s %-10.2f %-10llu %-10llu %-10llu\n",
               t->name, (double)prio/65536.0,
               (unsigned long long)t->schedule_count,
               (unsigned long long)t->run_time_ticks,
               (unsigned long long)avg_lat);

        total_selections += t->schedule_count;

        /* Basic sanity check: Task ran */
        TEST_ASSERT_MSG(t->schedule_count > 0, "Task should have run");
    }

    TEST_ASSERT_MSG(total_selections == (uint64_t)total_ticks, "Total selections match ticks");

    /* Fairness Check */
    double expected_share = 1.0 / (double)dag.num_tasks;
    for(int i=0; i<dag.num_tasks; i++) {
        double share = (double)dag.tasks[i].schedule_count / total_ticks;
        printf("Task %d Share: %.4f (Expected %.4f)\n", i, share, expected_share);

        if (share < 0.18 || share > 0.22) {
            printf("WARNING: Share deviation larger than expected for task %d\n", i);
        }
    }

    TEST_ASSERT_MSG(dag.tasks[0].run_time_ticks > 0, "Telemetry: Run time updated");

    beatty_print_stats(&sched, &dag);

    TEST_PASS("beatty_fairness_sim");
    return 0;
}

int main(void) {
    if (test_beatty_fairness_sim() != 0) {
        return 1;
    }
    printf("\nAll simulations passed.\n");
    return 0;
}
