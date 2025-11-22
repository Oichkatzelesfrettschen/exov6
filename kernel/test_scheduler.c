/**
 * @file test_scheduler.c
 * @brief Unit Tests and Benchmarks for PDAC Phase 3 Scheduler
 *
 * Tests all scheduler components:
 * - Linear Congruential Generator (LCG)
 * - Lottery scheduler
 * - Beatty sequence scheduler
 * - Hybrid scheduler
 * - Stochastic admission control
 *
 * @see docs/PDAC_PHASE3_PLAN.md for implementation details
 */

#include "lcg.h"
#include "sched_lottery.h"
#include "sched_beatty.h"
#include "sched_hybrid.h"
#include "sched_admission.h"
#include "dag_pdac.h"
#include "printf.h"
#include <stdint.h>
#include <string.h>

/*******************************************************************************
 * TEST FRAMEWORK
 ******************************************************************************/

static int g_tests_run = 0;
static int g_tests_passed = 0;
static int g_tests_failed = 0;

#define TEST_ASSERT(condition, message) \
    do { \
        if (!(condition)) { \
            printf("  FAIL: %s\n", message); \
            return -1; \
        } \
    } while (0)

#define TEST_ASSERT_EQ(actual, expected, message) \
    do { \
        if ((actual) != (expected)) { \
            printf("  FAIL: %s (expected %d, got %d)\n", message, (int)(expected), (int)(actual)); \
            return -1; \
        } \
    } while (0)

#define TEST_ASSERT_RANGE(value, min, max, message) \
    do { \
        if ((value) < (min) || (value) > (max)) { \
            printf("  FAIL: %s (value %.2f not in range [%.2f, %.2f])\n", \
                   message, (double)(value), (double)(min), (double)(max)); \
            return -1; \
        } \
    } while (0)

#define RUN_TEST(test_func) \
    do { \
        printf("\n[TEST] %s\n", #test_func); \
        g_tests_run++; \
        if (test_func() == 0) { \
            printf("  PASS\n"); \
            g_tests_passed++; \
        } else { \
            g_tests_failed++; \
        } \
    } while (0)

/*******************************************************************************
 * LCG TESTS
 ******************************************************************************/

/**
 * Test: LCG initialization
 */
static int test_lcg_init(void)
{
    lcg_state_t state;
    lcg_init(&state, 42);

    TEST_ASSERT_EQ(state.x, 42, "Initial state should match seed");
    TEST_ASSERT_EQ(state.count, 0, "Count should start at 0");

    return 0;
}

/**
 * Test: LCG generates non-zero values
 */
static int test_lcg_nonzero(void)
{
    lcg_state_t state;
    lcg_init(&state, 1);

    uint32_t val1 = lcg_next(&state);
    TEST_ASSERT(val1 != 0, "First value should be non-zero");

    uint32_t val2 = lcg_next(&state);
    TEST_ASSERT(val2 != 0, "Second value should be non-zero");
    TEST_ASSERT(val1 != val2, "Values should differ");

    return 0;
}

/**
 * Test: LCG range function
 */
static int test_lcg_range(void)
{
    lcg_state_t state;
    lcg_init(&state, 12345);

    /* Generate 100 values in range [0, 10) */
    for (int i = 0; i < 100; i++) {
        uint32_t val = lcg_range(&state, 10);
        TEST_ASSERT(val < 10, "Value should be in range [0, 10)");
    }

    return 0;
}

/**
 * Test: LCG uniform distribution [0.0, 1.0)
 */
static int test_lcg_uniform(void)
{
    lcg_state_t state;
    lcg_init(&state, 99999);

    /* Generate 100 values */
    for (int i = 0; i < 100; i++) {
        double val = lcg_uniform(&state);
        TEST_ASSERT_RANGE(val, 0.0, 1.0, "Value should be in [0.0, 1.0)");
    }

    return 0;
}

/**
 * Test: LCG statistical uniformity (chi-squared test)
 */
static int test_lcg_chi_squared(void)
{
    lcg_state_t state;
    lcg_init(&state, 42);

    /* Chi-squared test with 10 buckets, 10000 samples */
    double chi2 = lcg_test_uniform(&state, 10, 10000);

    /* Critical value for 9 degrees of freedom at α=0.05: 16.92 */
    TEST_ASSERT(chi2 < 20.0, "Chi-squared value should indicate uniform distribution");

    return 0;
}

/*******************************************************************************
 * LOTTERY SCHEDULER TESTS
 ******************************************************************************/

/**
 * Test: Lottery scheduler initialization
 */
static int test_lottery_init(void)
{
    lcg_state_t rng;
    lcg_init(&rng, 42);

    lottery_scheduler_t sched;
    lottery_init(&sched, &rng);

    TEST_ASSERT(sched.rng == &rng, "RNG should be stored");
    TEST_ASSERT_EQ(sched.total_tickets, 0, "Total tickets should start at 0");

    return 0;
}

/**
 * Test: Lottery ticket computation
 */
static int test_lottery_tickets(void)
{
    lcg_state_t rng;
    lcg_init(&rng, 42);

    lottery_scheduler_t sched;
    lottery_init(&sched, &rng);

    /* Create task with known resource norm */
    dag_task_t task;
    task.resources.cpu = Q16(1.0);
    task.resources.memory = 0;
    /* Other fields zero */

    lottery_update_tickets(&sched, 0, &task);

    uint32_t tickets = lottery_get_tickets(&sched, 0);
    TEST_ASSERT(tickets >= LOTTERY_MIN_TICKETS, "Tickets should be >= MIN");
    TEST_ASSERT(tickets <= LOTTERY_MAX_TICKETS, "Tickets should be <= MAX");

    return 0;
}

/**
 * Test: Lottery selection returns ready task
 */
static int test_lottery_select(void)
{
    lcg_state_t rng;
    lcg_init(&rng, 12345);

    lottery_scheduler_t sched;
    lottery_init(&sched, &rng);

    /* Create DAG with 2 tasks */
    dag_pdac_t dag;
    resource_vector_t quota = {.cpu = Q16(4.0), .memory = Q16(1024.0)};
    pdac_dag_init(&dag, quota);

    resource_vector_t res = {.cpu = Q16(1.0), .memory = Q16(200.0)};
    int t0 = pdac_dag_add_task(&dag, "Task 0", res);
    int t1 = pdac_dag_add_task(&dag, "Task 1", res);

    dag.tasks[t0].state = TASK_STATE_READY;
    dag.tasks[t1].state = TASK_STATE_READY;

    lottery_recompute_all_tickets(&sched, &dag);

    /* Select a task */
    dag_task_t *selected = lottery_select(&sched, &dag);
    TEST_ASSERT(selected != NULL, "Should select a task");
    TEST_ASSERT(selected->state == TASK_STATE_READY, "Selected task should be READY");

    return 0;
}

/**
 * Test: Lottery fairness (proportional selection)
 */
static int test_lottery_fairness(void)
{
    lcg_state_t rng;
    lcg_init(&rng, 42);

    lottery_scheduler_t sched;
    lottery_init(&sched, &rng);

    /* Create DAG with 2 tasks: one with 2x resources */
    dag_pdac_t dag;
    resource_vector_t quota = {.cpu = Q16(6.0), .memory = Q16(1024.0)};
    pdac_dag_init(&dag, quota);

    resource_vector_t res1 = {.cpu = Q16(1.0), .memory = Q16(100.0)};
    resource_vector_t res2 = {.cpu = Q16(2.0), .memory = Q16(200.0)};

    int t0 = pdac_dag_add_task(&dag, "Task 0 (1x)", res1);
    int t1 = pdac_dag_add_task(&dag, "Task 1 (2x)", res2);

    dag.tasks[t0].state = TASK_STATE_READY;
    dag.tasks[t1].state = TASK_STATE_READY;

    lottery_recompute_all_tickets(&sched, &dag);

    /* Run lottery 1000 times */
    uint32_t count0 = 0, count1 = 0;
    for (int i = 0; i < 1000; i++) {
        dag_task_t *selected = lottery_select(&sched, &dag);
        if (selected->id == t0) count0++;
        if (selected->id == t1) count1++;
    }

    /* Task 1 should be selected ~2x as often (within tolerance) */
    double ratio = (double)count1 / count0;
    TEST_ASSERT_RANGE(ratio, 1.5, 2.5, "Selection ratio should be ~2.0");

    return 0;
}

/*******************************************************************************
 * BEATTY SCHEDULER TESTS
 ******************************************************************************/

/**
 * Test: Beatty scheduler initialization
 */
static int test_beatty_init(void)
{
    beatty_scheduler_t sched;
    beatty_init(&sched, BEATTY_GOLDEN_RATIO);

    TEST_ASSERT_EQ(sched.counter, 0, "Counter should start at 0");
    TEST_ASSERT_EQ(sched.alpha, BEATTY_GOLDEN_RATIO, "Alpha should be golden ratio");

    return 0;
}

/**
 * Test: Beatty sequence generation
 */
static int test_beatty_sequence(void)
{
    beatty_scheduler_t sched;
    beatty_init(&sched, BEATTY_GOLDEN_RATIO);

    /* Generate first 5 Beatty numbers: 1, 3, 4, 6, 8 */
    uint64_t expected[] = {0, 1, 3, 4, 6, 8};

    for (int i = 0; i <= 5; i++) {
        sched.counter = i;
        uint64_t beatty = beatty_compute_next(&sched);

        /* Allow some tolerance due to Q16 fixed-point */
        TEST_ASSERT(beatty >= expected[i] - 1 && beatty <= expected[i] + 1,
                    "Beatty number should match expected value");
    }

    return 0;
}

/**
 * Test: Beatty selection returns ready task
 */
static int test_beatty_select(void)
{
    beatty_scheduler_t sched;
    beatty_init(&sched, BEATTY_GOLDEN_RATIO);

    /* Create DAG with 3 tasks */
    dag_pdac_t dag;
    resource_vector_t quota = {.cpu = Q16(6.0), .memory = Q16(1024.0)};
    pdac_dag_init(&dag, quota);

    resource_vector_t res = {.cpu = Q16(1.0), .memory = Q16(200.0)};
    for (int i = 0; i < 3; i++) {
        char name[32];
        snprintf(name, sizeof(name), "Task %d", i);
        int id = pdac_dag_add_task(&dag, name, res);
        dag.tasks[id].state = TASK_STATE_READY;
    }

    beatty_recompute_all_priorities(&sched, &dag);

    /* Select a task */
    dag_task_t *selected = beatty_select(&sched, &dag);
    TEST_ASSERT(selected != NULL, "Should select a task");
    TEST_ASSERT(selected->state == TASK_STATE_READY, "Selected task should be READY");

    return 0;
}

/**
 * Test: Beatty determinism (same state → same selection)
 */
static int test_beatty_determinism(void)
{
    /* Create DAG with 5 tasks */
    dag_pdac_t dag;
    resource_vector_t quota = {.cpu = Q16(5.0), .memory = Q16(1024.0)};
    pdac_dag_init(&dag, quota);

    resource_vector_t res = {.cpu = Q16(1.0), .memory = Q16(200.0)};
    for (int i = 0; i < 5; i++) {
        char name[32];
        snprintf(name, sizeof(name), "Task %d", i);
        int id = pdac_dag_add_task(&dag, name, res);
        dag.tasks[id].state = TASK_STATE_READY;
    }

    /* Run 1 */
    beatty_scheduler_t sched1;
    beatty_init(&sched1, BEATTY_GOLDEN_RATIO);
    beatty_recompute_all_priorities(&sched1, &dag);

    uint16_t sequence1[10];
    for (int i = 0; i < 10; i++) {
        dag_task_t *task = beatty_select(&sched1, &dag);
        sequence1[i] = task->id;
    }

    /* Run 2 (reset) */
    beatty_scheduler_t sched2;
    beatty_init(&sched2, BEATTY_GOLDEN_RATIO);
    beatty_recompute_all_priorities(&sched2, &dag);

    uint16_t sequence2[10];
    for (int i = 0; i < 10; i++) {
        dag_task_t *task = beatty_select(&sched2, &dag);
        sequence2[i] = task->id;
    }

    /* Both sequences should match */
    for (int i = 0; i < 10; i++) {
        TEST_ASSERT_EQ(sequence1[i], sequence2[i], "Sequences should be identical");
    }

    return 0;
}

/**
 * Stress Test: Beatty Long Run
 */
static int test_beatty_stress(void)
{
    printf("\n[STRESS] Beatty Scheduler Long Run (100,000 cycles)\n");

    beatty_scheduler_t sched;
    beatty_init(&sched, BEATTY_GOLDEN_RATIO);

    dag_pdac_t dag;
    resource_vector_t quota = {.e0 = Q16(100.0), .e1 = Q16(1024.0)};
    pdac_dag_init(&dag, quota);

    /* Create 10 tasks */
    resource_vector_t res = {.e0 = Q16(1.0), .e1 = Q16(10.0)};
    for(int i=0; i<10; i++) {
        char name[32];
        snprintf(name, sizeof(name), "StressTask %d", i);
        int id = pdac_dag_add_task(&dag, name, res);
        dag.tasks[id].state = TASK_STATE_READY;
    }

    beatty_recompute_all_priorities(&sched, &dag);

    /* Run 100,000 iterations */
    for(int i=0; i<100000; i++) {
        dag_task_t *task = beatty_select(&sched, &dag);
        if (task) {
             /* Mock run time update (since we added the field) */
             task->stats.run_time_ticks++;
        }
    }

    /* Check distribution */
    uint64_t min_sel = 1000000, max_sel = 0;
    for(int i=0; i<10; i++) {
        uint64_t sel = sched.selections[i];
        if (sel < min_sel) min_sel = sel;
        if (sel > max_sel) max_sel = sel;
    }

    printf("  Min selections: %llu\n", min_sel);
    printf("  Max selections: %llu\n", max_sel);
    printf("  Spread: %llu (%.2f%%)\n", max_sel - min_sel,
           (double)(max_sel - min_sel) * 100.0 / (100000.0/10.0));

    /* With Beatty, spread should be small */
    TEST_ASSERT(min_sel > 9500, "No starvation (expected ~10000)");
    TEST_ASSERT(max_sel < 10500, "No dominance (expected ~10000)");

    /* Print stats using the new telemetry-aware function */
    beatty_print_stats(&sched, &dag);

    return 0;
}

/*******************************************************************************
 * HYBRID SCHEDULER TESTS
 ******************************************************************************/

/**
 * Test: Hybrid scheduler initialization
 */
static int test_hybrid_init(void)
{
    lcg_state_t rng;
    lcg_init(&rng, 42);

    hybrid_scheduler_t sched;
    hybrid_init(&sched, &rng);

    TEST_ASSERT(sched.rng == &rng, "RNG should be stored");
    TEST_ASSERT_EQ(sched.lottery_selections, 0, "Lottery selections should start at 0");
    TEST_ASSERT_EQ(sched.beatty_selections, 0, "Beatty selections should start at 0");

    return 0;
}

/**
 * Test: Hybrid mode distribution (80/20)
 */
static int test_hybrid_mode_distribution(void)
{
    lcg_state_t rng;
    lcg_init(&rng, 12345);

    hybrid_scheduler_t sched;
    hybrid_init(&sched, &rng);

    /* Create simple DAG */
    dag_pdac_t dag;
    resource_vector_t quota = {.cpu = Q16(4.0), .memory = Q16(1024.0)};
    pdac_dag_init(&dag, quota);

    resource_vector_t res = {.cpu = Q16(1.0), .memory = Q16(200.0)};
    for (int i = 0; i < 4; i++) {
        char name[32];
        snprintf(name, sizeof(name), "Task %d", i);
        int id = pdac_dag_add_task(&dag, name, res);
        dag.tasks[id].state = TASK_STATE_READY;
    }

    hybrid_recompute_all_tasks(&sched, &dag);

    /* Run 1000 selections */
    for (int i = 0; i < 1000; i++) {
        hybrid_select(&sched, &dag);
    }

    uint64_t lottery_count = hybrid_get_lottery_count(&sched);
    uint64_t beatty_count = hybrid_get_beatty_count(&sched);

    /* Should be approximately 800 lottery, 200 Beatty */
    TEST_ASSERT_RANGE(lottery_count, 750, 850, "Lottery count should be ~800");
    TEST_ASSERT_RANGE(beatty_count, 150, 250, "Beatty count should be ~200");

    return 0;
}

/**
 * Test: Hybrid starvation-freedom
 */
static int test_hybrid_starvation_free(void)
{
    lcg_state_t rng;
    lcg_init(&rng, 42);

    hybrid_scheduler_t sched;
    hybrid_init(&sched, &rng);

    /* Create DAG with extreme priority imbalance */
    dag_pdac_t dag;
    resource_vector_t quota = {.cpu = Q16(10.0), .memory = Q16(2048.0)};
    pdac_dag_init(&dag, quota);

    /* Giant task (99% resources) */
    resource_vector_t res_giant = {.cpu = Q16(9.0), .memory = Q16(1800.0)};
    int giant = pdac_dag_add_task(&dag, "Giant", res_giant);
    dag.tasks[giant].state = TASK_STATE_READY;

    /* Tiny task (1% resources) */
    resource_vector_t res_tiny = {.cpu = Q16(0.1), .memory = Q16(20.0)};
    int tiny = pdac_dag_add_task(&dag, "Tiny", res_tiny);
    dag.tasks[tiny].state = TASK_STATE_READY;

    hybrid_recompute_all_tasks(&sched, &dag);

    /* Run 500 selections */
    for (int i = 0; i < 500; i++) {
        hybrid_select(&sched, &dag);
    }

    /* Tiny task should still run (thanks to Beatty component) */
    uint64_t tiny_count = hybrid_get_task_selection_count(&sched, tiny);
    TEST_ASSERT(tiny_count > 0, "Tiny task should run (starvation-free)");
    TEST_ASSERT(tiny_count > 25, "Tiny task should run at least 5% of time");

    return 0;
}

/*******************************************************************************
 * ADMISSION CONTROL TESTS
 ******************************************************************************/

/**
 * Test: Admission control initialization
 */
static int test_admission_init(void)
{
    lcg_state_t rng;
    lcg_init(&rng, 42);

    resource_vector_t capacity = {.cpu = Q16(4.0), .memory = Q16(1024.0)};
    resource_vector_t refill = {.cpu = Q16(0.1), .memory = Q16(10.0)};
    resource_vector_t burst = {.cpu = Q16(2.0), .memory = Q16(512.0)};

    admission_control_t ac;
    admission_init(&ac, &rng, capacity, refill, burst);

    TEST_ASSERT(ac.rng == &rng, "RNG should be stored");
    TEST_ASSERT_EQ(ac.total_attempts, 0, "Total attempts should start at 0");

    return 0;
}

/**
 * Test: Admission probability computation
 */
static int test_admission_probability(void)
{
    /* Low load → high probability */
    q16_t prob_low = admission_compute_probability(Q16(0.1));
    TEST_ASSERT(prob_low > Q16(0.8), "Low load should give high probability");

    /* Medium load → medium probability */
    q16_t prob_med = admission_compute_probability(Q16(1.0));
    TEST_ASSERT_RANGE((double)prob_med / 65536.0, 0.4, 0.6,
                      "Medium load should give ~0.5 probability");

    /* High load → low probability */
    q16_t prob_high = admission_compute_probability(Q16(10.0));
    TEST_ASSERT(prob_high < Q16(0.2), "High load should give low probability");

    return 0;
}

/**
 * Test: Admission under light load (should admit)
 */
static int test_admission_light_load(void)
{
    lcg_state_t rng;
    lcg_init(&rng, 42);

    resource_vector_t capacity = {.cpu = Q16(4.0), .memory = Q16(1024.0)};
    resource_vector_t refill = {.cpu = Q16(0.5), .memory = Q16(50.0)};
    resource_vector_t burst = {.cpu = Q16(4.0), .memory = Q16(1024.0)};

    admission_control_t ac;
    admission_init(&ac, &rng, capacity, refill, burst);

    /* Empty DAG (light load) */
    dag_pdac_t dag;
    pdac_dag_init(&dag, capacity);

    /* Try admitting small task */
    dag_task_t task;
    task.resources.cpu = Q16(0.5);
    task.resources.memory = Q16(100.0);

    int admitted = admission_try_admit(&ac, &dag, &task);
    TEST_ASSERT(admitted == 1, "Should admit under light load");

    return 0;
}

/**
 * Test: Admission under heavy load (stochastic)
 */
static int test_admission_heavy_load(void)
{
    lcg_state_t rng;
    lcg_init(&rng, 12345);

    resource_vector_t capacity = {.cpu = Q16(2.0), .memory = Q16(512.0)};
    resource_vector_t refill = {.cpu = Q16(0.01), .memory = Q16(1.0)};
    resource_vector_t burst = {.cpu = Q16(0.1), .memory = Q16(10.0)};

    admission_control_t ac;
    admission_init(&ac, &rng, capacity, refill, burst);

    /* DAG with heavy load */
    dag_pdac_t dag;
    pdac_dag_init(&dag, capacity);

    resource_vector_t res_heavy = {.cpu = Q16(1.8), .memory = Q16(480.0)};
    int heavy_id = pdac_dag_add_task(&dag, "Heavy", res_heavy);
    dag.tasks[heavy_id].state = TASK_STATE_RUNNING;

    /* Try admitting 100 tasks */
    dag_task_t task;
    task.resources.cpu = Q16(0.1);
    task.resources.memory = Q16(50.0);

    uint32_t admitted_count = 0;
    for (int i = 0; i < 100; i++) {
        if (admission_try_admit(&ac, &dag, &task)) {
            admitted_count++;
        }
    }

    /* Some should be admitted (stochastic, not hard cutoff) */
    TEST_ASSERT(admitted_count > 0, "Some tasks should be admitted");
    /* But not all (load is high) */
    TEST_ASSERT(admitted_count < 80, "Not all tasks should be admitted");

    return 0;
}

/*******************************************************************************
 * INTEGRATION TESTS
 ******************************************************************************/

/**
 * Test: Integration with DAG dependencies
 */
static int test_integration_dag_deps(void)
{
    lcg_state_t rng;
    lcg_init(&rng, 42);

    hybrid_scheduler_t sched;
    hybrid_init(&sched, &rng);

    /* Create DAG with dependencies: B depends on A */
    dag_pdac_t dag;
    resource_vector_t quota = {.cpu = Q16(4.0), .memory = Q16(1024.0)};
    pdac_dag_init(&dag, quota);

    resource_vector_t res = {.cpu = Q16(1.0), .memory = Q16(200.0)};
    int task_a = pdac_dag_add_task(&dag, "Task A", res);
    int task_b = pdac_dag_add_task(&dag, "Task B (depends on A)", res);

    pdac_dag_add_dependency(&dag, task_b, task_a);

    dag.tasks[task_a].state = TASK_STATE_READY;
    dag.tasks[task_b].state = TASK_STATE_PENDING; /* Waiting for A */

    hybrid_recompute_all_tasks(&sched, &dag);

    /* Select task - should only get A (B is not ready) */
    dag_task_t *selected = hybrid_select(&sched, &dag);
    TEST_ASSERT_EQ(selected->id, task_a, "Should select Task A (only ready task)");

    return 0;
}

/**
 * Test: Full scheduler pipeline (admission → scheduling)
 */
static int test_integration_full_pipeline(void)
{
    /* Setup RNG */
    lcg_state_t rng;
    lcg_init(&rng, 99999);

    /* Setup admission control */
    resource_vector_t capacity = {.cpu = Q16(8.0), .memory = Q16(2048.0)};
    resource_vector_t refill = {.cpu = Q16(0.2), .memory = Q16(20.0)};
    resource_vector_t burst = {.cpu = Q16(4.0), .memory = Q16(1024.0)};

    admission_control_t ac;
    admission_init(&ac, &rng, capacity, refill, burst);

    /* Setup hybrid scheduler */
    hybrid_scheduler_t sched;
    hybrid_init(&sched, &rng);

    /* Setup DAG */
    dag_pdac_t dag;
    pdac_dag_init(&dag, capacity);

    /* Simulate workload: admit tasks, schedule them */
    resource_vector_t res = {.cpu = Q16(1.0), .memory = Q16(200.0)};

    for (int i = 0; i < 20; i++) {
        dag_task_t task;
        task.resources = res;
        snprintf(task.name, sizeof(task.name), "Task %d", i);

        /* Try to admit */
        if (admission_try_admit(&ac, &dag, &task)) {
            /* Admitted - add to DAG */
            int id = pdac_dag_add_task(&dag, task.name, res);
            dag.tasks[id].state = TASK_STATE_READY;
        }
    }

    hybrid_recompute_all_tasks(&sched, &dag);

    /* Schedule 10 tasks */
    for (int i = 0; i < 10; i++) {
        dag_task_t *selected = hybrid_select(&sched, &dag);
        if (selected != NULL) {
            /* Mark as running (simulate execution) */
            selected->state = TASK_STATE_RUNNING;
        }
    }

    /* Verify statistics make sense */
    uint64_t total_admits = admission_get_token_admits(&ac) +
                            admission_get_stochastic_admits(&ac);
    TEST_ASSERT(total_admits > 0, "Should have admitted some tasks");

    uint64_t total_selections = hybrid_get_lottery_count(&sched) +
                                hybrid_get_beatty_count(&sched);
    TEST_ASSERT(total_selections > 0, "Should have scheduled some tasks");

    return 0;
}

/*******************************************************************************
 * TEST SUITE RUNNER
 ******************************************************************************/

void run_all_scheduler_tests(void)
{
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   PDAC PHASE 3 SCHEDULER - UNIT TESTS                      ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n");

    printf("\n=== LCG TESTS ===\n");
    RUN_TEST(test_lcg_init);
    RUN_TEST(test_lcg_nonzero);
    RUN_TEST(test_lcg_range);
    RUN_TEST(test_lcg_uniform);
    RUN_TEST(test_lcg_chi_squared);

    printf("\n=== LOTTERY SCHEDULER TESTS ===\n");
    RUN_TEST(test_lottery_init);
    RUN_TEST(test_lottery_tickets);
    RUN_TEST(test_lottery_select);
    RUN_TEST(test_lottery_fairness);

    printf("\n=== BEATTY SCHEDULER TESTS ===\n");
    RUN_TEST(test_beatty_init);
    RUN_TEST(test_beatty_sequence);
    RUN_TEST(test_beatty_select);
    RUN_TEST(test_beatty_determinism);
    RUN_TEST(test_beatty_stress);

    printf("\n=== HYBRID SCHEDULER TESTS ===\n");
    RUN_TEST(test_hybrid_init);
    RUN_TEST(test_hybrid_mode_distribution);
    RUN_TEST(test_hybrid_starvation_free);

    printf("\n=== ADMISSION CONTROL TESTS ===\n");
    RUN_TEST(test_admission_init);
    RUN_TEST(test_admission_probability);
    RUN_TEST(test_admission_light_load);
    RUN_TEST(test_admission_heavy_load);

    printf("\n=== INTEGRATION TESTS ===\n");
    RUN_TEST(test_integration_dag_deps);
    RUN_TEST(test_integration_full_pipeline);

    /* Summary */
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   TEST SUMMARY                                              ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n");
    printf("Tests Run:    %d\n", g_tests_run);
    printf("Tests Passed: %d\n", g_tests_passed);
    printf("Tests Failed: %d\n", g_tests_failed);

    if (g_tests_failed == 0) {
        printf("\n✓ ALL TESTS PASSED\n\n");
    } else {
        printf("\n✗ SOME TESTS FAILED\n\n");
    }
}
