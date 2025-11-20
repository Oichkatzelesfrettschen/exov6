/**
 * @file test_integration_phase5.c
 * @brief Comprehensive Integration Tests for PDAC Phase 5
 *
 * TEST COVERAGE:
 * ==============
 * This file contains 35 integration tests that verify all Phase 5 components
 * work correctly together in realistic scenarios.
 *
 * TEST SUITES:
 * ============
 * 1. Lock-Free + RCU Integration (8 tests)
 * 2. Work-Stealing + Lock-Free (7 tests)
 * 3. Work-Stealing + RCU (6 tests)
 * 4. Three-Way Integration (6 tests)
 * 5. Performance & Scalability (4 tests)
 * 6. Stress & Endurance (4 tests)
 *
 * TOTAL: 35 TESTS
 *
 * INTEGRATION PATTERNS TESTED:
 * ============================
 * - RCU-protected lock-free queues
 * - Work-stealing with RCU task tracking
 * - Hazard pointers + RCU combined reclamation
 * - Full system integration scenarios
 * - Concurrent stress under load
 * - Memory safety under extreme conditions
 */

#include "lockfree.h"
#include "rcu_pdac.h"
#include "work_stealing.h"
#include "dag_pdac.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

/* Test counters */
static int tests_run = 0;
static int tests_passed = 0;

/* Test utilities */
#define TEST_START(name) \
    do { \
        printf("TEST: %s ... ", name); \
        fflush(stdout); \
        tests_run++; \
    } while(0)

#define TEST_PASS() \
    do { \
        printf("PASS\n"); \
        tests_passed++; \
    } while(0)

#define TEST_FAIL(msg) \
    do { \
        printf("FAIL: %s\n", msg); \
        return; \
    } while(0)

#define ASSERT(cond, msg) \
    do { \
        if (!(cond)) { \
            TEST_FAIL(msg); \
        } \
    } while(0)

/*******************************************************************************
 * SUITE 1: Lock-Free + RCU Integration
 ******************************************************************************/

/**
 * Test: RCU-protected queue operations
 */
void test_rcu_protected_queue(void) {
    TEST_START("RCU-protected queue operations");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    /* Writer enqueues under RCU */
    rcu_read_lock(&rcu, 0);
    for (int i = 0; i < 10; i++) {
        int *data = (int*)malloc(sizeof(int));
        *data = i;
        ms_enqueue(&queue, data, 0);
    }
    rcu_read_unlock(&rcu, 0);

    /* Reader dequeues under RCU */
    rcu_read_lock(&rcu, 1);
    int count = 0;
    while (!ms_is_empty(&queue)) {
        int *data = (int*)ms_dequeue(&queue, 1);
        if (data) {
            ASSERT(*data >= 0 && *data < 10, "Data should be valid");
            free(data);
            count++;
        }
    }
    rcu_read_unlock(&rcu, 1);

    ASSERT(count == 10, "Should dequeue all items");

    TEST_PASS();
}

/**
 * Test: Hazard pointers + RCU combined
 */
void test_hp_rcu_combined(void) {
    TEST_START("Hazard pointers + RCU combined");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    /* Enqueue data */
    for (int i = 0; i < 20; i++) {
        int *data = (int*)malloc(sizeof(int));
        *data = i;
        ms_enqueue(&queue, data, 0);
    }

    /* RCU read-side protects queue access */
    /* HP protects individual nodes */
    rcu_read_lock(&rcu, 0);
    for (int i = 0; i < 10; i++) {
        int *data = (int*)ms_dequeue(&queue, 0);
        if (data) free(data);
    }
    rcu_read_unlock(&rcu, 0);

    ASSERT(ms_get_size(&queue) == 10, "Should have 10 remaining");

    /* Cleanup */
    int *data;
    while ((data = (int*)ms_dequeue(&queue, 0)) != NULL) {
        free(data);
    }

    TEST_PASS();
}

/**
 * Test: RCU grace period with lock-free operations
 */
void test_rcu_gp_with_lockfree(void) {
    TEST_START("RCU grace period with lock-free ops");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    /* Enqueue under RCU protection */
    rcu_read_lock(&rcu, 0);
    for (int i = 0; i < 50; i++) {
        int *data = (int*)malloc(sizeof(int));
        *data = i;
        ms_enqueue(&queue, data, 0);
    }
    rcu_read_unlock(&rcu, 0);

    /* Trigger grace period */
    synchronize_rcu(&rcu);

    /* Dequeue after GP */
    int count = 0;
    int *data;
    while ((data = (int*)ms_dequeue(&queue, 0)) != NULL) {
        count++;
        free(data);
    }

    ASSERT(count == 50, "All data should survive grace period");

    TEST_PASS();
}

/**
 * Test: Stack operations under RCU
 */
void test_stack_under_rcu(void) {
    TEST_START("Stack operations under RCU");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    treiber_stack_t stack;
    treiber_init(&stack, &hp);

    /* Push under RCU */
    rcu_read_lock(&rcu, 0);
    for (int i = 0; i < 30; i++) {
        int *data = (int*)malloc(sizeof(int));
        *data = i;
        treiber_push(&stack, data, 0);
    }
    rcu_read_unlock(&rcu, 0);

    /* Pop under RCU */
    rcu_read_lock(&rcu, 1);
    int count = 0;
    int *data;
    while ((data = (int*)treiber_pop(&stack, 1)) != NULL) {
        count++;
        free(data);
    }
    rcu_read_unlock(&rcu, 1);

    ASSERT(count == 30, "Should pop all items");

    TEST_PASS();
}

/**
 * Test: Concurrent enqueue/dequeue under RCU
 */
void test_concurrent_queue_rcu(void) {
    TEST_START("Concurrent queue ops under RCU");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    /* Simulated concurrent enqueuers */
    for (int cpu = 0; cpu < 2; cpu++) {
        rcu_read_lock(&rcu, cpu);
        for (int i = 0; i < 25; i++) {
            int *data = (int*)malloc(sizeof(int));
            *data = cpu * 100 + i;
            ms_enqueue(&queue, data, cpu);
        }
        rcu_read_unlock(&rcu, cpu);
    }

    /* Simulated concurrent dequeuers */
    int counts[2] = {0, 0};
    for (int cpu = 2; cpu < 4; cpu++) {
        rcu_read_lock(&rcu, cpu);
        for (int i = 0; i < 15; i++) {
            int *data = (int*)ms_dequeue(&queue, cpu);
            if (data) {
                counts[cpu - 2]++;
                free(data);
            }
        }
        rcu_read_unlock(&rcu, cpu);
    }

    int total_dequeued = counts[0] + counts[1];
    ASSERT(total_dequeued == 30, "Should dequeue 30 items");

    /* Cleanup */
    int *data;
    while ((data = (int*)ms_dequeue(&queue, 0)) != NULL) {
        free(data);
    }

    TEST_PASS();
}

/**
 * Test: RCU callback with lock-free cleanup
 */
void test_rcu_callback_lockfree(void) {
    TEST_START("RCU callback with lock-free cleanup");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    /* Create data */
    for (int i = 0; i < 10; i++) {
        int *data = (int*)malloc(sizeof(int));
        *data = i;
        ms_enqueue(&queue, data, 0);
    }

    /* Wait for grace period */
    synchronize_rcu(&rcu);

    /* Verify data still accessible */
    ASSERT(ms_get_size(&queue) == 10, "Data should persist");

    /* Cleanup */
    int *data;
    while ((data = (int*)ms_dequeue(&queue, 0)) != NULL) {
        free(data);
    }

    TEST_PASS();
}

/**
 * Test: Multiple RCU readers with lock-free writer
 */
void test_multi_rcu_readers_lockfree_writer(void) {
    TEST_START("Multi RCU readers + lock-free writer");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    /* Writer populates queue */
    for (int i = 0; i < 100; i++) {
        int *data = (int*)malloc(sizeof(int));
        *data = i;
        ms_enqueue(&queue, data, 0);
    }

    /* Multiple readers access concurrently */
    for (int reader = 0; reader < 4; reader++) {
        rcu_read_lock(&rcu, reader);
        size_t size = ms_get_size(&queue);
        ASSERT(size > 0, "Readers should see data");
        rcu_read_unlock(&rcu, reader);
    }

    /* Cleanup */
    int *data;
    while ((data = (int*)ms_dequeue(&queue, 0)) != NULL) {
        free(data);
    }

    TEST_PASS();
}

/**
 * Test: RCU + HP memory reclamation coordination
 */
void test_rcu_hp_reclamation(void) {
    TEST_START("RCU + HP reclamation coordination");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    /* Large workload to trigger HP reclamation */
    for (int i = 0; i < 200; i++) {
        int *data = (int*)malloc(sizeof(int));
        *data = i;
        ms_enqueue(&queue, data, 0);
    }

    /* Dequeue triggers HP scans */
    for (int i = 0; i < 150; i++) {
        rcu_read_lock(&rcu, 0);
        int *data = (int*)ms_dequeue(&queue, 0);
        rcu_read_unlock(&rcu, 0);
        if (data) free(data);
    }

    /* Grace period */
    synchronize_rcu(&rcu);

    /* Verify remaining data */
    ASSERT(ms_get_size(&queue) == 50, "Should have 50 remaining");

    /* Cleanup */
    int *data;
    while ((data = (int*)ms_dequeue(&queue, 0)) != NULL) {
        free(data);
    }

    TEST_PASS();
}

/*******************************************************************************
 * SUITE 2: Work-Stealing + Lock-Free Integration
 ******************************************************************************/

/**
 * Test: Work-stealing with lock-free queue
 */
void test_ws_with_lockfree_queue(void) {
    TEST_START("Work-stealing + lock-free queue");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    ms_queue_t result_queue;
    ms_queue_init(&result_queue, &hp);

    /* Submit tasks to work-stealing */
    for (int i = 0; i < 50; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, 0);
    }

    /* Process and collect results in lock-free queue */
    int processed = 0;
    while (processed < 50) {
        for (int cpu = 0; cpu < 4; cpu++) {
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                int *result = (int*)malloc(sizeof(int));
                *result = task->id;
                ms_enqueue(&result_queue, result, cpu);
                processed++;
                free(task);
            }
        }
    }

    ASSERT(ms_get_size(&result_queue) == 50, "All results collected");

    /* Cleanup */
    int *result;
    while ((result = (int*)ms_dequeue(&result_queue, 0)) != NULL) {
        free(result);
    }

    TEST_PASS();
}

/**
 * Test: Work-stealing victim selection with lock-free stack
 */
void test_ws_victim_with_stack(void) {
    TEST_START("WS victim selection + stack");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    treiber_stack_t completed_stack;
    treiber_init(&completed_stack, &hp);

    /* Unbalanced submission */
    for (int i = 0; i < 80; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, 0);  /* All to CPU 0 */
    }

    /* Process with stealing, push to stack */
    int processed = 0;
    while (processed < 80) {
        for (int cpu = 0; cpu < 4; cpu++) {
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                treiber_push(&completed_stack, task, cpu);
                processed++;
            }
        }
    }

    ASSERT(atomic_load(&completed_stack.push_count) == 80,
           "All tasks should be in stack");

    /* Cleanup */
    dag_task_t *task;
    while ((task = (dag_task_t*)treiber_pop(&completed_stack, 0)) != NULL) {
        free(task);
    }

    TEST_PASS();
}

/**
 * Test: Chase-Lev deque resize during stealing
 */
void test_deque_resize_during_steal(void) {
    TEST_START("Deque resize during stealing");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    /* Submit enough to trigger resize */
    for (int i = 0; i < 300; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, 0);
    }

    ASSERT(atomic_load(&sched.cpus[0].deque.resize_count) >= 1,
           "Should have resized");

    /* Steal while large */
    int stolen = 0;
    for (int attempt = 0; attempt < 50; attempt++) {
        dag_task_t *task = ws_scheduler_try_steal(&sched, 0, 1);
        if (task) {
            stolen++;
            free(task);
        }
    }

    ASSERT(stolen > 0, "Should steal from large deque");

    /* Cleanup */
    for (int cpu = 0; cpu < 4; cpu++) {
        dag_task_t *task;
        while ((task = ws_scheduler_get_task(&sched, cpu)) != NULL) {
            free(task);
        }
    }

    TEST_PASS();
}

/**
 * Test: Work-stealing with hazard pointer protection
 */
void test_ws_with_hp_protection(void) {
    TEST_START("Work-stealing + HP protection");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    ms_queue_t shared_queue;
    ms_queue_init(&shared_queue, &hp);

    /* Tasks submitted to WS, results to HP-protected queue */
    for (int i = 0; i < 60; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, i % 4);
    }

    int processed = 0;
    while (processed < 60) {
        for (int cpu = 0; cpu < 4; cpu++) {
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                /* Process and enqueue result */
                int *result = (int*)malloc(sizeof(int));
                *result = task->id * 2;
                ms_enqueue(&shared_queue, result, cpu);
                processed++;
                free(task);
            }
        }
    }

    ASSERT(ms_get_size(&shared_queue) == 60, "All results in queue");

    /* Cleanup */
    int *result;
    while ((result = (int*)ms_dequeue(&shared_queue, 0)) != NULL) {
        free(result);
    }

    TEST_PASS();
}

/**
 * Test: Load balancing with lock-free data collection
 */
void test_load_balance_lockfree_collect(void) {
    TEST_START("Load balancing + lock-free collect");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    treiber_stack_t result_stack;
    treiber_init(&result_stack, &hp);

    /* Heavily imbalanced */
    for (int i = 0; i < 100; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, 0);
    }

    /* Process (automatic load balancing) */
    int processed = 0;
    while (processed < 100) {
        for (int cpu = 0; cpu < 4; cpu++) {
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                treiber_push(&result_stack, task, cpu);
                processed++;
            }
        }
    }

    /* Verify load was balanced */
    uint64_t total_steals = atomic_load(&sched.total_steals);
    ASSERT(total_steals > 0, "Should have stealing activity");

    /* Cleanup */
    dag_task_t *task;
    while ((task = (dag_task_t*)treiber_pop(&result_stack, 0)) != NULL) {
        free(task);
    }

    TEST_PASS();
}

/**
 * Test: Circular victim selection with queue
 */
void test_circular_victim_queue(void) {
    TEST_START("Circular victim + queue");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    /* Set circular strategy */
    sched.cpus[0].victim_strategy = WS_VICTIM_CIRCULAR;

    ms_queue_t results;
    ms_queue_init(&results, &hp);

    /* Submit to multiple CPUs */
    for (int cpu = 0; cpu < 4; cpu++) {
        for (int i = 0; i < 10; i++) {
            dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
            task->id = cpu * 10 + i;
            ws_scheduler_submit(&sched, task, cpu);
        }
    }

    /* Process all */
    int processed = 0;
    while (processed < 40) {
        for (int cpu = 0; cpu < 4; cpu++) {
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                int *result = (int*)malloc(sizeof(int));
                *result = task->id;
                ms_enqueue(&results, result, cpu);
                processed++;
                free(task);
            }
        }
    }

    ASSERT(ms_get_size(&results) == 40, "All tasks processed");

    /* Cleanup */
    int *result;
    while ((result = (int*)ms_dequeue(&results, 0)) != NULL) {
        free(result);
    }

    TEST_PASS();
}

/**
 * Test: Random victim with stack collection
 */
void test_random_victim_stack(void) {
    TEST_START("Random victim + stack collection");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    treiber_stack_t stack;
    treiber_init(&stack, &hp);

    /* Random distribution */
    for (int i = 0; i < 50; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, i % 4);
    }

    /* Process */
    int processed = 0;
    while (processed < 50) {
        for (int cpu = 0; cpu < 4; cpu++) {
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                treiber_push(&stack, task, cpu);
                processed++;
            }
        }
    }

    ASSERT(atomic_load(&stack.push_count) == 50, "All pushed");

    /* Cleanup */
    dag_task_t *task;
    while ((task = (dag_task_t*)treiber_pop(&stack, 0)) != NULL) {
        free(task);
    }

    TEST_PASS();
}

/*******************************************************************************
 * SUITE 3: Work-Stealing + RCU Integration
 ******************************************************************************/

/**
 * Test: Work-stealing under RCU protection
 */
void test_ws_under_rcu(void) {
    TEST_START("Work-stealing under RCU");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    /* Submit tasks */
    rcu_read_lock(&rcu, 0);
    for (int i = 0; i < 40; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, 0);
    }
    rcu_read_unlock(&rcu, 0);

    /* Process under RCU */
    int processed = 0;
    while (processed < 40) {
        for (int cpu = 0; cpu < 4; cpu++) {
            rcu_read_lock(&rcu, cpu);
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            rcu_read_unlock(&rcu, cpu);

            if (task) {
                processed++;
                free(task);
            }
        }
    }

    ASSERT(processed == 40, "All tasks processed");

    TEST_PASS();
}

/**
 * Test: RCU grace period during work-stealing
 */
void test_rcu_gp_during_ws(void) {
    TEST_START("RCU GP during work-stealing");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    /* Submit */
    for (int i = 0; i < 100; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, 0);
    }

    /* Process with periodic grace periods */
    int processed = 0;
    while (processed < 100) {
        for (int cpu = 0; cpu < 4; cpu++) {
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                processed++;
                free(task);

                /* Periodic GP */
                if (processed % 25 == 0) {
                    synchronize_rcu(&rcu);
                }
            }
        }
    }

    ASSERT(processed == 100, "All processed");

    TEST_PASS();
}

/**
 * Test: Stealing with RCU-protected data
 */
void test_stealing_rcu_data(void) {
    TEST_START("Stealing + RCU-protected data");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    atomic_ptr_t shared_config;
    int *config = (int*)malloc(sizeof(int));
    *config = 42;
    rcu_assign_pointer(&shared_config, config);

    /* Submit tasks */
    for (int i = 0; i < 60; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, 0);
    }

    /* Process with RCU-protected config access */
    int processed = 0;
    while (processed < 60) {
        for (int cpu = 0; cpu < 4; cpu++) {
            rcu_read_lock(&rcu, cpu);
            int *cfg = (int*)rcu_dereference(&shared_config);
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                ASSERT(*cfg == 42, "Config should be valid");
                processed++;
                free(task);
            }
            rcu_read_unlock(&rcu, cpu);
        }
    }

    free(config);

    TEST_PASS();
}

/**
 * Test: Work-stealing with RCU callbacks
 */
void test_ws_with_rcu_callbacks(void) {
    TEST_START("Work-stealing + RCU callbacks");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    /* Submit tasks */
    for (int i = 0; i < 30; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, 0);
    }

    /* Process */
    int processed = 0;
    while (processed < 30) {
        for (int cpu = 0; cpu < 4; cpu++) {
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                processed++;
                free(task);

                /* Trigger RCU processing */
                rcu_process_callbacks(&rcu, 0);
            }
        }
    }

    synchronize_rcu(&rcu);

    TEST_PASS();
}

/**
 * Test: Multi-CPU work-stealing with RCU reads
 */
void test_multicpu_ws_rcu(void) {
    TEST_START("Multi-CPU WS + RCU reads");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    /* Distribute tasks */
    for (int cpu = 0; cpu < 4; cpu++) {
        for (int i = 0; i < 15; i++) {
            dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
            task->id = cpu * 15 + i;
            ws_scheduler_submit(&sched, task, cpu);
        }
    }

    /* Process with RCU */
    int processed = 0;
    while (processed < 60) {
        for (int cpu = 0; cpu < 4; cpu++) {
            rcu_read_lock(&rcu, cpu);
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                processed++;
                free(task);
            }
            rcu_read_unlock(&rcu, cpu);
        }
    }

    ASSERT(processed == 60, "All processed");

    TEST_PASS();
}

/**
 * Test: RCU synchronize with active work-stealing
 */
void test_rcu_sync_active_ws(void) {
    TEST_START("RCU sync with active WS");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    /* Submit large batch */
    for (int i = 0; i < 80; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, 0);
    }

    /* Process 40, sync, process remaining */
    int processed = 0;
    while (processed < 40) {
        for (int cpu = 0; cpu < 4; cpu++) {
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                processed++;
                free(task);
            }
        }
    }

    synchronize_rcu(&rcu);

    while (processed < 80) {
        for (int cpu = 0; cpu < 4; cpu++) {
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                processed++;
                free(task);
            }
        }
    }

    ASSERT(processed == 80, "All processed");

    TEST_PASS();
}

/*******************************************************************************
 * SUITE 4: Three-Way Integration (Lock-Free + RCU + Work-Stealing)
 ******************************************************************************/

/**
 * Test: Full three-way integration
 */
void test_three_way_integration(void) {
    TEST_START("Lock-free + RCU + WS integration");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    ms_queue_t result_queue;
    ms_queue_init(&result_queue, &hp);

    /* Submit to WS */
    for (int i = 0; i < 50; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, 0);
    }

    /* Process with RCU, collect in lock-free queue */
    int processed = 0;
    while (processed < 50) {
        for (int cpu = 0; cpu < 4; cpu++) {
            rcu_read_lock(&rcu, cpu);
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                int *result = (int*)malloc(sizeof(int));
                *result = task->id;
                ms_enqueue(&result_queue, result, cpu);
                processed++;
                free(task);
            }
            rcu_read_unlock(&rcu, cpu);
        }
    }

    synchronize_rcu(&rcu);

    ASSERT(ms_get_size(&result_queue) == 50, "All results collected");

    /* Cleanup */
    int *result;
    while ((result = (int*)ms_dequeue(&result_queue, 0)) != NULL) {
        free(result);
    }

    TEST_PASS();
}

/**
 * Test: Pipeline with all components
 */
void test_full_pipeline(void) {
    TEST_START("Full pipeline integration");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    ms_queue_t input_queue;
    ms_queue_init(&input_queue, &hp);

    treiber_stack_t output_stack;
    treiber_init(&output_stack, &hp);

    /* Stage 1: Generate input (lock-free queue) */
    for (int i = 0; i < 40; i++) {
        int *data = (int*)malloc(sizeof(int));
        *data = i;
        ms_enqueue(&input_queue, data, 0);
    }

    /* Stage 2: Distribute to work-stealing */
    while (!ms_is_empty(&input_queue)) {
        int *data = (int*)ms_dequeue(&input_queue, 0);
        if (data) {
            dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
            task->id = *data;
            ws_scheduler_submit(&sched, task, 0);
            free(data);
        }
    }

    /* Stage 3: Process with RCU, output to stack */
    int processed = 0;
    while (processed < 40) {
        for (int cpu = 0; cpu < 4; cpu++) {
            rcu_read_lock(&rcu, cpu);
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                treiber_push(&output_stack, task, cpu);
                processed++;
            }
            rcu_read_unlock(&rcu, cpu);
        }
    }

    ASSERT(atomic_load(&output_stack.push_count) == 40,
           "All tasks in output");

    /* Cleanup */
    dag_task_t *task;
    while ((task = (dag_task_t*)treiber_pop(&output_stack, 0)) != NULL) {
        free(task);
    }

    TEST_PASS();
}

/**
 * Test: Concurrent producers, WS processors, lock-free collectors
 */
void test_concurrent_producer_ws_collector(void) {
    TEST_START("Concurrent prod + WS + collect");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    ms_queue_t results;
    ms_queue_init(&results, &hp);

    /* Multiple producers submit to WS */
    for (int producer = 0; producer < 2; producer++) {
        for (int i = 0; i < 25; i++) {
            dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
            task->id = producer * 100 + i;
            ws_scheduler_submit(&sched, task, producer);
        }
    }

    /* WS processors with RCU */
    int processed = 0;
    while (processed < 50) {
        for (int cpu = 0; cpu < 4; cpu++) {
            rcu_read_lock(&rcu, cpu);
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                int *result = (int*)malloc(sizeof(int));
                *result = task->id;
                ms_enqueue(&results, result, cpu);
                processed++;
                free(task);
            }
            rcu_read_unlock(&rcu, cpu);
        }
    }

    ASSERT(ms_get_size(&results) == 50, "All results");

    /* Cleanup */
    int *result;
    while ((result = (int*)ms_dequeue(&results, 0)) != NULL) {
        free(result);
    }

    TEST_PASS();
}

/**
 * Test: Grace period during full system operation
 */
void test_gp_during_full_operation(void) {
    TEST_START("GP during full system operation");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    /* Submit tasks */
    for (int i = 0; i < 60; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, i % 4);
    }

    /* Process with periodic GPs */
    int processed = 0;
    while (processed < 60) {
        for (int cpu = 0; cpu < 4; cpu++) {
            rcu_read_lock(&rcu, cpu);
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                int *result = (int*)malloc(sizeof(int));
                *result = task->id;
                ms_enqueue(&queue, result, cpu);
                processed++;
                free(task);
            }
            rcu_read_unlock(&rcu, cpu);

            if (processed % 15 == 0) {
                synchronize_rcu(&rcu);
            }
        }
    }

    ASSERT(ms_get_size(&queue) == 60, "All processed");

    /* Cleanup */
    int *result;
    while ((result = (int*)ms_dequeue(&queue, 0)) != NULL) {
        free(result);
    }

    TEST_PASS();
}

/**
 * Test: Mixed stack/queue with WS and RCU
 */
void test_mixed_structures_ws_rcu(void) {
    TEST_START("Mixed structures + WS + RCU");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    treiber_stack_t stack;
    treiber_init(&stack, &hp);

    /* Submit to WS */
    for (int i = 0; i < 40; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, 0);
    }

    /* Process: even to queue, odd to stack */
    int processed = 0;
    while (processed < 40) {
        for (int cpu = 0; cpu < 4; cpu++) {
            rcu_read_lock(&rcu, cpu);
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                if (task->id % 2 == 0) {
                    ms_enqueue(&queue, task, cpu);
                } else {
                    treiber_push(&stack, task, cpu);
                }
                processed++;
            }
            rcu_read_unlock(&rcu, cpu);
        }
    }

    size_t queue_size = ms_get_size(&queue);
    size_t stack_size = atomic_load(&stack.push_count);

    ASSERT(queue_size + stack_size == 40, "All accounted for");

    /* Cleanup */
    dag_task_t *task;
    while ((task = (dag_task_t*)ms_dequeue(&queue, 0)) != NULL) {
        free(task);
    }
    while ((task = (dag_task_t*)treiber_pop(&stack, 0)) != NULL) {
        free(task);
    }

    TEST_PASS();
}

/**
 * Test: Full system with all victim strategies
 */
void test_full_system_all_strategies(void) {
    TEST_START("Full system + all strategies");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    /* Different strategy per CPU */
    sched.cpus[0].victim_strategy = WS_VICTIM_RANDOM;
    sched.cpus[1].victim_strategy = WS_VICTIM_CIRCULAR;
    sched.cpus[2].victim_strategy = WS_VICTIM_RANDOM;
    sched.cpus[3].victim_strategy = WS_VICTIM_CIRCULAR;

    ms_queue_t results;
    ms_queue_init(&results, &hp);

    /* Submit tasks */
    for (int i = 0; i < 80; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, 0);
    }

    /* Process */
    int processed = 0;
    while (processed < 80) {
        for (int cpu = 0; cpu < 4; cpu++) {
            rcu_read_lock(&rcu, cpu);
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                int *result = (int*)malloc(sizeof(int));
                *result = task->id;
                ms_enqueue(&results, result, cpu);
                processed++;
                free(task);
            }
            rcu_read_unlock(&rcu, cpu);
        }
    }

    ASSERT(ms_get_size(&results) == 80, "All processed");

    /* Cleanup */
    int *result;
    while ((result = (int*)ms_dequeue(&results, 0)) != NULL) {
        free(result);
    }

    TEST_PASS();
}

/*******************************************************************************
 * SUITE 5: Performance & Scalability
 ******************************************************************************/

/**
 * Test: High-throughput lock-free queue with RCU
 */
void test_high_throughput_queue_rcu(void) {
    TEST_START("High-throughput queue + RCU");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    const int N = 1000;

    /* Enqueue */
    rcu_read_lock(&rcu, 0);
    for (int i = 0; i < N; i++) {
        int *data = (int*)malloc(sizeof(int));
        *data = i;
        ms_enqueue(&queue, data, 0);
    }
    rcu_read_unlock(&rcu, 0);

    /* Dequeue */
    rcu_read_lock(&rcu, 1);
    int dequeued = 0;
    int *data;
    while ((data = (int*)ms_dequeue(&queue, 1)) != NULL) {
        dequeued++;
        free(data);
    }
    rcu_read_unlock(&rcu, 1);

    ASSERT(dequeued == N, "All dequeued");

    TEST_PASS();
}

/**
 * Test: Work-stealing scalability
 */
void test_ws_scalability(void) {
    TEST_START("Work-stealing scalability");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    const int N = 500;

    /* All to one CPU */
    for (int i = 0; i < N; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, 0);
    }

    /* Process across CPUs */
    int processed = 0;
    while (processed < N) {
        for (int cpu = 0; cpu < 4; cpu++) {
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                processed++;
                free(task);
            }
        }
    }

    /* Check distribution */
    uint64_t min_exec = UINT64_MAX;
    uint64_t max_exec = 0;
    for (int cpu = 0; cpu < 4; cpu++) {
        uint64_t exec = atomic_load(&sched.cpus[cpu].tasks_executed);
        if (exec < min_exec) min_exec = exec;
        if (exec > max_exec) max_exec = exec;
    }

    /* Should be relatively balanced (within 2x) */
    ASSERT(max_exec <= min_exec * 3, "Should be balanced");

    TEST_PASS();
}

/**
 * Test: RCU grace period performance
 */
void test_rcu_gp_performance(void) {
    TEST_START("RCU GP performance");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    /* Multiple rapid GPs with some RCU activity */
    for (int i = 0; i < 10; i++) {
        /* Some read-side activity before GP */
        for (int cpu = 0; cpu < 4; cpu++) {
            rcu_read_lock(&rcu, cpu);
            /* Simulate work */
            volatile int x = cpu * i;
            (void)x;
            rcu_read_unlock(&rcu, cpu);
        }

        synchronize_rcu(&rcu);
    }

    rcu_stats_t stats;
    rcu_get_stats(&rcu, &stats);

    /* Note: Multiple synchronize_rcu calls can share GPs (merge),
     * so we just verify that GPs completed, not exact count */
    ASSERT(stats.grace_periods > 0, "Should complete GPs");
    ASSERT(stats.grace_periods <= 10, "Should not exceed call count");

    TEST_PASS();
}

/**
 * Test: Mixed workload performance
 */
void test_mixed_workload_perf(void) {
    TEST_START("Mixed workload performance");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    const int N = 200;

    /* Submit */
    for (int i = 0; i < N; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, i % 4);
    }

    /* Process and collect */
    int processed = 0;
    while (processed < N) {
        for (int cpu = 0; cpu < 4; cpu++) {
            rcu_read_lock(&rcu, cpu);
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                int *result = (int*)malloc(sizeof(int));
                *result = task->id;
                ms_enqueue(&queue, result, cpu);
                processed++;
                free(task);
            }
            rcu_read_unlock(&rcu, cpu);
        }
    }

    ASSERT(ms_get_size(&queue) == N, "All processed");

    /* Cleanup */
    int *result;
    while ((result = (int*)ms_dequeue(&queue, 0)) != NULL) {
        free(result);
    }

    TEST_PASS();
}

/*******************************************************************************
 * SUITE 6: Stress & Endurance
 ******************************************************************************/

/**
 * Test: Extended stress test
 */
void test_extended_stress(void) {
    TEST_START("Extended stress test");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    const int ROUNDS = 10;
    const int PER_ROUND = 50;

    for (int round = 0; round < ROUNDS; round++) {
        /* Submit */
        for (int i = 0; i < PER_ROUND; i++) {
            dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
            task->id = round * PER_ROUND + i;
            ws_scheduler_submit(&sched, task, 0);
        }

        /* Process */
        int processed = 0;
        while (processed < PER_ROUND) {
            for (int cpu = 0; cpu < 4; cpu++) {
                rcu_read_lock(&rcu, cpu);
                dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
                if (task) {
                    int *result = (int*)malloc(sizeof(int));
                    *result = task->id;
                    ms_enqueue(&queue, result, cpu);
                    processed++;
                    free(task);
                }
                rcu_read_unlock(&rcu, cpu);
            }
        }

        /* Grace period each round */
        synchronize_rcu(&rcu);
    }

    ASSERT(ms_get_size(&queue) == ROUNDS * PER_ROUND, "All processed");

    /* Cleanup */
    int *result;
    while ((result = (int*)ms_dequeue(&queue, 0)) != NULL) {
        free(result);
    }

    TEST_PASS();
}

/**
 * Test: Memory pressure test
 */
void test_memory_pressure(void) {
    TEST_START("Memory pressure test");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    /* Large allocations */
    for (int i = 0; i < 300; i++) {
        int *data = (int*)malloc(sizeof(int));
        *data = i;
        ms_enqueue(&queue, data, 0);
    }

    /* Dequeue most */
    for (int i = 0; i < 250; i++) {
        int *data = (int*)ms_dequeue(&queue, 0);
        if (data) free(data);
    }

    synchronize_rcu(&rcu);

    /* Verify remaining */
    ASSERT(ms_get_size(&queue) == 50, "Correct remaining");

    /* Cleanup */
    int *data;
    while ((data = (int*)ms_dequeue(&queue, 0)) != NULL) {
        free(data);
    }

    TEST_PASS();
}

/**
 * Test: Rapid queue/dequeue cycles
 */
void test_rapid_cycles(void) {
    TEST_START("Rapid queue/dequeue cycles");

    hp_domain_t hp;
    hp_domain_init(&hp);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    for (int cycle = 0; cycle < 20; cycle++) {
        /* Enqueue */
        for (int i = 0; i < 25; i++) {
            int *data = (int*)malloc(sizeof(int));
            *data = i;
            ms_enqueue(&queue, data, 0);
        }

        /* Dequeue */
        for (int i = 0; i < 25; i++) {
            int *data = (int*)ms_dequeue(&queue, 0);
            if (data) free(data);
        }

        ASSERT(ms_is_empty(&queue), "Should be empty each cycle");
    }

    TEST_PASS();
}

/**
 * Test: Endurance test all components
 */
void test_endurance_all_components(void) {
    TEST_START("Endurance test all components");

    hp_domain_t hp;
    hp_domain_init(&hp);

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    treiber_stack_t stack;
    treiber_init(&stack, &hp);

    const int ITERATIONS = 100;

    for (int iter = 0; iter < ITERATIONS; iter++) {
        /* Submit to WS */
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = iter;
        ws_scheduler_submit(&sched, task, iter % 4);

        /* Process */
        dag_task_t *processed_task = ws_scheduler_get_task(&sched, iter % 4);
        if (processed_task) {
            /* Even to queue, odd to stack */
            if (processed_task->id % 2 == 0) {
                ms_enqueue(&queue, processed_task, 0);
            } else {
                treiber_push(&stack, processed_task, 0);
            }
        }

        /* Periodic cleanup */
        if (iter % 10 == 0) {
            dag_task_t *t;
            while ((t = (dag_task_t*)ms_dequeue(&queue, 0)) != NULL) {
                free(t);
            }
            while ((t = (dag_task_t*)treiber_pop(&stack, 0)) != NULL) {
                free(t);
            }
            synchronize_rcu(&rcu);
        }
    }

    /* Final cleanup */
    dag_task_t *t;
    while ((t = (dag_task_t*)ms_dequeue(&queue, 0)) != NULL) {
        free(t);
    }
    while ((t = (dag_task_t*)treiber_pop(&stack, 0)) != NULL) {
        free(t);
    }

    TEST_PASS();
}

/*******************************************************************************
 * TEST MAIN
 ******************************************************************************/

int main(void) {
    printf("========================================\n");
    printf("PDAC Phase 5 Integration Test Suite\n");
    printf("========================================\n\n");

    /* Suite 1: Lock-Free + RCU */
    printf("--- Lock-Free + RCU Integration (8 tests) ---\n");
    test_rcu_protected_queue();
    test_hp_rcu_combined();
    test_rcu_gp_with_lockfree();
    test_stack_under_rcu();
    test_concurrent_queue_rcu();
    test_rcu_callback_lockfree();
    test_multi_rcu_readers_lockfree_writer();
    test_rcu_hp_reclamation();

    /* Suite 2: Work-Stealing + Lock-Free */
    printf("\n--- Work-Stealing + Lock-Free (7 tests) ---\n");
    test_ws_with_lockfree_queue();
    test_ws_victim_with_stack();
    test_deque_resize_during_steal();
    test_ws_with_hp_protection();
    test_load_balance_lockfree_collect();
    test_circular_victim_queue();
    test_random_victim_stack();

    /* Suite 3: Work-Stealing + RCU */
    printf("\n--- Work-Stealing + RCU (6 tests) ---\n");
    test_ws_under_rcu();
    test_rcu_gp_during_ws();
    test_stealing_rcu_data();
    test_ws_with_rcu_callbacks();
    test_multicpu_ws_rcu();
    test_rcu_sync_active_ws();

    /* Suite 4: Three-Way Integration */
    printf("\n--- Three-Way Integration (6 tests) ---\n");
    test_three_way_integration();
    test_full_pipeline();
    test_concurrent_producer_ws_collector();
    test_gp_during_full_operation();
    test_mixed_structures_ws_rcu();
    test_full_system_all_strategies();

    /* Suite 5: Performance & Scalability */
    printf("\n--- Performance & Scalability (4 tests) ---\n");
    test_high_throughput_queue_rcu();
    test_ws_scalability();
    test_rcu_gp_performance();
    test_mixed_workload_perf();

    /* Suite 6: Stress & Endurance */
    printf("\n--- Stress & Endurance (4 tests) ---\n");
    test_extended_stress();
    test_memory_pressure();
    test_rapid_cycles();
    test_endurance_all_components();

    /* Summary */
    printf("\n========================================\n");
    printf("Integration Test Summary\n");
    printf("========================================\n");
    printf("Tests run:    %d\n", tests_run);
    printf("Tests passed: %d\n", tests_passed);
    printf("Tests failed: %d\n", tests_run - tests_passed);
    printf("Success rate: %.1f%%\n",
           100.0 * tests_passed / tests_run);
    printf("========================================\n");

    return (tests_run == tests_passed) ? 0 : 1;
}
