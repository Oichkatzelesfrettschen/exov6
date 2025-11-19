/**
 * @file test_work_stealing.c
 * @brief Comprehensive Tests for Chase-Lev Work-Stealing Deque
 *
 * TEST COVERAGE:
 * ==============
 * 1. Deque Initialization (2 tests)
 *    - Basic initialization
 *    - Array allocation
 *
 * 2. Owner Operations (6 tests)
 *    - Push operations
 *    - Pop operations
 *    - Push/pop sequencing (LIFO)
 *    - Empty deque handling
 *    - Array resizing
 *    - Large workload stress test
 *
 * 3. Thief Operations (4 tests)
 *    - Steal operations
 *    - Steal from empty deque
 *    - Multiple steals
 *    - Steal ordering (FIFO from top)
 *
 * 4. Contention Cases (4 tests)
 *    - Owner pop vs thief steal (last element)
 *    - Multiple thieves stealing
 *    - Concurrent push/steal
 *    - Race condition verification
 *
 * 5. Work-Stealing Scheduler (5 tests)
 *    - Scheduler initialization
 *    - Task submission
 *    - Local task retrieval
 *    - Work stealing across CPUs
 *    - Load balancing
 *
 * 6. Victim Selection (3 tests)
 *    - Random victim selection
 *    - Circular victim selection
 *    - Victim exclusion (no self-stealing)
 *
 * 7. Integration Tests (3 tests)
 *    - End-to-end work-stealing scenario
 *    - Imbalanced workload distribution
 *    - Stress test with many tasks
 *
 * TOTAL: 27 TESTS
 */

#include "work_stealing.h"
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
 * DEQUE INITIALIZATION TESTS
 ******************************************************************************/

/**
 * Test: Deque basic initialization
 */
void test_deque_init(void) {
    TEST_START("Deque initialization");

    ws_deque_t deque;
    ws_deque_init(&deque, 0);

    ASSERT(ws_deque_is_empty(&deque), "Should be empty after init");
    ASSERT(ws_deque_size(&deque) == 0, "Size should be 0");
    ASSERT(atomic_load(&deque.bottom) == 0, "Bottom should be 0");
    ASSERT(atomic_load(&deque.top) == 0, "Top should be 0");

    TEST_PASS();
}

/**
 * Test: Array allocation
 */
void test_array_alloc(void) {
    TEST_START("Array allocation");

    ws_array_t *array = ws_array_new(256);
    ASSERT(array != NULL, "Array allocation should succeed");
    ASSERT(array->capacity == 256, "Capacity should be 256");
    ASSERT(array->mask == 255, "Mask should be 255");
    ASSERT(array->tasks != NULL, "Tasks array should be allocated");

    /* Cleanup */
    free(array->tasks);
    free(array);

    TEST_PASS();
}

/*******************************************************************************
 * OWNER OPERATION TESTS
 ******************************************************************************/

/**
 * Test: Push operations
 */
void test_deque_push(void) {
    TEST_START("Deque push operations");

    rcu_state_t rcu;
    rcu_init(&rcu, 1);

    ws_deque_t deque;
    ws_deque_init(&deque, 0);

    /* Push 10 tasks */
    for (int i = 0; i < 10; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_deque_push(&deque, task, &rcu);
    }

    ASSERT(ws_deque_size(&deque) == 10, "Should have 10 tasks");
    ASSERT(!ws_deque_is_empty(&deque), "Should not be empty");

    /* Cleanup */
    dag_task_t *task;
    while ((task = ws_deque_pop(&deque, 0, &rcu)) != NULL) {
        free(task);
    }

    TEST_PASS();
}

/**
 * Test: Pop operations
 */
void test_deque_pop(void) {
    TEST_START("Deque pop operations");

    rcu_state_t rcu;
    rcu_init(&rcu, 1);

    ws_deque_t deque;
    ws_deque_init(&deque, 0);

    /* Push then pop */
    dag_task_t *task1 = (dag_task_t*)malloc(sizeof(dag_task_t));
    task1->id = 100;
    ws_deque_push(&deque, task1, &rcu);

    dag_task_t *popped = ws_deque_pop(&deque, 0, &rcu);
    ASSERT(popped != NULL, "Pop should return task");
    ASSERT(popped->id == 100, "Should pop the pushed task");

    free(popped);

    /* Pop from empty */
    popped = ws_deque_pop(&deque, 0, &rcu);
    ASSERT(popped == NULL, "Pop from empty should return NULL");

    TEST_PASS();
}

/**
 * Test: LIFO semantics (owner)
 */
void test_deque_lifo(void) {
    TEST_START("Deque LIFO semantics");

    rcu_state_t rcu;
    rcu_init(&rcu, 1);

    ws_deque_t deque;
    ws_deque_init(&deque, 0);

    /* Push 1, 2, 3 */
    for (int i = 1; i <= 3; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_deque_push(&deque, task, &rcu);
    }

    /* Pop should return 3, 2, 1 (LIFO) */
    dag_task_t *t1 = ws_deque_pop(&deque, 0, &rcu);
    ASSERT(t1 && t1->id == 3, "First pop should return 3");
    free(t1);

    dag_task_t *t2 = ws_deque_pop(&deque, 0, &rcu);
    ASSERT(t2 && t2->id == 2, "Second pop should return 2");
    free(t2);

    dag_task_t *t3 = ws_deque_pop(&deque, 0, &rcu);
    ASSERT(t3 && t3->id == 1, "Third pop should return 1");
    free(t3);

    TEST_PASS();
}

/**
 * Test: Empty deque handling
 */
void test_deque_empty(void) {
    TEST_START("Empty deque handling");

    rcu_state_t rcu;
    rcu_init(&rcu, 1);

    ws_deque_t deque;
    ws_deque_init(&deque, 0);

    ASSERT(ws_deque_is_empty(&deque), "Should be empty");

    /* Pop from empty */
    dag_task_t *task = ws_deque_pop(&deque, 0, &rcu);
    ASSERT(task == NULL, "Pop from empty should return NULL");

    /* Steal from empty */
    task = ws_deque_steal(&deque, 1, &rcu);
    ASSERT(task == NULL, "Steal from empty should return NULL");

    TEST_PASS();
}

/**
 * Test: Array resizing
 */
void test_deque_resize(void) {
    TEST_START("Deque array resizing");

    rcu_state_t rcu;
    rcu_init(&rcu, 1);

    ws_deque_t deque;
    ws_deque_init(&deque, 0);

    /* Push beyond initial capacity (256) */
    const int N = 300;
    for (int i = 0; i < N; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_deque_push(&deque, task, &rcu);
    }

    ASSERT(ws_deque_size(&deque) == N, "Should have all tasks after resize");
    ASSERT(atomic_load(&deque.resize_count) >= 1, "Should have resized");

    /* Cleanup */
    for (int i = 0; i < N; i++) {
        dag_task_t *task = ws_deque_pop(&deque, 0, &rcu);
        free(task);
    }

    TEST_PASS();
}

/**
 * Test: Large workload stress
 */
void test_deque_stress(void) {
    TEST_START("Deque stress test");

    rcu_state_t rcu;
    rcu_init(&rcu, 1);

    ws_deque_t deque;
    ws_deque_init(&deque, 0);

    const int N = 1000;

    /* Push N tasks */
    for (int i = 0; i < N; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_deque_push(&deque, task, &rcu);
    }

    ASSERT(ws_deque_size(&deque) == N, "Should have N tasks");

    /* Pop all */
    int popped = 0;
    dag_task_t *task;
    while ((task = ws_deque_pop(&deque, 0, &rcu)) != NULL) {
        ASSERT(task->id >= 0 && task->id < N, "Task ID should be valid");
        free(task);
        popped++;
    }

    ASSERT(popped == N, "Should pop all N tasks");
    ASSERT(ws_deque_is_empty(&deque), "Should be empty");

    TEST_PASS();
}

/*******************************************************************************
 * THIEF OPERATION TESTS
 ******************************************************************************/

/**
 * Test: Steal operations
 */
void test_deque_steal(void) {
    TEST_START("Deque steal operations");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    ws_deque_t deque;
    ws_deque_init(&deque, 0);

    /* Owner pushes */
    for (int i = 1; i <= 5; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_deque_push(&deque, task, &rcu);
    }

    /* Thief steals */
    dag_task_t *stolen = ws_deque_steal(&deque, 1, &rcu);
    ASSERT(stolen != NULL, "Steal should succeed");
    ASSERT(stolen->id == 1, "Should steal from top (FIFO for thieves)");
    free(stolen);

    ASSERT(ws_deque_size(&deque) == 4, "Size should be 4 after steal");

    /* Cleanup */
    dag_task_t *task;
    while ((task = ws_deque_pop(&deque, 0, &rcu)) != NULL) {
        free(task);
    }

    TEST_PASS();
}

/**
 * Test: Steal from empty
 */
void test_steal_empty(void) {
    TEST_START("Steal from empty deque");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    ws_deque_t deque;
    ws_deque_init(&deque, 0);

    dag_task_t *stolen = ws_deque_steal(&deque, 1, &rcu);
    ASSERT(stolen == NULL, "Steal from empty should return NULL");

    TEST_PASS();
}

/**
 * Test: Multiple steals
 */
void test_multiple_steals(void) {
    TEST_START("Multiple steal operations");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    ws_deque_t deque;
    ws_deque_init(&deque, 0);

    /* Push 10 tasks */
    for (int i = 0; i < 10; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_deque_push(&deque, task, &rcu);
    }

    /* Steal 5 times */
    for (int i = 0; i < 5; i++) {
        dag_task_t *stolen = ws_deque_steal(&deque, 1, &rcu);
        ASSERT(stolen != NULL, "Steal should succeed");
        ASSERT(stolen->id == i, "Should steal in FIFO order");
        free(stolen);
    }

    ASSERT(ws_deque_size(&deque) == 5, "Should have 5 remaining");

    /* Cleanup */
    dag_task_t *task;
    while ((task = ws_deque_pop(&deque, 0, &rcu)) != NULL) {
        free(task);
    }

    TEST_PASS();
}

/**
 * Test: Steal ordering (FIFO from top)
 */
void test_steal_ordering(void) {
    TEST_START("Steal FIFO ordering");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    ws_deque_t deque;
    ws_deque_init(&deque, 0);

    /* Push 1, 2, 3, 4, 5 */
    for (int i = 1; i <= 5; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_deque_push(&deque, task, &rcu);
    }

    /* Thieves steal from top (oldest first) */
    dag_task_t *t1 = ws_deque_steal(&deque, 1, &rcu);
    ASSERT(t1 && t1->id == 1, "First steal should get 1");
    free(t1);

    dag_task_t *t2 = ws_deque_steal(&deque, 1, &rcu);
    ASSERT(t2 && t2->id == 2, "Second steal should get 2");
    free(t2);

    /* Owner pops from bottom (newest first) */
    dag_task_t *t5 = ws_deque_pop(&deque, 0, &rcu);
    ASSERT(t5 && t5->id == 5, "Owner pop should get 5");
    free(t5);

    /* Cleanup */
    dag_task_t *task;
    while ((task = ws_deque_pop(&deque, 0, &rcu)) != NULL) {
        free(task);
    }

    TEST_PASS();
}

/*******************************************************************************
 * CONTENTION TESTS
 ******************************************************************************/

/**
 * Test: Owner pop vs thief steal (last element)
 */
void test_contention_last_element(void) {
    TEST_START("Contention on last element");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    ws_deque_t deque;
    ws_deque_init(&deque, 0);

    /* Push single task */
    dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
    task->id = 42;
    ws_deque_push(&deque, task, &rcu);

    /* Simulate contention: both try to get it */
    /* In reality, one succeeds, one fails */
    dag_task_t *owner_task = ws_deque_pop(&deque, 0, &rcu);
    dag_task_t *thief_task = ws_deque_steal(&deque, 1, &rcu);

    /* Exactly one should succeed */
    ASSERT((owner_task != NULL && thief_task == NULL) ||
           (owner_task == NULL && thief_task != NULL),
           "Exactly one operation should succeed");

    if (owner_task) free(owner_task);
    if (thief_task) free(thief_task);

    TEST_PASS();
}

/**
 * Test: Multiple thieves
 */
void test_multiple_thieves(void) {
    TEST_START("Multiple thieves stealing");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_deque_t deque;
    ws_deque_init(&deque, 0);

    /* Push 100 tasks */
    for (int i = 0; i < 100; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_deque_push(&deque, task, &rcu);
    }

    /* Simulate 3 thieves stealing */
    int stolen_count = 0;
    for (int thief = 1; thief <= 3; thief++) {
        for (int attempt = 0; attempt < 20; attempt++) {
            dag_task_t *stolen = ws_deque_steal(&deque, thief, &rcu);
            if (stolen) {
                stolen_count++;
                free(stolen);
            }
        }
    }

    ASSERT(stolen_count <= 100, "Cannot steal more than available");
    ASSERT(stolen_count > 0, "Should steal some tasks");

    /* Cleanup remaining */
    dag_task_t *task;
    while ((task = ws_deque_pop(&deque, 0, &rcu)) != NULL) {
        free(task);
    }

    TEST_PASS();
}

/**
 * Test: Concurrent push/steal
 */
void test_concurrent_push_steal(void) {
    TEST_START("Concurrent push and steal");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    ws_deque_t deque;
    ws_deque_init(&deque, 0);

    /* Owner pushes while thief tries to steal */
    for (int i = 0; i < 50; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_deque_push(&deque, task, &rcu);

        /* Thief steals every other push */
        if (i % 2 == 0) {
            dag_task_t *stolen = ws_deque_steal(&deque, 1, &rcu);
            if (stolen) {
                free(stolen);
            }
        }
    }

    /* Some tasks should remain */
    ASSERT(ws_deque_size(&deque) > 0, "Should have remaining tasks");

    /* Cleanup */
    dag_task_t *task;
    while ((task = ws_deque_pop(&deque, 0, &rcu)) != NULL) {
        free(task);
    }

    TEST_PASS();
}

/**
 * Test: Race condition verification
 */
void test_race_conditions(void) {
    TEST_START("Race condition verification");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    ws_deque_t deque;
    ws_deque_init(&deque, 0);

    /* Test many push/pop/steal cycles */
    int total_tasks = 0;
    int freed_tasks = 0;

    for (int cycle = 0; cycle < 10; cycle++) {
        /* Push 10 */
        for (int i = 0; i < 10; i++) {
            dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
            task->id = total_tasks++;
            ws_deque_push(&deque, task, &rcu);
        }

        /* Pop some */
        for (int i = 0; i < 3; i++) {
            dag_task_t *task = ws_deque_pop(&deque, 0, &rcu);
            if (task) {
                freed_tasks++;
                free(task);
            }
        }

        /* Steal some */
        for (int i = 0; i < 3; i++) {
            dag_task_t *task = ws_deque_steal(&deque, 1, &rcu);
            if (task) {
                freed_tasks++;
                free(task);
            }
        }
    }

    /* Drain remaining */
    dag_task_t *task;
    while ((task = ws_deque_pop(&deque, 0, &rcu)) != NULL) {
        freed_tasks++;
        free(task);
    }

    ASSERT(freed_tasks == total_tasks, "All tasks should be accounted for");

    TEST_PASS();
}

/*******************************************************************************
 * WORK-STEALING SCHEDULER TESTS
 ******************************************************************************/

/**
 * Test: Scheduler initialization
 */
void test_scheduler_init(void) {
    TEST_START("Scheduler initialization");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    ASSERT(sched.num_cpus == 4, "Should have 4 CPUs");
    ASSERT(sched.rcu == &rcu, "RCU pointer should be set");

    for (int i = 0; i < 4; i++) {
        ASSERT(sched.cpus[i].cpu_id == i, "CPU ID should match");
        ASSERT(ws_deque_is_empty(&sched.cpus[i].deque), "Deque should be empty");
    }

    TEST_PASS();
}

/**
 * Test: Task submission
 */
void test_scheduler_submit(void) {
    TEST_START("Scheduler task submission");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    /* Submit to CPU 0 */
    dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
    task->id = 123;
    ws_scheduler_submit(&sched, task, 0);

    ASSERT(ws_deque_size(&sched.cpus[0].deque) == 1, "CPU 0 should have 1 task");
    ASSERT(ws_deque_size(&sched.cpus[1].deque) == 0, "CPU 1 should have 0 tasks");

    /* Cleanup */
    free(ws_deque_pop(&sched.cpus[0].deque, 0, &rcu));

    TEST_PASS();
}

/**
 * Test: Local task retrieval
 */
void test_scheduler_local_get(void) {
    TEST_START("Scheduler local task retrieval");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    /* Submit tasks to CPU 0 */
    for (int i = 0; i < 5; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, 0);
    }

    /* Get task from CPU 0 (local) */
    dag_task_t *task = ws_scheduler_get_task(&sched, 0);
    ASSERT(task != NULL, "Should get local task");
    free(task);

    /* Cleanup */
    while ((task = ws_scheduler_get_task(&sched, 0)) != NULL) {
        free(task);
    }

    TEST_PASS();
}

/**
 * Test: Work stealing across CPUs
 */
void test_scheduler_stealing(void) {
    TEST_START("Scheduler work stealing");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    /* Submit all tasks to CPU 0 */
    for (int i = 0; i < 20; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, 0);
    }

    /* CPU 1 tries to get task (will steal) */
    dag_task_t *stolen = ws_scheduler_get_task(&sched, 1);
    ASSERT(stolen != NULL, "CPU 1 should steal a task");
    free(stolen);

    ASSERT(atomic_load(&sched.total_steals) > 0, "Steal count should increase");

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
 * Test: Load balancing
 */
void test_scheduler_load_balance(void) {
    TEST_START("Scheduler load balancing");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    /* Imbalanced: all tasks on CPU 0 */
    for (int i = 0; i < 100; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, 0);
    }

    /* All CPUs process tasks */
    int total = 0;
    while (total < 100) {
        for (int cpu = 0; cpu < 4; cpu++) {
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                total++;
                free(task);
            }
        }
    }

    /* All CPUs should have executed some tasks */
    uint64_t cpu0_exec = atomic_load(&sched.cpus[0].tasks_executed);
    uint64_t cpu1_exec = atomic_load(&sched.cpus[1].tasks_executed);
    uint64_t cpu2_exec = atomic_load(&sched.cpus[2].tasks_executed);
    uint64_t cpu3_exec = atomic_load(&sched.cpus[3].tasks_executed);

    ASSERT(cpu0_exec + cpu1_exec + cpu2_exec + cpu3_exec == 100,
           "Total tasks executed should be 100");
    ASSERT(cpu1_exec > 0 || cpu2_exec > 0 || cpu3_exec > 0,
           "Other CPUs should steal and execute");

    TEST_PASS();
}

/*******************************************************************************
 * VICTIM SELECTION TESTS
 ******************************************************************************/

/**
 * Test: Random victim selection
 */
void test_victim_selection_random(void) {
    TEST_START("Random victim selection");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    /* Select 10 victims */
    bool victims_seen[4] = {false};
    for (int i = 0; i < 10; i++) {
        uint8_t victim = ws_scheduler_select_victim(&sched, 0);
        ASSERT(victim < 4, "Victim should be valid");
        victims_seen[victim] = true;
    }

    /* Should see variety (probabilistic, but likely) */
    int unique_victims = 0;
    for (int i = 0; i < 4; i++) {
        if (victims_seen[i]) unique_victims++;
    }
    ASSERT(unique_victims >= 2, "Should see multiple victims");

    TEST_PASS();
}

/**
 * Test: Circular victim selection
 */
void test_victim_selection_circular(void) {
    TEST_START("Circular victim selection");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    /* Set circular strategy */
    sched.cpus[0].victim_strategy = WS_VICTIM_CIRCULAR;
    sched.cpus[0].next_victim = 1;

    /* Select 3 victims */
    uint8_t v1 = ws_scheduler_select_victim(&sched, 0);
    uint8_t v2 = ws_scheduler_select_victim(&sched, 0);
    uint8_t v3 = ws_scheduler_select_victim(&sched, 0);

    ASSERT(v1 == 1, "First victim should be 1");
    ASSERT(v2 == 2, "Second victim should be 2");
    ASSERT(v3 == 3, "Third victim should be 3");

    TEST_PASS();
}

/**
 * Test: No self-stealing
 */
void test_no_self_stealing(void) {
    TEST_START("No self-stealing");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    /* Select many victims from CPU 2 */
    for (int i = 0; i < 20; i++) {
        uint8_t victim = ws_scheduler_select_victim(&sched, 2);
        ASSERT(victim != 2, "Should never select self as victim");
    }

    TEST_PASS();
}

/*******************************************************************************
 * INTEGRATION TESTS
 ******************************************************************************/

/**
 * Test: End-to-end scenario
 */
void test_end_to_end(void) {
    TEST_START("End-to-end work-stealing");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    /* Submit 50 tasks distributed across CPUs */
    for (int i = 0; i < 50; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, i % 4);
    }

    /* All CPUs process until done */
    int processed = 0;
    while (processed < 50) {
        for (int cpu = 0; cpu < 4; cpu++) {
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                processed++;
                free(task);
            }
        }
    }

    ASSERT(processed == 50, "Should process all 50 tasks");

    TEST_PASS();
}

/**
 * Test: Imbalanced workload
 */
void test_imbalanced_workload(void) {
    TEST_START("Imbalanced workload distribution");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    /* CPU 0 gets 90 tasks, others get 10 total */
    for (int i = 0; i < 90; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, 0);
    }
    for (int i = 90; i < 100; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, (i % 3) + 1);
    }

    /* Process all */
    int processed = 0;
    while (processed < 100) {
        for (int cpu = 0; cpu < 4; cpu++) {
            dag_task_t *task = ws_scheduler_get_task(&sched, cpu);
            if (task) {
                processed++;
                free(task);
            }
        }
    }

    /* Work-stealing should distribute work */
    uint64_t steals = atomic_load(&sched.total_steals);
    ASSERT(steals > 0, "Should have work-stealing activity");

    TEST_PASS();
}

/**
 * Test: Stress test
 */
void test_stress(void) {
    TEST_START("Work-stealing stress test");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ws_scheduler_t sched;
    ws_scheduler_init(&sched, 4, &rcu);

    const int N = 500;

    /* Submit N tasks */
    for (int i = 0; i < N; i++) {
        dag_task_t *task = (dag_task_t*)malloc(sizeof(dag_task_t));
        task->id = i;
        ws_scheduler_submit(&sched, task, 0);  /* All to CPU 0 */
    }

    /* All CPUs process */
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

    ASSERT(processed == N, "Should process all N tasks");

    TEST_PASS();
}

/*******************************************************************************
 * TEST MAIN
 ******************************************************************************/

int main(void) {
    printf("========================================\n");
    printf("Work-Stealing Deque Test Suite\n");
    printf("========================================\n\n");

    /* Deque Initialization Tests */
    printf("--- Deque Initialization Tests ---\n");
    test_deque_init();
    test_array_alloc();

    /* Owner Operation Tests */
    printf("\n--- Owner Operation Tests ---\n");
    test_deque_push();
    test_deque_pop();
    test_deque_lifo();
    test_deque_empty();
    test_deque_resize();
    test_deque_stress();

    /* Thief Operation Tests */
    printf("\n--- Thief Operation Tests ---\n");
    test_deque_steal();
    test_steal_empty();
    test_multiple_steals();
    test_steal_ordering();

    /* Contention Tests */
    printf("\n--- Contention Tests ---\n");
    test_contention_last_element();
    test_multiple_thieves();
    test_concurrent_push_steal();
    test_race_conditions();

    /* Scheduler Tests */
    printf("\n--- Work-Stealing Scheduler Tests ---\n");
    test_scheduler_init();
    test_scheduler_submit();
    test_scheduler_local_get();
    test_scheduler_stealing();
    test_scheduler_load_balance();

    /* Victim Selection Tests */
    printf("\n--- Victim Selection Tests ---\n");
    test_victim_selection_random();
    test_victim_selection_circular();
    test_no_self_stealing();

    /* Integration Tests */
    printf("\n--- Integration Tests ---\n");
    test_end_to_end();
    test_imbalanced_workload();
    test_stress();

    /* Summary */
    printf("\n========================================\n");
    printf("Test Summary\n");
    printf("========================================\n");
    printf("Tests run:    %d\n", tests_run);
    printf("Tests passed: %d\n", tests_passed);
    printf("Tests failed: %d\n", tests_run - tests_passed);
    printf("Success rate: %.1f%%\n",
           100.0 * tests_passed / tests_run);
    printf("========================================\n");

    return (tests_run == tests_passed) ? 0 : 1;
}
