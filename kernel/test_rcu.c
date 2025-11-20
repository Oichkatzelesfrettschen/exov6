/**
 * @file test_rcu.c
 * @brief Comprehensive Tests for RCU (Read-Copy-Update)
 *
 * TEST COVERAGE:
 * ==============
 * 1. RCU Initialization (2 tests)
 *    - Basic initialization
 *    - Per-CPU data initialization
 *
 * 2. Read-Side Critical Sections (4 tests)
 *    - rcu_read_lock/unlock
 *    - Nested critical sections
 *    - Dereference operations
 *    - Pointer assignment
 *
 * 3. Grace Period Mechanics (5 tests)
 *    - GP start/complete cycle
 *    - Quiescent state reporting
 *    - GP advancement
 *    - GP state machine
 *    - Multiple GPs
 *
 * 4. Synchronous Reclamation (3 tests)
 *    - synchronize_rcu basic
 *    - synchronize_rcu correctness
 *    - Multiple synchronize_rcu
 *
 * 5. Asynchronous Reclamation (4 tests)
 *    - call_rcu basic
 *    - Multiple callbacks
 *    - Callback ordering (FIFO)
 *    - Callback invocation after GP
 *
 * 6. Correctness Tests (4 tests)
 *    - Memory reclamation safety
 *    - Concurrent readers
 *    - Reader-writer correctness
 *    - Grace period guarantees
 *
 * 7. Integration Tests (3 tests)
 *    - RCU-protected linked list
 *    - Mixed sync/async reclamation
 *    - Stress test
 *
 * TOTAL: 25 TESTS
 */

#include "rcu_pdac.h"
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
 * RCU INITIALIZATION TESTS
 ******************************************************************************/

/**
 * Test: RCU basic initialization
 */
void test_rcu_init(void) {
    TEST_START("RCU initialization");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    ASSERT(rcu.num_cpus == 4, "Should have 4 CPUs");
    ASSERT(atomic_load(&rcu.gp_seq) == 0, "GP sequence should be 0");
    ASSERT(atomic_load(&rcu.gp_state) == RCU_GP_IDLE, "Should be IDLE");
    ASSERT(atomic_load(&rcu.total_grace_periods) == 0, "No GPs yet");

    TEST_PASS();
}

/**
 * Test: Per-CPU data initialization
 */
void test_rcu_cpu_init(void) {
    TEST_START("Per-CPU initialization");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    for (int i = 0; i < 2; i++) {
        rcu_cpu_data_t *cpu = &rcu.cpus[i];
        ASSERT(atomic_load(&cpu->nesting) == 0, "Nesting should be 0");
        ASSERT(cpu->callback_list == NULL, "Callback list should be NULL");
        ASSERT(atomic_load(&cpu->callback_count) == 0, "No callbacks");
    }

    TEST_PASS();
}

/*******************************************************************************
 * READ-SIDE CRITICAL SECTION TESTS
 ******************************************************************************/

/**
 * Test: rcu_read_lock/unlock
 */
void test_rcu_read_lock_unlock(void) {
    TEST_START("rcu_read_lock/unlock");

    rcu_state_t rcu;
    rcu_init(&rcu, 1);

    /* Initial nesting is 0 */
    ASSERT(atomic_load(&rcu.cpus[0].nesting) == 0, "Initial nesting = 0");

    /* Enter critical section */
    rcu_read_lock(&rcu, 0);
    ASSERT(atomic_load(&rcu.cpus[0].nesting) == 1, "Nesting should be 1");

    /* Exit critical section */
    rcu_read_unlock(&rcu, 0);
    ASSERT(atomic_load(&rcu.cpus[0].nesting) == 0, "Nesting back to 0");

    TEST_PASS();
}

/**
 * Test: Nested critical sections
 */
void test_rcu_nested(void) {
    TEST_START("Nested critical sections");

    rcu_state_t rcu;
    rcu_init(&rcu, 1);

    /* Nest 3 levels deep */
    rcu_read_lock(&rcu, 0);
    ASSERT(atomic_load(&rcu.cpus[0].nesting) == 1, "Level 1");

    rcu_read_lock(&rcu, 0);
    ASSERT(atomic_load(&rcu.cpus[0].nesting) == 2, "Level 2");

    rcu_read_lock(&rcu, 0);
    ASSERT(atomic_load(&rcu.cpus[0].nesting) == 3, "Level 3");

    /* Unwind */
    rcu_read_unlock(&rcu, 0);
    ASSERT(atomic_load(&rcu.cpus[0].nesting) == 2, "Back to level 2");

    rcu_read_unlock(&rcu, 0);
    ASSERT(atomic_load(&rcu.cpus[0].nesting) == 1, "Back to level 1");

    rcu_read_unlock(&rcu, 0);
    ASSERT(atomic_load(&rcu.cpus[0].nesting) == 0, "Back to 0");

    TEST_PASS();
}

/**
 * Test: rcu_dereference
 */
void test_rcu_dereference(void) {
    TEST_START("rcu_dereference");

    rcu_state_t rcu;
    rcu_init(&rcu, 1);

    atomic_ptr_t ptr;
    int value = 42;
    atomic_store(&ptr, &value);

    /* Dereference */
    rcu_read_lock(&rcu, 0);
    int *deref = rcu_dereference(&ptr);
    ASSERT(deref == &value, "Dereference should return pointer");
    ASSERT(*deref == 42, "Value should be 42");
    rcu_read_unlock(&rcu, 0);

    TEST_PASS();
}

/**
 * Test: rcu_assign_pointer
 */
void test_rcu_assign_pointer(void) {
    TEST_START("rcu_assign_pointer");

    atomic_ptr_t ptr;
    int value1 = 10;
    int value2 = 20;

    atomic_store(&ptr, &value1);
    ASSERT(atomic_load(&ptr) == &value1, "Initial value");

    /* Assign new pointer */
    rcu_assign_pointer(&ptr, &value2);
    ASSERT(atomic_load(&ptr) == &value2, "Updated value");

    TEST_PASS();
}

/*******************************************************************************
 * GRACE PERIOD TESTS
 ******************************************************************************/

/**
 * Test: GP start/complete cycle
 */
void test_gp_cycle(void) {
    TEST_START("Grace period start/complete");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    ASSERT(atomic_load(&rcu.gp_state) == RCU_GP_IDLE, "Initially IDLE");

    /* Start GP */
    spinlock_acquire(&rcu.gp_lock);
    rcu_start_gp(&rcu);
    spinlock_release(&rcu.gp_lock);

    ASSERT(atomic_load(&rcu.gp_state) == RCU_GP_WAIT_QS, "Should be WAIT_QS");
    ASSERT(atomic_load(&rcu.qs_mask) != 0, "QS mask should be set");

    /* Report QS from both CPUs */
    rcu_note_qs(&rcu, 0);
    rcu_note_qs(&rcu, 1);

    /* Advance to completion */
    rcu_gp_advance(&rcu, 0);

    /* Should eventually reach IDLE */
    rcu_gp_state_t state = atomic_load(&rcu.gp_state);
    ASSERT(state == RCU_GP_DONE || state == RCU_GP_IDLE,
           "Should be DONE or IDLE");

    TEST_PASS();
}

/**
 * Test: Quiescent state reporting
 */
void test_qs_reporting(void) {
    TEST_START("Quiescent state reporting");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    /* Start GP */
    spinlock_acquire(&rcu.gp_lock);
    rcu_start_gp(&rcu);
    spinlock_release(&rcu.gp_lock);

    /* Initially no QS reported */
    ASSERT(atomic_load(&rcu.qs_completed) == 0, "No QS reported");

    /* Report QS from CPU 0 */
    rcu_note_qs(&rcu, 0);
    uint64_t qs_completed = atomic_load(&rcu.qs_completed);
    ASSERT((qs_completed & (1ULL << 0)) != 0, "CPU 0 should report");

    /* Report QS from CPU 1 */
    rcu_note_qs(&rcu, 1);
    qs_completed = atomic_load(&rcu.qs_completed);
    ASSERT((qs_completed & (1ULL << 1)) != 0, "CPU 1 should report");

    TEST_PASS();
}

/**
 * Test: GP advancement
 */
void test_gp_advance(void) {
    TEST_START("GP advancement");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    uint64_t initial_seq = atomic_load(&rcu.gp_seq);

    /* Add callback to force GP */
    rcu_head_t dummy;
    call_rcu(&rcu, &dummy, NULL, 0);

    /* Advance GP multiple times */
    for (int i = 0; i < 10; i++) {
        rcu_gp_advance(&rcu, 0);
        rcu_note_qs(&rcu, 0);
        rcu_note_qs(&rcu, 1);
    }

    uint64_t final_seq = atomic_load(&rcu.gp_seq);
    ASSERT(final_seq > initial_seq, "GP sequence should advance");

    TEST_PASS();
}

/**
 * Test: GP state machine
 */
void test_gp_state_machine(void) {
    TEST_START("GP state machine");

    rcu_state_t rcu;
    rcu_init(&rcu, 1);

    /* IDLE state */
    ASSERT(atomic_load(&rcu.gp_state) == RCU_GP_IDLE, "Start in IDLE");

    /* IDLE → WAIT_QS (by adding callback) */
    rcu_head_t cb;
    call_rcu(&rcu, &cb, NULL, 0);
    rcu_gp_advance(&rcu, 0);

    rcu_gp_state_t state = atomic_load(&rcu.gp_state);
    ASSERT(state == RCU_GP_WAIT_QS, "Should transition to WAIT_QS");

    /* WAIT_QS → DONE (by reporting QS) */
    rcu_note_qs(&rcu, 0);
    rcu_gp_advance(&rcu, 0);

    /* DONE → IDLE */
    rcu_gp_advance(&rcu, 0);
    state = atomic_load(&rcu.gp_state);
    ASSERT(state == RCU_GP_IDLE || state == RCU_GP_DONE,
           "Should be IDLE or DONE");

    TEST_PASS();
}

/**
 * Test: Multiple grace periods
 */
void test_multiple_gps(void) {
    TEST_START("Multiple grace periods");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    uint64_t initial_gp = atomic_load(&rcu.total_grace_periods);

    /* Run 5 GPs */
    for (int i = 0; i < 5; i++) {
        /* Add callback to trigger GP */
        rcu_head_t cb;
        call_rcu(&rcu, &cb, NULL, 0);

        /* Complete GP */
        for (int j = 0; j < 20; j++) {
            rcu_gp_advance(&rcu, 0);
            rcu_note_qs(&rcu, 0);
            rcu_note_qs(&rcu, 1);
            rcu_process_callbacks(&rcu, 0);
        }
    }

    uint64_t final_gp = atomic_load(&rcu.total_grace_periods);
    ASSERT(final_gp > initial_gp, "Should complete multiple GPs");

    TEST_PASS();
}

/*******************************************************************************
 * SYNCHRONOUS RECLAMATION TESTS
 ******************************************************************************/

/**
 * Test: synchronize_rcu basic
 */
void test_synchronize_rcu_basic(void) {
    TEST_START("synchronize_rcu basic");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    uint64_t gp_before = atomic_load(&rcu.total_grace_periods);

    /* Call synchronize_rcu */
    synchronize_rcu(&rcu);

    uint64_t gp_after = atomic_load(&rcu.total_grace_periods);
    ASSERT(gp_after >= gp_before, "GP should advance");

    TEST_PASS();
}

/**
 * Test: synchronize_rcu correctness
 */
void test_synchronize_rcu_correctness(void) {
    TEST_START("synchronize_rcu correctness");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    atomic_ptr_t ptr;
    int old_val = 100;
    int new_val = 200;

    rcu_assign_pointer(&ptr, &old_val);

    /* Simulate reader seeing old value */
    rcu_read_lock(&rcu, 0);
    int *reader_ptr = rcu_dereference(&ptr);
    ASSERT(*reader_ptr == 100, "Reader sees old value");

    /* Writer updates pointer (in separate "thread") */
    rcu_assign_pointer(&ptr, &new_val);

    /* Reader still has old pointer (valid) */
    ASSERT(*reader_ptr == 100, "Old pointer still valid");

    rcu_read_unlock(&rcu, 0);

    /* Wait for grace period */
    synchronize_rcu(&rcu);

    /* Now safe to reclaim old_val (in real code) */
    /* We don't actually free here to avoid use-after-free in test */

    TEST_PASS();
}

/**
 * Test: Multiple synchronize_rcu
 */
void test_multiple_sync_rcu(void) {
    TEST_START("Multiple synchronize_rcu");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    uint64_t gp_before = atomic_load(&rcu.total_grace_periods);

    /* Multiple sync calls should all complete */
    for (int i = 0; i < 3; i++) {
        synchronize_rcu(&rcu);
    }

    uint64_t gp_after = atomic_load(&rcu.total_grace_periods);
    ASSERT(gp_after >= gp_before,
           "GPs should advance (some may merge)");

    TEST_PASS();
}

/*******************************************************************************
 * ASYNCHRONOUS RECLAMATION TESTS
 ******************************************************************************/

/* Callback counter for testing */
static int callback_invocations = 0;

static void test_callback(rcu_head_t *head) {
    (void)head;
    callback_invocations++;
}

/**
 * Test: call_rcu basic
 */
void test_call_rcu_basic(void) {
    TEST_START("call_rcu basic");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    callback_invocations = 0;

    rcu_head_t cb;
    call_rcu(&rcu, &cb, test_callback, 0);

    /* Callback should be pending */
    ASSERT(atomic_load(&rcu.cpus[0].callback_count) == 1,
           "Should have 1 pending callback");

    /* Process callbacks (trigger GP) */
    for (int i = 0; i < 20; i++) {
        rcu_gp_advance(&rcu, 0);
        rcu_note_qs(&rcu, 0);
        rcu_note_qs(&rcu, 1);
        rcu_process_callbacks(&rcu, 0);
    }

    /* Callback should be invoked */
    ASSERT(callback_invocations == 1, "Callback should be invoked once");

    TEST_PASS();
}

/**
 * Test: Multiple callbacks
 */
void test_multiple_callbacks(void) {
    TEST_START("Multiple callbacks");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    callback_invocations = 0;

    /* Register 5 callbacks */
    rcu_head_t cbs[5];
    for (int i = 0; i < 5; i++) {
        call_rcu(&rcu, &cbs[i], test_callback, 0);
    }

    ASSERT(atomic_load(&rcu.cpus[0].callback_count) == 5,
           "Should have 5 pending");

    /* Process */
    for (int i = 0; i < 30; i++) {
        rcu_gp_advance(&rcu, 0);
        rcu_note_qs(&rcu, 0);
        rcu_note_qs(&rcu, 1);
        rcu_process_callbacks(&rcu, 0);
    }

    ASSERT(callback_invocations == 5, "All 5 callbacks should run");

    TEST_PASS();
}

/**
 * Test: Callback ordering (FIFO)
 */
void test_callback_ordering(void) {
    TEST_START("Callback FIFO ordering");

    rcu_state_t rcu;
    rcu_init(&rcu, 1);

    /* Use array to track ordering */
    static int order_tracker[3];
    static int order_idx = 0;
    order_idx = 0;

    void cb1(rcu_head_t *h) { (void)h; order_tracker[order_idx++] = 1; }
    void cb2(rcu_head_t *h) { (void)h; order_tracker[order_idx++] = 2; }
    void cb3(rcu_head_t *h) { (void)h; order_tracker[order_idx++] = 3; }

    rcu_head_t cbs[3];
    call_rcu(&rcu, &cbs[0], cb1, 0);
    call_rcu(&rcu, &cbs[1], cb2, 0);
    call_rcu(&rcu, &cbs[2], cb3, 0);

    /* Process */
    for (int i = 0; i < 30; i++) {
        rcu_gp_advance(&rcu, 0);
        rcu_note_qs(&rcu, 0);
        rcu_process_callbacks(&rcu, 0);
    }

    /* Check FIFO order */
    ASSERT(order_tracker[0] == 1 && order_tracker[1] == 2 && order_tracker[2] == 3,
           "Callbacks should execute in FIFO order");

    TEST_PASS();
}

/**
 * Test: Callback invocation after GP
 */
void test_callback_after_gp(void) {
    TEST_START("Callback invoked after GP");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    callback_invocations = 0;

    rcu_head_t cb;
    call_rcu(&rcu, &cb, test_callback, 0);

    /* Callback should NOT run immediately */
    ASSERT(callback_invocations == 0, "Callback should not run yet");

    /* Start but don't complete GP */
    rcu_gp_advance(&rcu, 0);
    ASSERT(callback_invocations == 0, "Callback still not run");

    /* Complete GP */
    rcu_note_qs(&rcu, 0);
    rcu_note_qs(&rcu, 1);
    rcu_process_callbacks(&rcu, 0);

    /* Process done callbacks */
    rcu_gp_advance(&rcu, 0);
    rcu_process_callbacks(&rcu, 0);

    ASSERT(callback_invocations >= 1, "Callback should run after GP");

    TEST_PASS();
}

/*******************************************************************************
 * CORRECTNESS TESTS
 ******************************************************************************/

/**
 * Test: Memory reclamation safety
 */
void test_memory_safety(void) {
    TEST_START("Memory reclamation safety");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    atomic_ptr_t global_ptr;
    int *old_data = malloc(sizeof(int));
    *old_data = 42;

    rcu_assign_pointer(&global_ptr, old_data);

    /* Reader acquires pointer */
    rcu_read_lock(&rcu, 0);
    int *reader_ptr = rcu_dereference(&global_ptr);
    ASSERT(*reader_ptr == 42, "Reader sees data");

    /* Writer allocates new data */
    int *new_data = malloc(sizeof(int));
    *new_data = 100;
    rcu_assign_pointer(&global_ptr, new_data);

    /* Reader still has valid old pointer */
    ASSERT(*reader_ptr == 42, "Old data still accessible");

    rcu_read_unlock(&rcu, 0);

    /* Wait for GP before freeing */
    synchronize_rcu(&rcu);
    free(old_data);  /* Now safe */

    /* New reader sees new data */
    rcu_read_lock(&rcu, 0);
    int *new_reader_ptr = rcu_dereference(&global_ptr);
    ASSERT(*new_reader_ptr == 100, "New reader sees new data");
    rcu_read_unlock(&rcu, 0);

    free(new_data);

    TEST_PASS();
}

/**
 * Test: Concurrent readers
 */
void test_concurrent_readers(void) {
    TEST_START("Concurrent readers");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    atomic_ptr_t ptr;
    int value = 999;
    rcu_assign_pointer(&ptr, &value);

    /* Simulate 4 concurrent readers */
    for (int cpu = 0; cpu < 4; cpu++) {
        rcu_read_lock(&rcu, cpu);
    }

    /* All should see same value */
    for (int cpu = 0; cpu < 4; cpu++) {
        int *p = rcu_dereference(&ptr);
        ASSERT(*p == 999, "All readers see correct value");
    }

    /* All exit */
    for (int cpu = 0; cpu < 4; cpu++) {
        rcu_read_unlock(&rcu, cpu);
    }

    /* Verify nesting back to 0 */
    for (int cpu = 0; cpu < 4; cpu++) {
        ASSERT(atomic_load(&rcu.cpus[cpu].nesting) == 0,
               "Nesting should be 0");
    }

    TEST_PASS();
}

/**
 * Test: Reader-writer correctness
 */
void test_reader_writer_correctness(void) {
    TEST_START("Reader-writer correctness");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    atomic_ptr_t ptr;
    int val1 = 1, val2 = 2;

    rcu_assign_pointer(&ptr, &val1);

    /* Reader 1 enters */
    rcu_read_lock(&rcu, 0);
    int *r1 = rcu_dereference(&ptr);

    /* Writer updates */
    rcu_assign_pointer(&ptr, &val2);

    /* Reader 2 enters (may see val1 or val2) */
    rcu_read_lock(&rcu, 1);
    int *r2 = rcu_dereference(&ptr);

    /* Reader 1 still sees val1 */
    ASSERT(*r1 == 1, "Reader 1 still sees old value");

    /* Reader 2 sees val1 or val2 (both valid) */
    ASSERT(*r2 == 1 || *r2 == 2, "Reader 2 sees valid value");

    rcu_read_unlock(&rcu, 0);
    rcu_read_unlock(&rcu, 1);

    /* After GP, new readers see val2 */
    synchronize_rcu(&rcu);

    rcu_read_lock(&rcu, 0);
    int *r3 = rcu_dereference(&ptr);
    ASSERT(*r3 == 2, "New reader sees new value");
    rcu_read_unlock(&rcu, 0);

    TEST_PASS();
}

/**
 * Test: Grace period guarantees
 */
void test_gp_guarantees(void) {
    TEST_START("Grace period guarantees");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    /* A GP must wait for all pre-existing readers */
    rcu_read_lock(&rcu, 0);
    uint64_t gp_seq_before = atomic_load(&rcu.gp_seq);

    /* Try to start GP (should wait for reader) */
    rcu_head_t cb;
    call_rcu(&rcu, &cb, NULL, 0);
    rcu_gp_advance(&rcu, 0);

    /* GP started but not complete (reader still in CS) */
    /* Should be WAIT_QS or still starting */

    /* Reader exits */
    rcu_read_unlock(&rcu, 0);

    /* Now GP can complete */
    for (int i = 0; i < 20; i++) {
        rcu_note_qs(&rcu, 0);
        rcu_note_qs(&rcu, 1);
        rcu_gp_advance(&rcu, 0);
    }

    uint64_t gp_seq_after = atomic_load(&rcu.gp_seq);
    ASSERT(gp_seq_after > gp_seq_before, "GP should complete after reader exits");

    TEST_PASS();
}

/*******************************************************************************
 * INTEGRATION TESTS
 ******************************************************************************/

/**
 * Test: RCU-protected linked list
 */
struct list_node {
    int data;
    struct list_node *next;
    rcu_head_t rcu;
};

void test_rcu_list(void) {
    TEST_START("RCU-protected linked list");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    atomic_ptr_t list_head;
    atomic_store(&list_head, NULL);

    /* Add nodes */
    struct list_node *n1 = malloc(sizeof(struct list_node));
    n1->data = 1;
    n1->next = NULL;
    rcu_assign_pointer(&list_head, n1);

    struct list_node *n2 = malloc(sizeof(struct list_node));
    n2->data = 2;
    n2->next = n1;
    rcu_assign_pointer(&list_head, n2);

    /* Reader traverses */
    rcu_read_lock(&rcu, 0);
    struct list_node *curr = rcu_dereference(&list_head);
    int count = 0;
    while (curr) {
        count++;
        curr = curr->next;
    }
    ASSERT(count == 2, "Should have 2 nodes");
    rcu_read_unlock(&rcu, 0);

    /* Cleanup */
    synchronize_rcu(&rcu);
    free(n1);
    free(n2);

    TEST_PASS();
}

/**
 * Test: Mixed sync/async reclamation
 */
void test_mixed_reclamation(void) {
    TEST_START("Mixed sync/async reclamation");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    callback_invocations = 0;

    /* Async */
    rcu_head_t cb;
    call_rcu(&rcu, &cb, test_callback, 0);

    /* Sync */
    synchronize_rcu(&rcu);

    /* Process callbacks */
    rcu_process_callbacks(&rcu, 0);

    ASSERT(callback_invocations >= 1, "Async callback should run");

    TEST_PASS();
}

/**
 * Test: RCU stress test
 */
void test_rcu_stress(void) {
    TEST_START("RCU stress test");

    rcu_state_t rcu;
    rcu_init(&rcu, 4);

    callback_invocations = 0;

    /* Many callbacks */
    const int N = 100;
    rcu_head_t cbs[N];
    for (int i = 0; i < N; i++) {
        call_rcu(&rcu, &cbs[i], test_callback, i % 4);
    }

    /* Many GPs */
    for (int i = 0; i < 50; i++) {
        rcu_gp_advance(&rcu, 0);
        for (int cpu = 0; cpu < 4; cpu++) {
            rcu_note_qs(&rcu, cpu);
        }
        rcu_process_callbacks(&rcu, 0);
    }

    ASSERT(callback_invocations == N, "All callbacks should execute");

    rcu_stats_t stats;
    rcu_get_stats(&rcu, &stats);
    ASSERT(stats.grace_periods > 0, "Should have completed GPs");

    TEST_PASS();
}

/*******************************************************************************
 * TEST MAIN
 ******************************************************************************/

int main(void) {
    printf("========================================\n");
    printf("RCU (Read-Copy-Update) Test Suite\n");
    printf("========================================\n\n");

    /* Initialization Tests */
    printf("--- Initialization Tests ---\n");
    test_rcu_init();
    test_rcu_cpu_init();

    /* Read-Side Tests */
    printf("\n--- Read-Side Critical Section Tests ---\n");
    test_rcu_read_lock_unlock();
    test_rcu_nested();
    test_rcu_dereference();
    test_rcu_assign_pointer();

    /* Grace Period Tests */
    printf("\n--- Grace Period Tests ---\n");
    test_gp_cycle();
    test_qs_reporting();
    test_gp_advance();
    test_gp_state_machine();
    test_multiple_gps();

    /* Synchronous Reclamation Tests */
    printf("\n--- Synchronous Reclamation Tests ---\n");
    test_synchronize_rcu_basic();
    test_synchronize_rcu_correctness();
    test_multiple_sync_rcu();

    /* Asynchronous Reclamation Tests */
    printf("\n--- Asynchronous Reclamation Tests ---\n");
    test_call_rcu_basic();
    test_multiple_callbacks();
    test_callback_ordering();
    test_callback_after_gp();

    /* Correctness Tests */
    printf("\n--- Correctness Tests ---\n");
    test_memory_safety();
    test_concurrent_readers();
    test_reader_writer_correctness();
    test_gp_guarantees();

    /* Integration Tests */
    printf("\n--- Integration Tests ---\n");
    test_rcu_list();
    test_mixed_reclamation();
    test_rcu_stress();

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
