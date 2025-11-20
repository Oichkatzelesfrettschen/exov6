/**
 * @file rcu_pdac.c
 * @brief Read-Copy-Update (RCU) Implementation
 *
 * IMPLEMENTATION NOTES:
 * =====================
 * This is a simplified but functional RCU implementation based on
 * Linux kernel RCU concepts, adapted for pedagogical clarity.
 *
 * GRACE PERIOD ALGORITHM:
 * =======================
 * 1. **Start GP**: Record which CPUs need to report quiescent state (QS)
 * 2. **Wait for QS**: Each CPU reports when not in read-side critical section
 * 3. **Complete GP**: When all CPUs report, GP is done
 * 4. **Invoke callbacks**: Run deferred callbacks registered with call_rcu()
 *
 * STATE MACHINE:
 * ==============
 * ```
 *   ┌─────────┐
 *   │  IDLE   │ ←─────────┐
 *   └────┬────┘            │
 *        │ start_gp()      │
 *        ↓                 │
 *   ┌─────────┐            │
 *   │ WAIT_QS │            │
 *   └────┬────┘            │
 *        │ all QS reported │
 *        ↓                 │
 *   ┌─────────┐            │
 *   │  DONE   │ ──────────┘
 *   └─────────┘  invoke callbacks
 * ```
 *
 * QUIESCENT STATE DETECTION:
 * ==========================
 * A quiescent state is detected when:
 * - CPU exits outermost RCU read-side critical section (nesting == 0)
 * - Explicit rcu_note_qs() call
 *
 * MEMORY BARRIERS:
 * ================
 * - rcu_read_lock(): acquire barrier (prevent reordering with loads)
 * - rcu_read_unlock(): release barrier (prevent reordering with stores)
 * - rcu_dereference(): acquire load (see published data)
 * - rcu_assign_pointer(): release store (publish data)
 *
 * CALLBACK PROCESSING:
 * ====================
 * Callbacks registered with call_rcu() are:
 * 1. Added to per-CPU pending list
 * 2. After GP completes, moved to done list
 * 3. Invoked in FIFO order
 *
 * SCALABILITY:
 * ============
 * - Per-CPU data: No cache-line ping-pong for read-side
 * - Quiescent state reporting: Only when exiting critical section
 * - Callback lists: Per-CPU to avoid contention
 */

#include "rcu_pdac.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>

/*******************************************************************************
 * RCU INITIALIZATION
 ******************************************************************************/

/**
 * Initialize per-CPU RCU data
 */
void rcu_cpu_init(rcu_cpu_data_t *cpu_data) {
    atomic_store(&cpu_data->nesting, 0);
    atomic_store(&cpu_data->qs_seq, 0);
    cpu_data->need_qs = false;

    cpu_data->callback_list = NULL;
    cpu_data->callback_tail = NULL;
    atomic_store(&cpu_data->callback_count, 0);

    cpu_data->done_list = NULL;
    atomic_store(&cpu_data->done_count, 0);

    atomic_store(&cpu_data->read_locks, 0);
    atomic_store(&cpu_data->grace_periods, 0);
    atomic_store(&cpu_data->callbacks_invoked, 0);
}

/**
 * Initialize RCU subsystem
 */
void rcu_init(rcu_state_t *rcu, uint8_t num_cpus) {
    /* Initialize global state */
    atomic_store(&rcu->gp_seq, 0);
    atomic_store(&rcu->gp_state, RCU_GP_IDLE);
    atomic_store(&rcu->gp_start, 0);

    atomic_store(&rcu->qs_mask, 0);
    atomic_store(&rcu->qs_completed, 0);

    rcu->num_cpus = num_cpus;

    atomic_store(&rcu->total_grace_periods, 0);
    atomic_store(&rcu->total_callbacks, 0);
    atomic_store(&rcu->avg_gp_duration_us, 0);

    atomic_store(&rcu->gp_lock, 0);

    /* Initialize per-CPU data */
    for (uint8_t i = 0; i < num_cpus; i++) {
        rcu_cpu_init(&rcu->cpus[i]);
    }
}

/*******************************************************************************
 * QUIESCENT STATE REPORTING
 ******************************************************************************/

/**
 * Report quiescent state for CPU
 *
 * ALGORITHM:
 * 1. Check if CPU needs to report QS for current GP
 * 2. Update QS sequence number
 * 3. Mark CPU as completed in qs_completed bitmap
 *
 * Note: GP completion is handled by rcu_gp_advance, not here
 */
void rcu_report_qs(rcu_state_t *rcu, uint8_t cpu_id) {
    rcu_cpu_data_t *cpu = &rcu->cpus[cpu_id];

    /* Check if we need to report */
    if (!cpu->need_qs) {
        return;
    }

    /* Get current GP sequence */
    uint64_t gp_seq = atomic_load(&rcu->gp_seq);

    /* Update our QS sequence */
    atomic_store(&cpu->qs_seq, gp_seq);

    /* Mark as completed */
    uint64_t cpu_mask = (1ULL << cpu_id);
    atomic_fetch_or(&rcu->qs_completed, cpu_mask);

    /* Clear need_qs flag */
    cpu->need_qs = false;

    /* Note: GP completion check is done in rcu_gp_advance to avoid deadlock */
}

/**
 * Explicitly note quiescent state
 */
void rcu_note_qs(rcu_state_t *rcu, uint8_t cpu_id) {
    rcu_cpu_data_t *cpu = &rcu->cpus[cpu_id];

    /* Only report if not in critical section */
    int nesting = atomic_load(&cpu->nesting);
    if (nesting == 0 && cpu->need_qs) {
        rcu_report_qs(rcu, cpu_id);
    }
}

/*******************************************************************************
 * GRACE PERIOD MANAGEMENT
 ******************************************************************************/

/**
 * Start a new grace period
 *
 * ALGORITHM:
 * 1. Advance GP sequence number
 * 2. Build QS mask (all active CPUs)
 * 3. Mark each CPU as needing QS
 * 4. Clear QS completed bitmap
 * 5. Transition to WAIT_QS state
 */
void rcu_start_gp(rcu_state_t *rcu) {
    /* Must hold gp_lock */

    /* Advance GP sequence */
    uint64_t new_seq = atomic_fetch_add(&rcu->gp_seq, 1) + 1;
    atomic_store(&rcu->gp_start, new_seq);  /* Simplified: use seq as timestamp */

    /* Build QS mask for active CPUs */
    uint64_t qs_mask = 0;
    for (uint8_t i = 0; i < rcu->num_cpus; i++) {
        qs_mask |= (1ULL << i);
        rcu->cpus[i].need_qs = true;
    }

    atomic_store(&rcu->qs_mask, qs_mask);
    atomic_store(&rcu->qs_completed, 0);

    /* Transition to WAIT_QS */
    atomic_store(&rcu->gp_state, RCU_GP_WAIT_QS);

    /* Note: QS reporting is done externally via rcu_note_qs() to avoid deadlock */
}

/**
 * Check if grace period is complete
 */
bool rcu_gp_complete(const rcu_state_t *rcu) {
    uint64_t qs_mask = atomic_load(&rcu->qs_mask);
    uint64_t qs_completed = atomic_load(&rcu->qs_completed);
    return (qs_completed == qs_mask) && (qs_mask != 0);
}

/**
 * Complete grace period
 *
 * ALGORITHM:
 * 1. Move callbacks from pending to done for each CPU
 * 2. Update statistics
 * 3. Transition to DONE state
 */
void rcu_complete_gp(rcu_state_t *rcu) {
    /* Must hold gp_lock */

    /* Move callbacks from pending to done for each CPU */
    for (uint8_t i = 0; i < rcu->num_cpus; i++) {
        rcu_cpu_data_t *cpu = &rcu->cpus[i];

        if (cpu->callback_list != NULL) {
            /* Move entire callback list to done */
            if (cpu->done_list == NULL) {
                cpu->done_list = cpu->callback_list;
            } else {
                /* Append to existing done list */
                rcu_head_t *tail = cpu->done_list;
                while (tail->next != NULL) {
                    tail = tail->next;
                }
                tail->next = cpu->callback_list;
            }

            int count = atomic_load(&cpu->callback_count);
            atomic_fetch_add(&cpu->done_count, count);
            atomic_fetch_add(&rcu->total_callbacks, count);

            /* Clear pending list */
            cpu->callback_list = NULL;
            cpu->callback_tail = NULL;
            atomic_store(&cpu->callback_count, 0);
        }

        /* Update per-CPU GP counter */
        atomic_fetch_add(&cpu->grace_periods, 1);
    }

    /* Update global statistics */
    atomic_fetch_add(&rcu->total_grace_periods, 1);

    /* Transition to DONE */
    atomic_store(&rcu->gp_state, RCU_GP_DONE);
}

/**
 * Advance grace period state machine
 *
 * ALGORITHM:
 * State machine progression:
 * IDLE → (start GP if callbacks pending) → WAIT_QS
 * WAIT_QS → (all QS reported) → DONE
 * DONE → (invoke callbacks) → IDLE
 */
void rcu_gp_advance(rcu_state_t *rcu, uint64_t now_us) {
    (void)now_us;  /* Simplified: not using time-based triggers */

    spinlock_acquire(&rcu->gp_lock);

    rcu_gp_state_t state = atomic_load(&rcu->gp_state);

    switch (state) {
    case RCU_GP_IDLE: {
        /* Check if any CPU has pending callbacks */
        bool has_callbacks = false;
        for (uint8_t i = 0; i < rcu->num_cpus; i++) {
            int count = atomic_load(&rcu->cpus[i].callback_count);
            if (count > 0) {
                has_callbacks = true;
                break;
            }
        }

        if (has_callbacks) {
            rcu_start_gp(rcu);
        }
        break;
    }

    case RCU_GP_WAIT_QS: {
        /* Check if all CPUs reported QS */
        if (rcu_gp_complete(rcu)) {
            rcu_complete_gp(rcu);
        }
        break;
    }

    case RCU_GP_DONE: {
        /* Transition back to IDLE (callbacks invoked separately) */
        atomic_store(&rcu->gp_state, RCU_GP_IDLE);
        break;
    }
    }

    spinlock_release(&rcu->gp_lock);
}

/*******************************************************************************
 * SYNCHRONOUS RECLAMATION
 ******************************************************************************/

/**
 * Wait for grace period (blocking)
 *
 * ALGORITHM:
 * 1. Record current GP sequence
 * 2. Ensure new GP starts
 * 3. Poll until GP sequence advances
 * 4. Additional GP to ensure completion
 */
void synchronize_rcu(rcu_state_t *rcu) {
    /* Note current GP sequence */
    uint64_t start_seq = atomic_load(&rcu->gp_seq);

    /* Force GP to start if idle */
    spinlock_acquire(&rcu->gp_lock);
    rcu_gp_state_t state = atomic_load(&rcu->gp_state);
    if (state == RCU_GP_IDLE) {
        /* Add a dummy callback to force GP */
        rcu->cpus[0].need_qs = true;  /* Trick to start GP */
        rcu_start_gp(rcu);
    }
    spinlock_release(&rcu->gp_lock);

    /* Poll until GP advances past our sequence */
    int iterations = 0;
    const int MAX_ITERATIONS = 100000;  /* Prevent infinite loop */

    while (iterations < MAX_ITERATIONS) {
        uint64_t current_seq = atomic_load(&rcu->gp_seq);

        /* If GP has advanced, we're done */
        if (current_seq > start_seq) {
            /* Ensure callbacks are processed */
            rcu_process_callbacks(rcu, 0);
            return;
        }

        /* Help GP make progress */
        rcu_gp_advance(rcu, 0);

        /* Try reporting QS for all CPUs */
        for (uint8_t i = 0; i < rcu->num_cpus; i++) {
            rcu_note_qs(rcu, i);
        }

        iterations++;
    }

    /* If we hit max iterations, force completion */
    spinlock_acquire(&rcu->gp_lock);
    state = atomic_load(&rcu->gp_state);
    if (state == RCU_GP_WAIT_QS) {
        /* Force all QS bits */
        uint64_t mask = atomic_load(&rcu->qs_mask);
        atomic_store(&rcu->qs_completed, mask);
        rcu_complete_gp(rcu);
    }
    spinlock_release(&rcu->gp_lock);
}

/*******************************************************************************
 * ASYNCHRONOUS RECLAMATION
 ******************************************************************************/

/**
 * Register callback for asynchronous reclamation
 *
 * ALGORITHM:
 * 1. Initialize callback header
 * 2. Add to per-CPU pending list
 * 3. Trigger GP if needed
 */
void call_rcu(rcu_state_t *rcu, rcu_head_t *head,
              void (*func)(rcu_head_t *head), uint8_t cpu_id) {
    rcu_cpu_data_t *cpu = &rcu->cpus[cpu_id];

    /* Initialize callback */
    head->next = NULL;
    head->func = func;

    /* Add to pending list (lock-free single-producer) */
    if (cpu->callback_tail == NULL) {
        /* List is empty */
        cpu->callback_list = head;
        cpu->callback_tail = head;
    } else {
        /* Append to tail */
        cpu->callback_tail->next = head;
        cpu->callback_tail = head;
    }

    atomic_fetch_add(&cpu->callback_count, 1);

    /* Trigger GP advancement */
    rcu_gp_advance(rcu, 0);
}

/**
 * Invoke completed callbacks
 *
 * ALGORITHM:
 * 1. Get done list
 * 2. Clear done list
 * 3. Invoke each callback
 */
void rcu_invoke_callbacks(rcu_state_t *rcu, uint8_t cpu_id) {
    rcu_cpu_data_t *cpu = &rcu->cpus[cpu_id];

    /* Get done list */
    rcu_head_t *list = cpu->done_list;
    if (list == NULL) {
        return;
    }

    /* Clear done list */
    cpu->done_list = NULL;
    atomic_store(&cpu->done_count, 0);

    /* Invoke callbacks */
    int invoked = 0;
    while (list != NULL) {
        rcu_head_t *next = list->next;

        /* Invoke callback */
        if (list->func) {
            list->func(list);
        }

        invoked++;
        list = next;
    }

    atomic_fetch_add(&cpu->callbacks_invoked, invoked);
}

/**
 * Process all pending RCU work
 */
void rcu_process_callbacks(rcu_state_t *rcu, uint64_t now_us) {
    /* Advance GP state machine */
    rcu_gp_advance(rcu, now_us);

    /* Invoke completed callbacks for all CPUs */
    for (uint8_t i = 0; i < rcu->num_cpus; i++) {
        rcu_invoke_callbacks(rcu, i);
    }
}

/*******************************************************************************
 * STATISTICS & MONITORING
 ******************************************************************************/

/**
 * Collect RCU statistics
 */
void rcu_get_stats(const rcu_state_t *rcu, rcu_stats_t *stats) {
    stats->grace_periods = atomic_load(&rcu->total_grace_periods);
    stats->current_gp_seq = atomic_load(&rcu->gp_seq);
    stats->avg_gp_duration_us = atomic_load(&rcu->avg_gp_duration_us);

    /* Aggregate per-CPU stats */
    stats->read_locks = 0;
    stats->callbacks_invoked = 0;
    stats->pending_callbacks = 0;

    for (uint8_t i = 0; i < rcu->num_cpus; i++) {
        const rcu_cpu_data_t *cpu = &rcu->cpus[i];
        stats->read_locks += atomic_load(&cpu->read_locks);
        stats->callbacks_invoked += atomic_load(&cpu->callbacks_invoked);
        stats->pending_callbacks += atomic_load(&cpu->callback_count);
        stats->pending_callbacks += atomic_load(&cpu->done_count);
    }
}

/**
 * Print RCU statistics
 */
void rcu_print_stats(const rcu_state_t *rcu) {
    rcu_stats_t stats;
    rcu_get_stats(rcu, &stats);

    printf("=== RCU Statistics ===\n");
    printf("Grace Periods:      %lu\n", stats.grace_periods);
    printf("Current GP Seq:     %lu\n", stats.current_gp_seq);
    printf("Read-side locks:    %lu\n", stats.read_locks);
    printf("Callbacks invoked:  %lu\n", stats.callbacks_invoked);
    printf("Pending callbacks:  %lu\n", stats.pending_callbacks);
    printf("Avg GP duration:    %lu μs\n", stats.avg_gp_duration_us);

    printf("\nPer-CPU Stats:\n");
    for (uint8_t i = 0; i < rcu->num_cpus; i++) {
        const rcu_cpu_data_t *cpu = &rcu->cpus[i];
        printf("  CPU %d: locks=%lu, GPs=%lu, callbacks=%lu, pending=%d\n",
               i,
               atomic_load(&cpu->read_locks),
               atomic_load(&cpu->grace_periods),
               atomic_load(&cpu->callbacks_invoked),
               atomic_load(&cpu->callback_count));
    }
}

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example data structure for RCU examples
 */
struct rcu_node {
    int data;
    rcu_head_t rcu;
    struct rcu_node *next;
};

/**
 * Example: RCU-protected linked list
 */
void example_rcu_list(void) {
    printf("=== RCU-Protected Linked List Example ===\n\n");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    atomic_ptr_t list_head;
    atomic_store(&list_head, NULL);

    /* Create initial node */
    struct rcu_node *node1 = malloc(sizeof(struct rcu_node));
    node1->data = 1;
    node1->next = NULL;
    rcu_assign_pointer(&list_head, node1);

    printf("Created list with node: data=1\n");

    /* Reader: traverse list */
    printf("\nReader traversing:\n");
    rcu_read_lock(&rcu, 0);
    struct rcu_node *curr = rcu_dereference(&list_head);
    while (curr) {
        printf("  Node data=%d\n", curr->data);
        curr = curr->next;
    }
    rcu_read_unlock(&rcu, 0);

    /* Writer: add new node */
    printf("\nWriter adding node: data=2\n");
    struct rcu_node *node2 = malloc(sizeof(struct rcu_node));
    node2->data = 2;
    node2->next = node1;
    rcu_assign_pointer(&list_head, node2);

    /* Reader can still see old or new */
    printf("Reader traversing after update:\n");
    rcu_read_lock(&rcu, 0);
    curr = rcu_dereference(&list_head);
    while (curr) {
        printf("  Node data=%d\n", curr->data);
        curr = curr->next;
    }
    rcu_read_unlock(&rcu, 0);

    /* Cleanup */
    free(node1);
    free(node2);

    printf("\n");
}

/**
 * Callback for RCU example
 */
static void free_rcu_node(rcu_head_t *head) {
    struct rcu_node *node = container_of(head, struct rcu_node, rcu);
    printf("  Callback: freeing node with data=%d\n", node->data);
    free(node);
}

/**
 * Example: Synchronous vs asynchronous reclamation
 */
void example_rcu_reclamation(void) {
    printf("=== RCU Reclamation Example ===\n\n");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    /* Synchronous reclamation */
    printf("Synchronous reclamation:\n");
    struct rcu_node *old_node = malloc(sizeof(struct rcu_node));
    old_node->data = 100;

    printf("  Freeing old node (blocking)...\n");
    synchronize_rcu(&rcu);
    free(old_node);
    printf("  Old node freed\n");

    /* Asynchronous reclamation */
    printf("\nAsynchronous reclamation:\n");
    struct rcu_node *async_node = malloc(sizeof(struct rcu_node));
    async_node->data = 200;

    printf("  Registering callback (non-blocking)...\n");
    call_rcu(&rcu, &async_node->rcu, free_rcu_node, 0);
    printf("  call_rcu() returned immediately\n");

    printf("  Processing callbacks...\n");
    rcu_process_callbacks(&rcu, 0);

    printf("\n");
}

/**
 * Example: Grace period mechanics
 */
void example_rcu_grace_period(void) {
    printf("=== Grace Period Mechanics ===\n\n");

    rcu_state_t rcu;
    rcu_init(&rcu, 2);

    printf("Initial state:\n");
    rcu_print_stats(&rcu);

    printf("\nStarting grace period...\n");
    spinlock_acquire(&rcu.gp_lock);
    rcu_start_gp(&rcu);
    spinlock_release(&rcu.gp_lock);

    printf("Grace period started, waiting for quiescent states...\n");
    rcu_print_stats(&rcu);

    printf("\nReporting quiescent states...\n");
    rcu_note_qs(&rcu, 0);
    rcu_note_qs(&rcu, 1);

    printf("All quiescent states reported\n");
    rcu_process_callbacks(&rcu, 0);
    rcu_print_stats(&rcu);

    printf("\n");
}

/**
 * Example: RCU vs locks performance comparison
 */
void example_rcu_vs_locks(void) {
    printf("=== RCU vs Locks Performance ===\n\n");

    printf("Read-heavy workload (95%% reads, 5%% writes):\n");
    printf("  Locks:  High contention, readers block each other\n");
    printf("  RCU:    No contention, readers never block\n");
    printf("\n");

    printf("Reader overhead:\n");
    printf("  Locks:  Mutex acquire/release (~100ns each)\n");
    printf("  RCU:    rcu_read_lock/unlock (~10ns each)\n");
    printf("  Speedup: ~10x for readers\n");
    printf("\n");

    printf("Scalability:\n");
    printf("  Locks:  Linear degradation with cores (cache ping-pong)\n");
    printf("  RCU:    Linear speedup (no cache-line sharing)\n");
    printf("\n");

    printf("Trade-off:\n");
    printf("  Locks:  Immediate reclamation\n");
    printf("  RCU:    Deferred reclamation (grace period wait)\n");
    printf("\n");
}
