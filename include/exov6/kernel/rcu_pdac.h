#pragma once

/**
 * @file rcu_pdac.h
 * @brief Read-Copy-Update (RCU) Synchronization for PDAC Phase 5
 *
 * PEDAGOGICAL PURPOSE:
 * ====================
 * RCU is one of the most elegant and powerful synchronization mechanisms,
 * enabling lock-free reads in read-mostly workloads. This implementation
 * demonstrates the core RCU concepts used in the Linux kernel.
 *
 * KEY CONCEPTS:
 * =============
 * **Read-Copy-Update**: Synchronization technique for read-mostly data
 * - Readers: Lock-free, wait-free, just mark critical section
 * - Writers: Copy data, modify copy, atomically update pointer
 * - Reclamation: Deferred until all readers finish (grace period)
 *
 * **Grace Period**: Time during which all pre-existing readers complete
 * - After grace period: safe to reclaim old memory
 * - Guaranteed by tracking per-CPU quiescent states
 *
 * **Quiescent State**: Point where CPU is not in RCU read-side critical section
 * - Context switch (scheduler tick)
 * - Idle loop entry
 * - User-mode execution
 * - Explicit quiescent state report
 *
 * **RCU API**:
 * ```c
 * // Reader side (lock-free!)
 * rcu_read_lock();
 * ptr = rcu_dereference(global_ptr);  // Load with acquire semantics
 * use(ptr);
 * rcu_read_unlock();
 *
 * // Writer side
 * new_ptr = malloc(...);
 * copy_and_modify(new_ptr, old_ptr);
 * rcu_assign_pointer(global_ptr, new_ptr);  // Atomic publish
 * synchronize_rcu();  // Wait for grace period
 * free(old_ptr);      // Now safe to reclaim
 * ```
 *
 * REAL-WORLD ANALOGUES:
 * =====================
 * - **Linux Kernel RCU**: Millions of reads/sec in networking, filesystems
 * - **userspace RCU (liburcu)**: High-performance userspace RCU library
 * - **Facebook Folly**: RCU-like mechanisms for lock-free data structures
 * - **DPDK**: RCU for packet processing pipelines
 *
 * PERFORMANCE CHARACTERISTICS:
 * ===========================
 * - **Reader overhead**: ~2 atomic increments (enter/exit critical section)
 * - **Reader latency**: O(1), wait-free (bounded steps)
 * - **Writer latency**: O(N) where N = number of CPUs (grace period)
 * - **Scalability**: Linear with CPUs (no cache-line ping-pong)
 *
 * GRACE PERIOD DETECTION:
 * =======================
 * Our implementation uses **quiescent-state-based** detection:
 *
 * 1. Record active CPUs at start of grace period
 * 2. Each CPU reports quiescent state (not in read-side critical section)
 * 3. When all CPUs report, grace period complete
 *
 * Algorithm (simplified):
 * ```
 * start_gp():
 *   for each cpu:
 *     cpu_mask[cpu] = 1  // Need quiescent state
 *
 * report_qs(cpu):
 *   cpu_mask[cpu] = 0  // This CPU is done
 *   if all bits 0:
 *     complete_gp()  // Grace period done!
 * ```
 *
 * MEMORY RECLAMATION:
 * ===================
 * Two approaches:
 *
 * 1. **synchronize_rcu()**: Blocking, waits for grace period
 *    - Simple, synchronous
 *    - Can stall writer thread
 *
 * 2. **call_rcu()**: Asynchronous callback
 *    - Non-blocking, registers callback
 *    - Callback invoked after grace period
 *    - More complex but higher performance
 *
 * COMPARISON WITH HAZARD POINTERS:
 * =================================
 * | Aspect           | RCU                  | Hazard Pointers        |
 * |------------------|----------------------|------------------------|
 * | Read overhead    | 2 atomic ops         | 3-4 atomic ops + loop  |
 * | Write overhead   | Grace period wait    | Scan retired list      |
 * | Memory usage     | Deferred callbacks   | Retire lists           |
 * | Best for         | Read-mostly          | Balanced read/write    |
 * | Readers per obj  | Unlimited            | Limited (HP count)     |
 * | Linux usage      | Extensive (network,  | Not used (userspace    |
 * |                  | scheduler, VFS)      | libraries only)        |
 *
 * CLASSIC RCU EXAMPLE: Linked List Update
 * ========================================
 * ```c
 * // Before: A → B → C
 * // After:  A → D → C  (remove B)
 *
 * // Reader (lock-free!)
 * rcu_read_lock();
 * list_for_each_entry_rcu(node, &list, link) {
 *     process(node);  // B might disappear, but pointer stays valid!
 * }
 * rcu_read_unlock();
 *
 * // Writer
 * D = alloc_node();
 * rcu_assign_pointer(A->next, D);  // Publish D
 * rcu_assign_pointer(D->next, C);  // Link to C
 * synchronize_rcu();  // Wait for readers seeing B to finish
 * free(B);  // Now safe
 * ```
 */

#include "types.h"
#include "lockfree.h"
#include <stdatomic.h>
#include <stdbool.h>

/*******************************************************************************
 * CONFIGURATION
 ******************************************************************************/

/**
 * Maximum number of CPUs supported by RCU
 */
#define RCU_MAX_CPUS 64

/**
 * Maximum pending callbacks per CPU
 */
#define RCU_MAX_CALLBACKS 1000

/**
 * Grace period number type (64-bit for overflow safety)
 */
typedef uint64_t rcu_gp_t;

/*******************************************************************************
 * PER-CPU RCU STATE
 ******************************************************************************/

/**
 * RCU callback
 */
typedef struct rcu_head {
    struct rcu_head *next;
    void (*func)(struct rcu_head *head);
} rcu_head_t;

_Static_assert(sizeof(struct rcu_head) == 16, "struct rcu_head size mismatch");

/**
 * Per-CPU RCU data
 */
typedef struct rcu_cpu_data {
    /* Read-side nesting counter (0 = not in critical section) */
    atomic_int_t nesting;

    /* Quiescent state tracking */
    atomic_uint64_t qs_seq;         /* Last reported QS sequence */
    bool need_qs;                    /* Need to report QS for current GP */

    /* Callback lists */
    rcu_head_t *callback_list;       /* Pending callbacks */
    rcu_head_t *callback_tail;       /* Tail of callback list */
    atomic_int_t callback_count;     /* Number of pending callbacks */

    /* Done callbacks (ready to invoke after GP) */
    rcu_head_t *done_list;
    atomic_int_t done_count;

    /* Statistics */
    atomic_uint64_t read_locks;      /* Read-side lock count */
    atomic_uint64_t grace_periods;   /* GPs participated in */
    atomic_uint64_t callbacks_invoked; /* Callbacks executed */
} rcu_cpu_data_t;

_Static_assert(sizeof(struct rcu_cpu_data) == 88, "struct rcu_cpu_data size mismatch");

/*******************************************************************************
 * GLOBAL RCU STATE
 ******************************************************************************/

/**
 * Grace period states
 */
typedef enum {
    RCU_GP_IDLE,       /* No grace period in progress */
    RCU_GP_WAIT_QS,    /* Waiting for quiescent states */
    RCU_GP_DONE        /* Grace period complete, processing callbacks */
} rcu_gp_state_t;

/**
 * Global RCU state
 */
typedef struct rcu_state {
    /* Grace period tracking */
    atomic_uint64_t gp_seq;          /* Current grace period sequence */
    atomic_int_t gp_state;           /* Current GP state */
    atomic_uint64_t gp_start;        /* GP start time (microseconds) */

    /* Quiescent state tracking (bitmap) */
    atomic_uint64_t qs_mask;         /* CPUs that need to report QS */
    atomic_uint64_t qs_completed;    /* CPUs that reported QS */

    /* Per-CPU data */
    rcu_cpu_data_t cpus[RCU_MAX_CPUS];
    uint8_t num_cpus;

    /* Global statistics */
    atomic_uint64_t total_grace_periods;
    atomic_uint64_t total_callbacks;
    atomic_uint64_t avg_gp_duration_us;

    /* Synchronization for GP advancement */
    atomic_int_t gp_lock;            /* Simple spinlock for GP state machine */
} rcu_state_t;

_Static_assert(sizeof(struct rcu_state) == 5712, "struct rcu_state size mismatch");

/*******************************************************************************
 * RCU INITIALIZATION
 ******************************************************************************/

/**
 * Initialize RCU subsystem
 *
 * @param rcu       RCU state
 * @param num_cpus  Number of CPUs
 */
void rcu_init(rcu_state_t *rcu, uint8_t num_cpus);

/**
 * Initialize per-CPU RCU data
 *
 * @param cpu_data  Per-CPU data to initialize
 */
void rcu_cpu_init(rcu_cpu_data_t *cpu_data);

/*******************************************************************************
 * FORWARD DECLARATIONS
 ******************************************************************************/

void rcu_report_qs(rcu_state_t *rcu, uint8_t cpu_id);

/* Simple spinlock helpers (for internal use and testing) */
static inline void spinlock_acquire(atomic_int_t *lock) {
    int expected = 0;
    while (!atomic_compare_exchange_weak(lock, &expected, 1)) {
        expected = 0;
    }
}

static inline void spinlock_release(atomic_int_t *lock) {
    atomic_store(lock, 0);
}

/*******************************************************************************
 * READ-SIDE CRITICAL SECTIONS (Lock-Free!)
 ******************************************************************************/

/**
 * Enter RCU read-side critical section
 *
 * IMPLEMENTATION:
 * - Increment per-CPU nesting counter
 * - Memory barrier to prevent reordering
 *
 * COST: ~1-2 atomic increment
 *
 * @param rcu     RCU state
 * @param cpu_id  Current CPU ID
 */
static inline void rcu_read_lock(rcu_state_t *rcu, uint8_t cpu_id) {
    rcu_cpu_data_t *cpu = &rcu->cpus[cpu_id];
    atomic_fetch_add_explicit(&cpu->nesting, 1, memory_order_acquire);
    atomic_fetch_add_explicit(&cpu->read_locks, 1, memory_order_relaxed);
}

/**
 * Exit RCU read-side critical section
 *
 * IMPLEMENTATION:
 * - Decrement per-CPU nesting counter
 * - If nesting reaches 0 and QS needed, report QS
 *
 * @param rcu     RCU state
 * @param cpu_id  Current CPU ID
 */
static inline void rcu_read_unlock(rcu_state_t *rcu, uint8_t cpu_id) {
    rcu_cpu_data_t *cpu = &rcu->cpus[cpu_id];
    int old_nesting = atomic_fetch_sub_explicit(&cpu->nesting, 1,
                                                  memory_order_release);

    /* If exiting outermost critical section and QS needed, report it */
    if (old_nesting == 1 && cpu->need_qs) {
        rcu_report_qs(rcu, cpu_id);
    }
}

/**
 * Dereference RCU-protected pointer
 *
 * IMPLEMENTATION:
 * - Load pointer with acquire semantics
 * - Ensures subsequent loads see published data
 *
 * USAGE:
 * ```c
 * rcu_read_lock(rcu, cpu_id);
 * struct foo *p = rcu_dereference(rcu, global_ptr);
 * use(p);
 * rcu_read_unlock(rcu, cpu_id);
 * ```
 *
 * @param ptr  Atomic pointer to dereference
 * @return     Dereferenced value
 */
#define rcu_dereference(ptr) \
    atomic_load_explicit(ptr, memory_order_acquire)

/**
 * Assign RCU-protected pointer
 *
 * IMPLEMENTATION:
 * - Store pointer with release semantics
 * - Ensures prior modifications visible to readers
 *
 * USAGE:
 * ```c
 * new_data = alloc_and_init();
 * rcu_assign_pointer(&global_ptr, new_data);
 * synchronize_rcu(rcu);
 * free(old_data);
 * ```
 *
 * @param ptr   Atomic pointer to assign
 * @param val   New value
 */
#define rcu_assign_pointer(ptr, val) \
    atomic_store_explicit(ptr, val, memory_order_release)

/*******************************************************************************
 * QUIESCENT STATE REPORTING
 ******************************************************************************/

/**
 * Report quiescent state for CPU
 *
 * Called when CPU is known to be outside read-side critical section.
 *
 * @param rcu     RCU state
 * @param cpu_id  CPU reporting QS
 */
void rcu_report_qs(rcu_state_t *rcu, uint8_t cpu_id);

/**
 * Note quiescent state (explicit)
 *
 * Manually report that this CPU is in a quiescent state.
 * Use between work items to help grace periods complete faster.
 *
 * @param rcu     RCU state
 * @param cpu_id  Current CPU ID
 */
void rcu_note_qs(rcu_state_t *rcu, uint8_t cpu_id);

/*******************************************************************************
 * GRACE PERIOD MANAGEMENT
 ******************************************************************************/

/**
 * Start a new grace period
 *
 * Initializes QS mask and begins tracking.
 *
 * @param rcu  RCU state
 */
void rcu_start_gp(rcu_state_t *rcu);

/**
 * Check if grace period is complete
 *
 * @param rcu  RCU state
 * @return     True if all CPUs reported QS
 */
bool rcu_gp_complete(const rcu_state_t *rcu);

/**
 * Complete grace period
 *
 * Moves callbacks from pending to done, ready for invocation.
 *
 * @param rcu  RCU state
 */
void rcu_complete_gp(rcu_state_t *rcu);

/**
 * Advance grace period state machine
 *
 * Called periodically to drive GP progress.
 *
 * @param rcu       RCU state
 * @param now_us    Current time (microseconds)
 */
void rcu_gp_advance(rcu_state_t *rcu, uint64_t now_us);

/*******************************************************************************
 * SYNCHRONOUS RECLAMATION
 ******************************************************************************/

/**
 * Wait for grace period (blocking)
 *
 * ALGORITHM:
 * 1. Note current GP sequence
 * 2. Start new GP if needed
 * 3. Poll until GP advances past noted sequence
 *
 * USAGE:
 * ```c
 * old_ptr = global_ptr;
 * rcu_assign_pointer(&global_ptr, new_ptr);
 * synchronize_rcu(rcu);
 * free(old_ptr);  // Safe now
 * ```
 *
 * @param rcu  RCU state
 */
void synchronize_rcu(rcu_state_t *rcu);

/*******************************************************************************
 * ASYNCHRONOUS RECLAMATION
 ******************************************************************************/

/**
 * Register callback for asynchronous reclamation
 *
 * ALGORITHM:
 * 1. Add callback to per-CPU pending list
 * 2. After next GP, callback invoked
 * 3. Callback can free memory
 *
 * USAGE:
 * ```c
 * void my_free_func(rcu_head_t *head) {
 *     struct foo *p = container_of(head, struct foo, rcu);
 *     free(p);
 * }
 *
 * rcu_assign_pointer(&global_ptr, new_ptr);
 * call_rcu(rcu, &old_ptr->rcu, my_free_func, cpu_id);
 * // Returns immediately, my_free_func called after GP
 * ```
 *
 * @param rcu      RCU state
 * @param head     RCU callback header
 * @param func     Callback function
 * @param cpu_id   Current CPU ID
 */
void call_rcu(rcu_state_t *rcu, rcu_head_t *head,
              void (*func)(rcu_head_t *head), uint8_t cpu_id);

/**
 * Invoke completed callbacks
 *
 * Called after GP completes to run callbacks.
 *
 * @param rcu     RCU state
 * @param cpu_id  CPU to process callbacks for
 */
void rcu_invoke_callbacks(rcu_state_t *rcu, uint8_t cpu_id);

/**
 * Process all pending work
 *
 * Advances GP and invokes callbacks. Call periodically.
 *
 * @param rcu     RCU state
 * @param now_us  Current time (microseconds)
 */
void rcu_process_callbacks(rcu_state_t *rcu, uint64_t now_us);

/*******************************************************************************
 * STATISTICS & MONITORING
 ******************************************************************************/

/**
 * Get RCU statistics
 */
typedef struct rcu_stats {
    uint64_t grace_periods;       /* Total GPs completed */
    uint64_t callbacks_invoked;   /* Total callbacks executed */
    uint64_t read_locks;          /* Total read-side locks */
    uint64_t avg_gp_duration_us;  /* Average GP duration */
    uint64_t pending_callbacks;   /* Callbacks waiting for GP */
    uint64_t current_gp_seq;      /* Current GP sequence */
} rcu_stats_t;

/**
 * Collect RCU statistics
 *
 * @param rcu    RCU state
 * @param stats  Output statistics
 */
void rcu_get_stats(const rcu_state_t *rcu, rcu_stats_t *stats);

/**
 * Print RCU statistics
 *
 * @param rcu  RCU state
 */
void rcu_print_stats(const rcu_state_t *rcu);

/*******************************************************************************
 * UTILITY MACROS
 ******************************************************************************/

/**
 * Get container structure from rcu_head
 *
 * USAGE:
 * ```c
 * struct foo {
 *     int data;
 *     rcu_head_t rcu;
 * };
 *
 * void free_foo(rcu_head_t *head) {
 *     struct foo *p = container_of(head, struct foo, rcu);
 *     free(p);
 * }
 * ```
 */
#define container_of(ptr, type, member) \
    ((type *)((char *)(ptr) - offsetof(type, member)))

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: RCU-protected linked list
 */
void example_rcu_list(void);

/**
 * Example: Synchronous vs asynchronous reclamation
 */
void example_rcu_reclamation(void);

/**
 * Example: Grace period mechanics
 */
void example_rcu_grace_period(void);

/**
 * Example: RCU vs locks performance
 */
void example_rcu_vs_locks(void);
