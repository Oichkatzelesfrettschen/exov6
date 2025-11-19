#pragma once

/**
 * @file work_stealing.h
 * @brief Chase-Lev Work-Stealing Deque for PDAC Phase 5.3
 *
 * PEDAGOGICAL PURPOSE:
 * ====================
 * Work-stealing is a fundamental load-balancing technique used in parallel
 * runtime systems. This implementation is based on the Chase-Lev deque,
 * which provides optimal performance characteristics:
 *
 * - **Owner operations (push/pop)**: Wait-free, O(1), no atomics in common case
 * - **Thief operations (steal)**: Lock-free, O(1), minimal contention
 * - **Dynamic resizing**: Automatic array growth when needed
 *
 * CLASSIC PAPER:
 * ==============
 * "Dynamic Circular Work-Stealing Deque"
 * David Chase and Yossi Lev, SPAA 2005
 *
 * KEY INSIGHT:
 * ============
 * The Chase-Lev deque exploits the observation that:
 * - **Owner** always operates at the BOTTOM (most recent end)
 * - **Thieves** always operate at the TOP (oldest end)
 * - This separation minimizes contention
 *
 * ALGORITHM OVERVIEW:
 * ===================
 * ```
 * Deque: [T1][T2][T3][T4][T5]
 *         ^top              ^bottom (owner's end)
 *
 * Owner push:    Add at bottom (no atomic!)
 * Owner pop:     Remove from bottom (fast path: no atomic)
 * Thief steal:   Remove from top (atomic CAS)
 *
 * Contention case: Owner pop vs Thief steal on last element
 * → Resolved via atomic CAS on top
 * ```
 *
 * REAL-WORLD USAGE:
 * =================
 * - **Intel TBB**: Task scheduler uses Chase-Lev deques
 * - **Go Runtime**: Goroutine scheduler has work-stealing with similar design
 * - **Java ForkJoinPool**: Uses variant of Chase-Lev deque
 * - **Cilk**: Original work-stealing runtime (Blumofe & Leiserson, 1999)
 * - **Rust Rayon**: Data parallelism library with work-stealing
 *
 * PERFORMANCE CHARACTERISTICS:
 * ============================
 * | Operation      | Latency | Atomics | Contention |
 * |----------------|---------|---------|------------|
 * | push (owner)   | ~10ns   | 0       | None       |
 * | pop (owner)    | ~20ns   | 0-1     | Low        |
 * | steal (thief)  | ~50ns   | 2-3     | Medium     |
 * | resize         | ~1μs    | Many    | High       |
 *
 * CORRECTNESS PROPERTIES:
 * =======================
 * 1. **Wait-free owner**: Owner always makes progress (bounded steps)
 * 2. **Lock-free thieves**: At least one thief makes progress
 * 3. **Linearizable**: Operations appear atomic at linearization point
 * 4. **Memory safe**: No use-after-free via hazard pointers/RCU
 *
 * WORK-STEALING SCHEDULER:
 * ========================
 * ```c
 * // Owner (worker thread)
 * while (true) {
 *     task = ws_deque_pop(my_deque);
 *     if (task) {
 *         execute(task);
 *     } else {
 *         // Local queue empty, try stealing
 *         victim = select_random_victim();
 *         task = ws_deque_steal(victim->deque);
 *         if (task) {
 *             execute(task);
 *         } else {
 *             // All queues empty, idle or terminate
 *         }
 *     }
 * }
 * ```
 *
 * VICTIM SELECTION STRATEGIES:
 * ============================
 * 1. **Random**: Pick random victim (simple, good cache locality)
 * 2. **Circular**: Round-robin through victims (predictable, fair)
 * 3. **Affinity-aware**: Prefer nearby CPUs (NUMA-aware)
 * 4. **Adaptive**: Learn which victims have work (overhead)
 *
 * COMPARISON WITH OTHER SCHEDULERS:
 * ==================================
 * | Scheduler      | Load Balance | Locality | Overhead | Best For        |
 * |----------------|--------------|----------|----------|-----------------|
 * | Work-Stealing  | Automatic    | High     | Low      | Irregular tasks |
 * | Lottery        | Manual       | Medium   | Medium   | Fairness        |
 * | Beatty         | Fixed        | High     | Low      | Deterministic   |
 * | Work-Sharing   | Proactive    | Low      | High     | Regular tasks   |
 *
 * INTEGRATION WITH PDAC:
 * ======================
 * Work-stealing complements PDAC's existing schedulers:
 * - Use work-stealing for dynamic load balancing
 * - Use lottery/Beatty for fairness/determinism within CPU
 * - Use admission control for global resource management
 * - Use RCU for lock-free cross-CPU stealing
 */

#include "types.h"
#include "dag_pdac.h"
#include "lockfree.h"
#include "rcu_pdac.h"
#include <stdatomic.h>
#include <stdbool.h>

/*******************************************************************************
 * CONFIGURATION
 ******************************************************************************/

/**
 * Initial deque capacity (must be power of 2)
 */
#define WS_DEQUE_INITIAL_CAPACITY 256

/**
 * Maximum deque capacity
 */
#define WS_DEQUE_MAX_CAPACITY (1 << 20)  /* 1M tasks */

/**
 * Maximum number of CPUs for work-stealing
 */
#define WS_MAX_CPUS 64

/**
 * Number of steal attempts before declaring idle
 */
#define WS_STEAL_ATTEMPTS 4

/*******************************************************************************
 * CHASE-LEV DEQUE STRUCTURES
 ******************************************************************************/

/**
 * Circular array for deque storage
 *
 * IMPLEMENTATION NOTE:
 * The array is dynamically resizable. When full, we allocate a new
 * array of double size and copy elements. Old array is reclaimed
 * via RCU to ensure thieves don't access freed memory.
 */
typedef struct ws_array {
    size_t capacity;          /* Power of 2 */
    size_t mask;              /* capacity - 1 (for fast modulo) */
    dag_task_t **tasks;       /* Task pointers */
    rcu_head_t rcu;           /* For RCU reclamation */
} ws_array_t;

/**
 * Chase-Lev work-stealing deque
 *
 * ALGORITHM:
 * - top: Atomic, accessed by thieves (CAS for steal)
 * - bottom: Non-atomic, accessed only by owner
 * - array: RCU-protected, can be replaced during resize
 *
 * INVARIANT: top <= bottom
 * - Empty: top == bottom
 * - One element: bottom - top == 1
 * - Multiple elements: bottom - top > 1
 */
typedef struct ws_deque {
    /* Owner's bottom pointer (non-atomic in fast path) */
    atomic_size_t bottom;

    /* Thieves' top pointer (atomic) */
    atomic_size_t top;

    /* RCU-protected array pointer */
    atomic_ptr_t array;

    /* Owner CPU ID (for debugging/stats) */
    uint8_t owner_cpu;

    /* Statistics */
    atomic_uint64_t push_count;
    atomic_uint64_t pop_count;
    atomic_uint64_t steal_count;
    atomic_uint64_t steal_attempts;
    atomic_uint64_t resize_count;
} ws_deque_t;

/*******************************************************************************
 * WORK-STEALING SCHEDULER
 ******************************************************************************/

/**
 * Victim selection strategy
 */
typedef enum {
    WS_VICTIM_RANDOM,      /* Random victim */
    WS_VICTIM_CIRCULAR,    /* Round-robin */
    WS_VICTIM_AFFINITY     /* NUMA-aware (future) */
} ws_victim_strategy_t;

/**
 * Per-CPU work-stealing scheduler
 */
typedef struct ws_percpu_sched {
    uint8_t cpu_id;
    ws_deque_t deque;

    /* Victim selection state */
    ws_victim_strategy_t victim_strategy;
    uint8_t next_victim;           /* For circular strategy */

    /* Local statistics */
    atomic_uint64_t tasks_executed;
    atomic_uint64_t steals_succeeded;
    atomic_uint64_t steals_failed;
    atomic_uint64_t idle_cycles;
} ws_percpu_sched_t;

/**
 * Global work-stealing scheduler state
 */
typedef struct ws_scheduler {
    /* Per-CPU schedulers */
    ws_percpu_sched_t cpus[WS_MAX_CPUS];
    uint8_t num_cpus;

    /* RCU for safe cross-CPU access */
    rcu_state_t *rcu;

    /* Global statistics */
    atomic_uint64_t total_tasks;
    atomic_uint64_t total_steals;
    atomic_uint64_t total_migrations;
} ws_scheduler_t;

/*******************************************************************************
 * DEQUE ARRAY OPERATIONS
 ******************************************************************************/

/**
 * Allocate new circular array
 */
ws_array_t *ws_array_new(size_t capacity);

/**
 * Free array (called via RCU)
 */
void ws_array_free(rcu_head_t *head);

/**
 * Get task at index (with wraparound)
 */
static inline dag_task_t *ws_array_get(ws_array_t *array, size_t index) {
    return array->tasks[index & array->mask];
}

/**
 * Put task at index (with wraparound)
 */
static inline void ws_array_put(ws_array_t *array, size_t index, dag_task_t *task) {
    array->tasks[index & array->mask] = task;
}

/*******************************************************************************
 * CHASE-LEV DEQUE OPERATIONS
 ******************************************************************************/

/**
 * Initialize work-stealing deque
 *
 * @param deque      Deque to initialize
 * @param owner_cpu  CPU that owns this deque
 */
void ws_deque_init(ws_deque_t *deque, uint8_t owner_cpu);

/**
 * Push task to bottom (owner only)
 *
 * ALGORITHM (Chase-Lev):
 * 1. Load bottom (non-atomic)
 * 2. Load top (atomic acquire)
 * 3. Check if resize needed: size = bottom - top >= capacity
 * 4. If resize: grow array to 2x capacity
 * 5. Store task at array[bottom]
 * 6. Increment bottom (atomic release for resize case)
 *
 * LINEARIZATION POINT: Store to bottom (makes push visible)
 *
 * PERFORMANCE: O(1) amortized (resize is rare)
 *
 * @param deque  Deque
 * @param task   Task to push
 * @param rcu    RCU state for safe resizing
 */
void ws_deque_push(ws_deque_t *deque, dag_task_t *task, rcu_state_t *rcu);

/**
 * Pop task from bottom (owner only)
 *
 * ALGORITHM (Chase-Lev):
 * 1. Load bottom (non-atomic)
 * 2. Decrement bottom
 * 3. Store new bottom (atomic release)
 * 4. Load array (RCU-protected)
 * 5. Load task at array[bottom]
 * 6. Load top (atomic acquire)
 * 7. Check size = bottom - top:
 *    - If size < 0: empty, restore bottom, return NULL
 *    - If size == 0: contention with steal, CAS top to resolve
 *    - If size > 0: success, return task
 *
 * LINEARIZATION POINT: Atomic store to bottom or CAS on top
 *
 * FAST PATH: No contention, only 1 atomic store (to bottom)
 *
 * @param deque   Deque
 * @param cpu_id  Owner CPU ID for RCU
 * @param rcu     RCU state
 * @return        Popped task, or NULL if empty
 */
dag_task_t *ws_deque_pop(ws_deque_t *deque, uint8_t cpu_id, rcu_state_t *rcu);

/**
 * Steal task from top (thieves only)
 *
 * ALGORITHM (Chase-Lev):
 * 1. Load top (atomic acquire)
 * 2. Load bottom (atomic acquire)
 * 3. Check size = bottom - top:
 *    - If size <= 0: empty, return NULL
 * 4. Load array (RCU-protected)
 * 5. Load task at array[top]
 * 6. Try CAS(top, old_top, old_top + 1)
 *    - If CAS succeeds: return task
 *    - If CAS fails: retry (another thief stole it)
 *
 * LINEARIZATION POINT: Successful CAS on top
 *
 * @param deque   Deque to steal from
 * @param cpu_id  Thief CPU ID for RCU
 * @param rcu     RCU state
 * @return        Stolen task, or NULL if empty/failed
 */
dag_task_t *ws_deque_steal(ws_deque_t *deque, uint8_t cpu_id, rcu_state_t *rcu);

/**
 * Check if deque is empty (approximate)
 *
 * Note: Result may be stale immediately.
 *
 * @param deque  Deque
 * @return       True if appears empty
 */
bool ws_deque_is_empty(const ws_deque_t *deque);

/**
 * Get deque size (approximate)
 *
 * @param deque  Deque
 * @return       Approximate size
 */
size_t ws_deque_size(const ws_deque_t *deque);

/*******************************************************************************
 * WORK-STEALING SCHEDULER OPERATIONS
 ******************************************************************************/

/**
 * Initialize work-stealing scheduler
 *
 * @param sched     Scheduler
 * @param num_cpus  Number of CPUs
 * @param rcu       RCU state
 */
void ws_scheduler_init(ws_scheduler_t *sched, uint8_t num_cpus, rcu_state_t *rcu);

/**
 * Submit task to local CPU queue
 *
 * @param sched   Scheduler
 * @param task    Task to submit
 * @param cpu_id  CPU to submit to
 */
void ws_scheduler_submit(ws_scheduler_t *sched, dag_task_t *task, uint8_t cpu_id);

/**
 * Get next task for execution (local pop or steal)
 *
 * ALGORITHM:
 * 1. Try pop from local deque
 * 2. If empty, try stealing from random victim
 * 3. Repeat steal attempts up to WS_STEAL_ATTEMPTS
 * 4. If all fail, return NULL (idle)
 *
 * @param sched   Scheduler
 * @param cpu_id  Current CPU ID
 * @return        Task to execute, or NULL if idle
 */
dag_task_t *ws_scheduler_get_task(ws_scheduler_t *sched, uint8_t cpu_id);

/**
 * Select victim CPU for stealing
 *
 * @param sched       Scheduler
 * @param thief_cpu   Thief CPU ID
 * @return            Victim CPU ID
 */
uint8_t ws_scheduler_select_victim(ws_scheduler_t *sched, uint8_t thief_cpu);

/**
 * Try stealing from specific victim
 *
 * @param sched       Scheduler
 * @param victim_cpu  Victim CPU ID
 * @param thief_cpu   Thief CPU ID
 * @return            Stolen task, or NULL if failed
 */
dag_task_t *ws_scheduler_try_steal(ws_scheduler_t *sched, uint8_t victim_cpu, uint8_t thief_cpu);

/*******************************************************************************
 * STATISTICS & MONITORING
 ******************************************************************************/

/**
 * Work-stealing statistics
 */
typedef struct ws_stats {
    uint64_t total_tasks;
    uint64_t total_steals;
    uint64_t total_migrations;
    uint64_t total_pushes;
    uint64_t total_pops;
    uint64_t steal_success_rate;  /* Percentage (0-100) */
    uint64_t avg_deque_size;
} ws_stats_t;

/**
 * Collect work-stealing statistics
 *
 * @param sched  Scheduler
 * @param stats  Output statistics
 */
void ws_get_stats(const ws_scheduler_t *sched, ws_stats_t *stats);

/**
 * Print work-stealing statistics
 *
 * @param sched  Scheduler
 */
void ws_print_stats(const ws_scheduler_t *sched);

/**
 * Print per-CPU statistics
 *
 * @param sched  Scheduler
 */
void ws_print_percpu_stats(const ws_scheduler_t *sched);

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Basic work-stealing with 4 CPUs
 */
void example_work_stealing_basic(void);

/**
 * Example: Load balancing demonstration
 */
void example_work_stealing_load_balance(void);

/**
 * Example: Comparison with static partitioning
 */
void example_work_stealing_vs_static(void);

/**
 * Example: Deque operations and contention
 */
void example_chase_lev_deque(void);
