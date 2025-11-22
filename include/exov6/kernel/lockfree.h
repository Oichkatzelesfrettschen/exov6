#pragma once

/**
 * @file lockfree.h
 * @brief Lock-Free Data Structures for PDAC Phase 5
 *
 * PEDAGOGICAL PURPOSE:
 * ====================
 * Demonstrates state-of-the-art concurrent algorithms that achieve
 * synchronization WITHOUT locks, enabling:
 * - True parallelism (no blocking)
 * - Deadlock-free (no locks to deadlock)
 * - Lock-free progress (at least one thread makes progress)
 * - Wait-free operations (bounded steps, owner-side only)
 *
 * KEY CONCEPTS:
 * =============
 * **Compare-And-Swap (CAS)**: Atomic operation that is the foundation
 * ```c
 * bool CAS(atomic_ptr_t *ptr, void *expected, void *new_val) {
 *     if (*ptr == expected) {
 *         *ptr = new_val;
 *         return true;
 *     }
 *     return false;
 * }
 * ```
 *
 * **ABA Problem**: Value changes A→B→A, CAS succeeds incorrectly
 * Solution: Hazard pointers or generation counters
 *
 * **Memory Reclamation**: Cannot free immediately (other threads may access)
 * Solutions:
 * - Hazard Pointers (HP): Mark pointers in-use
 * - Epoch-Based Reclamation (EBR): Track epochs
 * - RCU: Read-Copy-Update (separate module)
 *
 * REAL-WORLD ANALOGUES:
 * =====================
 * - **Michael-Scott Queue**: Used in Java ConcurrentLinkedQueue
 * - **Treiber Stack**: Used in many lock-free allocators
 * - **Chase-Lev Deque**: Intel TBB, Go runtime work-stealing
 * - **Hazard Pointers**: Facebook Folly, Rust crossbeam
 *
 * LINEARIZABILITY:
 * ================
 * All operations appear to take effect atomically at some point
 * between invocation and response (linearization point).
 *
 * **Example**:
 * Thread 1: enqueue(A) [start] ───→ [CAS succeeds] ←─ linearization point ───→ [return]
 * Thread 2:                              dequeue() [start] ───→ [sees A] ───→ [return A]
 *
 * The CAS is the linearization point - after it, A is "visible" to all threads.
 */

#include "types.h"
#include <stdatomic.h>
#include <stdbool.h>

/*******************************************************************************
 * ATOMIC PRIMITIVES
 ******************************************************************************/

/**
 * Atomic pointer type (for lock-free data structures)
 */
typedef _Atomic(void*) atomic_ptr_t;

/**
 * Atomic size type
 */
typedef _Atomic(size_t) atomic_size_t;

/**
 * Atomic integer types
 */
typedef _Atomic(int) atomic_int_t;
typedef _Atomic(uint64_t) atomic_uint64_t;

/**
 * Memory ordering for atomic operations
 *
 * - relaxed: No synchronization (reordering allowed)
 * - acquire: Synchronize with release (read barrier)
 * - release: Synchronize with acquire (write barrier)
 * - acq_rel: Both acquire and release
 * - seq_cst: Sequentially consistent (strongest, default)
 */

/*******************************************************************************
 * HAZARD POINTERS (Memory Reclamation)
 ******************************************************************************/

/**
 * Maximum threads supported
 */
#define HP_MAX_THREADS 64

/**
 * Hazard pointers per thread
 */
#define HP_PER_THREAD 4

/**
 * Retirement threshold (trigger scan when this many retired)
 */
#define HP_RETIRE_THRESHOLD 100

/**
 * Hazard pointer record
 */
typedef struct hazard_pointer {
    atomic_ptr_t ptr;              /* Protected pointer */
    atomic_int_t active;           /* 1 if in use, 0 if free */
} hazard_pointer_t;

/**
 * Retired node (waiting to be freed)
 */
typedef struct retired_node {
    void *ptr;
    void (*deleter)(void*);        /* Custom deletion function */
    struct retired_node *next;
} retired_node_t;

/**
 * Hazard pointer domain (one per data structure type)
 */
typedef struct hp_domain {
    hazard_pointer_t hps[HP_MAX_THREADS * HP_PER_THREAD];

    /* Per-thread retired lists */
    retired_node_t *retire_lists[HP_MAX_THREADS];
    atomic_int_t retire_counts[HP_MAX_THREADS];
} hp_domain_t;

/**
 * Initialize hazard pointer domain
 */
void hp_domain_init(hp_domain_t *domain);

/**
 * Acquire a hazard pointer
 *
 * @param domain  HP domain
 * @param tid     Thread ID
 * @param hp_idx  Hazard pointer index (0 to HP_PER_THREAD-1)
 * @return        Pointer to HP (for protect operation)
 */
hazard_pointer_t *hp_acquire(hp_domain_t *domain, int tid, int hp_idx);

/**
 * Protect a pointer with hazard pointer
 *
 * @param hp   Hazard pointer
 * @param src  Source pointer (atomic)
 * @return     Protected value
 */
void *hp_protect(hazard_pointer_t *hp, atomic_ptr_t *src);

/**
 * Clear hazard pointer (no longer protecting)
 *
 * @param hp  Hazard pointer to clear
 */
void hp_clear(hazard_pointer_t *hp);

/**
 * Retire a node for later deletion
 *
 * @param domain   HP domain
 * @param tid      Thread ID
 * @param ptr      Pointer to retire
 * @param deleter  Deletion function
 */
void hp_retire(hp_domain_t *domain, int tid, void *ptr, void (*deleter)(void*));

/**
 * Scan and free retired nodes
 *
 * @param domain  HP domain
 * @param tid     Thread ID
 */
void hp_scan(hp_domain_t *domain, int tid);

/*******************************************************************************
 * MICHAEL-SCOTT LOCK-FREE QUEUE (MPMC)
 ******************************************************************************/

/**
 * Michael-Scott queue node
 */
typedef struct ms_node {
    void *data;
    atomic_ptr_t next;
} ms_node_t;

/**
 * Michael-Scott queue (lock-free MPMC)
 *
 * Properties:
 * - Multiple producers, multiple consumers
 * - Lock-free (at least one thread makes progress)
 * - FIFO ordering
 * - Linearizable
 */
typedef struct ms_queue {
    atomic_ptr_t head;             /* Dequeue from head */
    atomic_ptr_t tail;             /* Enqueue to tail */
    hp_domain_t *hp;               /* Hazard pointers */

    /* Statistics */
    atomic_uint64_t enqueue_count;
    atomic_uint64_t dequeue_count;
} ms_queue_t;

/**
 * Initialize Michael-Scott queue
 */
void ms_queue_init(ms_queue_t *queue, hp_domain_t *hp);

/**
 * Enqueue (lock-free)
 *
 * Linearization point: CAS that swings tail->next
 *
 * @param queue  Queue
 * @param data   Data to enqueue
 * @param tid    Thread ID
 */
void ms_enqueue(ms_queue_t *queue, void *data, int tid);

/**
 * Dequeue (lock-free)
 *
 * Linearization point: CAS that advances head
 *
 * @param queue  Queue
 * @param tid    Thread ID
 * @return       Dequeued data, or NULL if empty
 */
void *ms_dequeue(ms_queue_t *queue, int tid);

/**
 * Check if queue is empty (approximate)
 *
 * @param queue  Queue
 * @return       True if empty (may be stale)
 */
bool ms_is_empty(ms_queue_t *queue);

/**
 * Get queue size (approximate)
 */
uint64_t ms_get_size(ms_queue_t *queue);

/*******************************************************************************
 * TREIBER LOCK-FREE STACK (LIFO)
 ******************************************************************************/

/**
 * Treiber stack node
 */
typedef struct treiber_node {
    void *data;
    atomic_ptr_t next;
} treiber_node_t;

/**
 * Treiber stack (lock-free LIFO)
 *
 * Properties:
 * - Lock-free push/pop
 * - LIFO ordering
 * - ABA-safe (with hazard pointers)
 */
typedef struct treiber_stack {
    atomic_ptr_t top;              /* Top of stack */
    hp_domain_t *hp;               /* Hazard pointers */

    /* Statistics */
    atomic_uint64_t push_count;
    atomic_uint64_t pop_count;
} treiber_stack_t;

/**
 * Initialize Treiber stack
 */
void treiber_init(treiber_stack_t *stack, hp_domain_t *hp);

/**
 * Push (lock-free)
 *
 * @param stack  Stack
 * @param data   Data to push
 * @param tid    Thread ID
 */
void treiber_push(treiber_stack_t *stack, void *data, int tid);

/**
 * Pop (lock-free)
 *
 * @param stack  Stack
 * @param tid    Thread ID
 * @return       Popped data, or NULL if empty
 */
void *treiber_pop(treiber_stack_t *stack, int tid);

/**
 * Check if stack is empty
 */
bool treiber_is_empty(treiber_stack_t *stack);

/*******************************************************************************
 * ATOMIC COUNTERS (for Telemetry)
 ******************************************************************************/

/**
 * Lock-free counter
 */
typedef struct atomic_counter {
    atomic_uint64_t value;
} atomic_counter_t;

/**
 * Initialize counter
 */
static inline void atomic_counter_init(atomic_counter_t *counter) {
    atomic_store(&counter->value, 0);
}

/**
 * Increment counter
 */
static inline void atomic_counter_inc(atomic_counter_t *counter) {
    atomic_fetch_add(&counter->value, 1);
}

/**
 * Add to counter
 */
static inline void atomic_counter_add(atomic_counter_t *counter, uint64_t delta) {
    atomic_fetch_add(&counter->value, delta);
}

/**
 * Read counter value
 */
static inline uint64_t atomic_counter_read(atomic_counter_t *counter) {
    return atomic_load(&counter->value);
}

/*******************************************************************************
 * UTILITY FUNCTIONS
 ******************************************************************************/

/**
 * Get current thread ID (0 to HP_MAX_THREADS-1)
 */
int get_thread_id(void);

/**
 * Simulated thread ID for single-threaded testing
 */
extern __thread int simulated_tid;

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Concurrent queue operations
 */
void example_lockfree_queue(void);

/**
 * Example: Concurrent stack operations
 */
void example_lockfree_stack(void);

/**
 * Example: Hazard pointer memory safety
 */
void example_hazard_pointers(void);

/**
 * Example: ABA problem demonstration
 */
void example_aba_problem(void);
