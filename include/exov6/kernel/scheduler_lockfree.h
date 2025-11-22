/**
 * @file scheduler_lockfree.h
 * @brief Lock-Free RCU-Based Scheduler (Task 5.5.2)
 *
 * High-performance lock-free scheduler with:
 * - Per-CPU lock-free ready queues (Michael-Scott)
 * - RCU-protected task metadata
 * - Atomic state transitions
 * - Lock-free load balancing
 *
 * Expected Benefits:
 * - 50-100x lower enqueue/dequeue latency
 * - Zero scheduler lock contention
 * - Predictable real-time performance
 * - Near-linear scalability
 */

#pragma once

#include <stdint.h>
#include <stdatomic.h>
#include <stdbool.h>
#include "lockfree.h"
#include "rcu_pdac.h"
#include "q16_octonion.h"

#ifdef __cplusplus
extern "C" {
#endif

/*******************************************************************************
 * CONFIGURATION
 ******************************************************************************/

#define MAX_CPUS                 16      /**< Maximum CPUs supported */
#define MAX_TASKS                4096    /**< Maximum concurrent tasks */
#define SCHEDULER_QUANTUM_US     10000   /**< Default quantum (10ms) */

/*******************************************************************************
 * TASK TYPES
 ******************************************************************************/

/** Task identifier */
typedef uint32_t task_id_t;

/** Task state (atomic) */
typedef enum {
    TASK_STATE_NEW = 0,        /**< Just created */
    TASK_STATE_READY = 1,      /**< Ready to run */
    TASK_STATE_RUNNING = 2,    /**< Currently executing */
    TASK_STATE_BLOCKED = 3,    /**< Waiting for I/O */
    TASK_STATE_COMPLETED = 4,  /**< Finished */
    TASK_STATE_TERMINATED = 5  /**< Terminated/killed */
} task_state_t;

/** Task priority (higher = more important) */
typedef enum {
    TASK_PRIORITY_LOW = 0,
    TASK_PRIORITY_NORMAL = 10,
    TASK_PRIORITY_HIGH = 20,
    TASK_PRIORITY_REALTIME = 30
} task_priority_t;

/*******************************************************************************
 * CORE DATA STRUCTURES
 ******************************************************************************/

/**
 * @brief Lock-free task structure
 *
 * All frequently-accessed fields are atomic for lock-free access.
 * Metadata is RCU-protected for safe concurrent reads.
 */
typedef struct task {
    task_id_t id;                        /**< Unique task ID */

    /* Atomic fields (lock-free access) */
    _Atomic task_state_t state;          /**< Current state */
    _Atomic uint8_t current_cpu;         /**< CPU currently running on */
    _Atomic uint64_t runtime_ns;         /**< Total runtime */
    _Atomic uint64_t context_switches;   /**< Number of context switches */

    /* Scheduling metadata (RCU-protected reads) */
    q16_t priority;                      /**< Base priority */
    uint64_t quantum_ns;                 /**< Time quantum */
    uint64_t deadline_ns;                /**< Real-time deadline (0 = none) */

    /* CPU affinity */
    uint8_t preferred_cpu;               /**< Preferred CPU (for locality) */
    uint64_t cpu_mask;                   /**< Allowed CPUs (bitmask) */

    /* Resource accounting */
    uint64_t memory_allocated;           /**< Memory usage */
    uint64_t io_operations;              /**< I/O count */

    /* Timestamps */
    uint64_t create_time_ns;             /**< Creation timestamp */
    uint64_t start_time_ns;              /**< Last start timestamp */

    /* Function pointer */
    void (*task_func)(void *);           /**< Task function */
    void *task_arg;                      /**< Task argument */

    /* RCU reclamation */
    rcu_head_t rcu_head;                 /**< RCU callback */
} task_t;

/**
 * @brief Per-CPU scheduler state
 *
 * Each CPU has its own lock-free ready queue and statistics.
 */
typedef struct cpu_scheduler {
    /* Lock-free ready queue */
    ms_queue_t ready_queue;              /**< Per-CPU ready queue */

    /* Currently running task (atomic) */
    _Atomic(task_t *) current_task;      /**< Active task */

    /* Load metrics (atomic) */
    _Atomic uint32_t queue_length;       /**< Current queue length */
    _Atomic uint64_t total_enqueues;     /**< Total enqueues */
    _Atomic uint64_t total_dequeues;     /**< Total dequeues */
    _Atomic uint64_t idle_time_ns;       /**< Time spent idle */

    /* Statistics */
    _Atomic uint64_t stolen_from;        /**< Tasks stolen from this CPU */
    _Atomic uint64_t stolen_to;          /**< Tasks stolen to this CPU */
} cpu_scheduler_t;

/**
 * @brief Global lock-free scheduler state
 *
 * Uses:
 * - Per-CPU lock-free queues for task ready state
 * - RCU for safe concurrent metadata access
 * - Atomic counters for global statistics
 */
typedef struct scheduler_lockfree {
    /* Per-CPU schedulers */
    cpu_scheduler_t cpus[MAX_CPUS];
    uint8_t num_cpus;

    /* RCU state */
    rcu_state_t rcu;

    /* Hazard pointer domain */
    hp_domain_t hp;

    /* Global task table (for lookup by ID) */
    _Atomic(task_t *) task_table[MAX_TASKS];

    /* Global statistics (atomic) */
    _Atomic uint64_t total_tasks;        /**< Total tasks created */
    _Atomic uint64_t active_tasks;       /**< Currently active */
    _Atomic uint64_t completed_tasks;    /**< Completed tasks */
    _Atomic uint64_t total_runtime_ns;   /**< Total CPU time */

    /* Configuration */
    uint64_t default_quantum_ns;         /**< Default time quantum */
    bool enable_work_stealing;           /**< Enable cross-CPU stealing */
} scheduler_lockfree_t;

/*******************************************************************************
 * SCHEDULER MANAGEMENT
 ******************************************************************************/

/**
 * @brief Initialize lock-free scheduler
 *
 * @param sched     Scheduler to initialize
 * @param num_cpus  Number of CPUs
 * @return 0 on success, negative on error
 */
int scheduler_lockfree_init(scheduler_lockfree_t *sched, uint8_t num_cpus);

/**
 * @brief Destroy lock-free scheduler
 *
 * WARNING: All tasks must be completed before destroying.
 *
 * @param sched  Scheduler to destroy
 */
void scheduler_lockfree_destroy(scheduler_lockfree_t *sched);

/*******************************************************************************
 * TASK MANAGEMENT (LOCK-FREE)
 ******************************************************************************/

/**
 * @brief Create new task
 *
 * @param sched      Scheduler
 * @param id         Task ID (must be unique)
 * @param priority   Task priority
 * @param task_func  Task function
 * @param task_arg   Task argument
 * @return 0 on success, negative on error
 *
 * Performance: O(1) lock-free
 */
int scheduler_task_create(scheduler_lockfree_t *sched, task_id_t id,
                         q16_t priority, void (*task_func)(void *),
                         void *task_arg);

/**
 * @brief Enqueue task to ready queue (lock-free)
 *
 * Transitions task from NEW → READY and adds to CPU's ready queue.
 *
 * @param sched  Scheduler
 * @param id     Task ID
 * @param cpu    Target CPU
 * @return 0 on success, negative on error
 *
 * Performance: O(1) lock-free enqueue
 * Expected: 10-50ns (vs 500-2000ns for locked)
 */
int scheduler_task_enqueue(scheduler_lockfree_t *sched, task_id_t id,
                          uint8_t cpu);

/**
 * @brief Dequeue task from ready queue (lock-free)
 *
 * Gets next ready task from CPU's queue. May steal from other CPUs.
 * Transitions task READY → RUNNING.
 *
 * @param sched  Scheduler
 * @param cpu    Current CPU
 * @return Task pointer, or NULL if no tasks ready
 *
 * Performance: O(1) average, lock-free
 */
task_t *scheduler_task_dequeue(scheduler_lockfree_t *sched, uint8_t cpu);

/**
 * @brief Mark task as completed (atomic state transition)
 *
 * Transitions task RUNNING → COMPLETED.
 *
 * @param sched  Scheduler
 * @param task   Task to complete
 * @return 0 on success, negative on error
 *
 * Performance: O(1) atomic operation
 */
int scheduler_task_complete(scheduler_lockfree_t *sched, task_t *task);

/**
 * @brief Block task (waiting for I/O)
 *
 * Transitions task RUNNING → BLOCKED.
 *
 * @param sched  Scheduler
 * @param task   Task to block
 * @return 0 on success, negative on error
 */
int scheduler_task_block(scheduler_lockfree_t *sched, task_t *task);

/**
 * @brief Unblock task (I/O completed)
 *
 * Transitions task BLOCKED → READY and re-enqueues.
 *
 * @param sched  Scheduler
 * @param id     Task ID
 * @param cpu    Target CPU
 * @return 0 on success, negative on error
 */
int scheduler_task_unblock(scheduler_lockfree_t *sched, task_id_t id,
                          uint8_t cpu);

/**
 * @brief Lookup task by ID (RCU-protected)
 *
 * Returns pointer to task (valid until RCU grace period).
 * Caller must use rcu_read_lock/unlock.
 *
 * @param sched  Scheduler
 * @param id     Task ID
 * @return Task pointer, or NULL if not found
 *
 * Performance: O(1) RCU-protected read
 */
static inline task_t *scheduler_task_lookup(scheduler_lockfree_t *sched,
                                           task_id_t id)
{
    if (id >= MAX_TASKS) return NULL;
    return atomic_load(&sched->task_table[id]);
}

/*******************************************************************************
 * LOAD BALANCING (LOCK-FREE)
 ******************************************************************************/

/**
 * @brief Steal task from another CPU (lock-free)
 *
 * Attempts to steal a task from the most loaded CPU.
 * Uses atomic operations for safe concurrent stealing.
 *
 * @param sched  Scheduler
 * @param cpu    Current (stealing) CPU
 * @return Stolen task, or NULL if nothing to steal
 *
 * Performance: O(n) where n = num_cpus, lock-free
 */
task_t *scheduler_steal_task(scheduler_lockfree_t *sched, uint8_t cpu);

/**
 * @brief Get least loaded CPU (atomic reads)
 *
 * Finds CPU with shortest ready queue.
 *
 * @param sched  Scheduler
 * @return CPU ID with minimum load
 *
 * Performance: O(n) where n = num_cpus, lock-free
 */
uint8_t scheduler_get_least_loaded_cpu(scheduler_lockfree_t *sched);

/**
 * @brief Balance load across CPUs (RCU-protected)
 *
 * Migrates tasks from heavily loaded CPUs to idle ones.
 * Uses RCU for safe concurrent access to task metadata.
 *
 * @param sched  Scheduler
 * @param cpu    Current CPU (initiating balance)
 *
 * Performance: O(n * m) where n = num_cpus, m = migrations
 */
void scheduler_balance_load(scheduler_lockfree_t *sched, uint8_t cpu);

/*******************************************************************************
 * STATISTICS
 ******************************************************************************/

/**
 * @brief Per-CPU scheduler statistics
 */
typedef struct {
    uint32_t queue_length;       /**< Current queue length */
    uint64_t total_enqueues;     /**< Total enqueues */
    uint64_t total_dequeues;     /**< Total dequeues */
    uint64_t idle_time_ns;       /**< Idle time */
    uint64_t stolen_from;        /**< Tasks stolen from this CPU */
    uint64_t stolen_to;          /**< Tasks stolen to this CPU */
    task_t *current_task;        /**< Currently running task */
} cpu_stats_t;

/**
 * @brief Global scheduler statistics
 */
typedef struct {
    uint64_t total_tasks;        /**< Total tasks created */
    uint64_t active_tasks;       /**< Currently active */
    uint64_t completed_tasks;    /**< Completed tasks */
    uint64_t total_runtime_ns;   /**< Total CPU time */
    uint8_t num_cpus;            /**< Number of CPUs */
} scheduler_stats_t;

/**
 * @brief Get per-CPU statistics (atomic reads)
 *
 * @param sched  Scheduler
 * @param cpu    CPU ID
 * @param stats  Output statistics
 */
void scheduler_get_cpu_stats(const scheduler_lockfree_t *sched, uint8_t cpu,
                            cpu_stats_t *stats);

/**
 * @brief Get global statistics (atomic reads)
 *
 * @param sched  Scheduler
 * @param stats  Output statistics
 */
void scheduler_get_stats(const scheduler_lockfree_t *sched,
                        scheduler_stats_t *stats);

/*******************************************************************************
 * UTILITIES
 ******************************************************************************/

/**
 * @brief Get current timestamp (nanoseconds)
 *
 * @return Current time in nanoseconds
 */
uint64_t scheduler_get_time_ns(void);

/**
 * @brief Print task info (debugging)
 *
 * @param task  Task to print
 */
void scheduler_task_print(const task_t *task);

/**
 * @brief Print scheduler statistics (debugging)
 *
 * @param sched  Scheduler
 */
void scheduler_print_stats(const scheduler_lockfree_t *sched);

#ifdef __cplusplus
}
#endif
