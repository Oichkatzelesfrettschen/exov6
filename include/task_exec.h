#pragma once

/**
 * @file task_exec.h
 * @brief Task Execution Model for PDAC
 *
 * PEDAGOGICAL PURPOSE:
 * ====================
 * Bridges the gap between scheduling theory and practice by defining
 * what it means to "execute" a task in an operating system.
 *
 * KEY CONCEPTS:
 * =============
 * **Time Quantum**: Maximum time slice a task runs before preemption
 * **Context Switch**: Overhead of switching between tasks (TLB flush, cache, etc.)
 * **Task Lifecycle**: State machine from NEW to COMPLETED
 * **CPU Affinity**: Hint for which CPU should run this task
 *
 * REAL-WORLD ANALOGUES:
 * =====================
 * - Linux: task_struct + context_switch() in kernel/sched/core.c
 * - FreeBSD: struct thread + mi_switch()
 * - Xen: struct vcpu + context_switch_to()
 *
 * DESIGN DECISIONS:
 * =================
 * 1. **Quantum-based preemption** (not voluntary)
 *    - Ensures fairness even for CPU-bound tasks
 *    - Prevents starvation
 *
 * 2. **Context switch cost accounting**
 *    - Realistic overhead modeling
 *    - Helps understand scheduler efficiency
 *
 * 3. **Capability integration**
 *    - Each task has a capability for resource access
 *    - Security enforced at execution time
 */

#include "types.h"
#include "dag_pdac.h"

/*******************************************************************************
 * CONFIGURATION
 ******************************************************************************/

/**
 * Default time quantum (milliseconds)
 *
 * Typical values:
 * - Linux CFS: 4-20ms (adaptive)
 * - Windows: 10-120ms (priority-dependent)
 * - Real-time: 1-5ms (deterministic)
 * - PDAC: 10ms (balanced)
 */
#define TIME_QUANTUM_MS 10

/**
 * Context switch overhead (microseconds)
 *
 * Real hardware measurements:
 * - Modern x86: 1-5 μs
 * - ARM Cortex-A: 0.5-2 μs
 * - Xeon (with L3 cache): 2-8 μs
 * - PDAC simulation: 2 μs
 */
#define CONTEXT_SWITCH_COST_US 2

/**
 * Maximum CPUs supported
 */
#define MAX_CPUS 16

/*******************************************************************************
 * TASK EXECUTION CONTEXT
 ******************************************************************************/

/**
 * Task execution context
 *
 * Maintains runtime state for a single task.
 * Created when task starts executing, destroyed when task completes.
 */
typedef struct task_context {
    /* Associated task */
    dag_task_t *task;                  /* Pointer to DAG task */

    /* Timing */
    uint64_t start_time_us;            /* When task started (microseconds) */
    uint64_t cpu_time_used_us;         /* Total CPU time consumed */
    uint64_t quantum_remaining_us;     /* Time left in current quantum */
    uint64_t last_scheduled_us;        /* Last time task was scheduled */

    /* Capability */
    int capability_slot;               /* Capability for resource access */

    /* CPU affinity */
    uint8_t cpu_id;                    /* Current CPU executing this */
    uint8_t preferred_cpu;             /* Hint for scheduler (cache locality) */

    /* Performance counters */
    uint64_t context_switches;         /* Times preempted */
    uint64_t total_wait_time_us;       /* Time spent waiting (READY state) */

    /* Flags */
    bool quantum_expired;              /* True if quantum ran out */
    bool voluntary_yield;              /* True if task yielded voluntarily */
} task_context_t;

/*******************************************************************************
 * TASK LIFECYCLE
 ******************************************************************************/

/**
 * Initialize task execution context
 *
 * Call this when a task is first admitted to the system.
 *
 * @param ctx        Execution context to initialize
 * @param task       DAG task to execute
 * @param cap_slot   Capability slot for resource access (-1 if none)
 */
void task_exec_init(task_context_t *ctx, dag_task_t *task, int cap_slot);

/**
 * Start task execution
 *
 * Called when task transitions from READY → RUNNING.
 * Resets quantum and records start time.
 *
 * @param ctx   Execution context
 * @param now   Current time (microseconds)
 */
void task_exec_start(task_context_t *ctx, uint64_t now);

/**
 * Execute task for a duration
 *
 * Simulates running the task for the given duration.
 * Updates CPU time, quantum, and checks for completion.
 *
 * @param ctx          Execution context
 * @param duration_us  Duration to run (microseconds)
 * @return             True if task completed, false if more work remains
 */
bool task_exec_run(task_context_t *ctx, uint64_t duration_us);

/**
 * Preempt task execution
 *
 * Called when task's quantum expires or higher-priority task arrives.
 * Transitions task from RUNNING → READY.
 *
 * @param ctx   Execution context
 * @param now   Current time (microseconds)
 */
void task_exec_preempt(task_context_t *ctx, uint64_t now);

/**
 * Complete task execution
 *
 * Called when task finishes all work.
 * Transitions task from RUNNING → COMPLETED.
 *
 * @param ctx   Execution context
 * @param now   Current time (microseconds)
 */
void task_exec_complete(task_context_t *ctx, uint64_t now);

/*******************************************************************************
 * QUANTUM MANAGEMENT
 ******************************************************************************/

/**
 * Check if task should be preempted (quantum expired)
 *
 * @param ctx   Execution context
 * @return      True if quantum expired
 */
bool task_should_preempt(const task_context_t *ctx);

/**
 * Consume quantum time
 *
 * Decrements quantum_remaining by elapsed time.
 *
 * @param ctx         Execution context
 * @param elapsed_us  Time elapsed (microseconds)
 */
void task_consume_quantum(task_context_t *ctx, uint64_t elapsed_us);

/**
 * Reset quantum (after preemption or voluntary yield)
 *
 * @param ctx   Execution context
 */
void task_reset_quantum(task_context_t *ctx);

/**
 * Get remaining quantum time
 *
 * @param ctx   Execution context
 * @return      Remaining time (microseconds)
 */
uint64_t task_get_quantum_remaining(const task_context_t *ctx);

/*******************************************************************************
 * CONTEXT SWITCHING
 ******************************************************************************/

/**
 * Perform context switch between tasks
 *
 * Simulates overhead of switching contexts:
 * - Save/restore registers
 * - TLB flush
 * - Cache pollution
 * - Pipeline flush
 *
 * This adds CONTEXT_SWITCH_COST_US to both tasks' accounting.
 *
 * @param from   Task being switched out (NULL if CPU was idle)
 * @param to     Task being switched in (NULL if going idle)
 * @return       Context switch cost (microseconds)
 */
uint64_t task_context_switch(task_context_t *from, task_context_t *to);

/**
 * Get total context switch overhead for a task
 *
 * @param ctx   Execution context
 * @return      Total overhead (microseconds)
 */
uint64_t task_get_context_switch_overhead(const task_context_t *ctx);

/*******************************************************************************
 * CPU AFFINITY
 ******************************************************************************/

/**
 * Set preferred CPU for task
 *
 * Hint for scheduler to prefer this CPU (cache locality).
 * Not a hard requirement.
 *
 * @param ctx      Execution context
 * @param cpu_id   Preferred CPU (0 to MAX_CPUS-1)
 */
void task_set_preferred_cpu(task_context_t *ctx, uint8_t cpu_id);

/**
 * Get preferred CPU for task
 *
 * @param ctx   Execution context
 * @return      Preferred CPU ID
 */
uint8_t task_get_preferred_cpu(const task_context_t *ctx);

/**
 * Check if task is running on preferred CPU
 *
 * @param ctx   Execution context
 * @return      True if cpu_id == preferred_cpu
 */
bool task_on_preferred_cpu(const task_context_t *ctx);

/*******************************************************************************
 * STATISTICS & INTROSPECTION
 ******************************************************************************/

/**
 * Get task turnaround time (start → completion)
 *
 * @param ctx   Execution context
 * @param now   Current time (microseconds)
 * @return      Turnaround time (microseconds)
 */
uint64_t task_get_turnaround_time(const task_context_t *ctx, uint64_t now);

/**
 * Get task wait time (time spent READY but not RUNNING)
 *
 * @param ctx   Execution context
 * @return      Wait time (microseconds)
 */
uint64_t task_get_wait_time(const task_context_t *ctx);

/**
 * Get task CPU utilization (cpu_time / turnaround_time)
 *
 * @param ctx   Execution context
 * @param now   Current time (microseconds)
 * @return      Utilization (Q16 fixed-point, 0.0-1.0)
 */
q16_t task_get_utilization(const task_context_t *ctx, uint64_t now);

/**
 * Print task execution statistics
 *
 * @param ctx   Execution context
 */
void task_print_stats(const task_context_t *ctx);

/*******************************************************************************
 * WORK SIMULATION
 ******************************************************************************/

/**
 * Estimate task work remaining
 *
 * Uses resource norm as proxy for work.
 * Larger resource requirements → more work.
 *
 * @param ctx   Execution context
 * @return      Estimated work remaining (microseconds)
 */
uint64_t task_estimate_work_remaining(const task_context_t *ctx);

/**
 * Check if task has completed its work
 *
 * @param ctx   Execution context
 * @return      True if work complete
 */
bool task_is_work_complete(const task_context_t *ctx);

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Task lifecycle demonstration
 */
void example_task_lifecycle(void);

/**
 * Example: Quantum-based preemption
 */
void example_quantum_preemption(void);

/**
 * Example: Context switch overhead
 */
void example_context_switch_cost(void);
